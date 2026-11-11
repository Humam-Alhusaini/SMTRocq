(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

open Common
open SmtAtom
open SmtForm
open Eunoia_witness

let sorted = List.sort_uniq (fun a b -> Int.compare (Form.to_lit a) (Form.to_lit b))

let run ~check =
  let count = ref 0 in
  let fresh () = Atom.create (),Form.create () in
  let symbol atoms i dom ty xs = Atom.get atoms
      (Aapp (dummy_indexed_op (Index i) dom ty,Array.of_list xs)) in
  let form forms a = Form.get forms (Fatom a) in
  let bool atoms forms i = form forms (symbol atoms i [||] SmtBtype.Tbool []) in
  let binary forms op a b = Form.get forms (Fapp (op,[|a;b|])) in
  let positive ?limits ?(pure_uf=false) ?(whole_uf=false) name atoms forms premises conclusion =
    let premises = List.map sorted premises and conclusion = sorted conclusion in
    let result = if whole_uf then Search.compress_uf ~atoms ~forms ~premises ~conclusion ()
      else Search.produce ?limits ~atoms ~forms ~premises ~conclusion () in
    match result with
    | Error e -> failwith (name ^ ": " ^ Search.string_of_failure e)
    | Ok w ->
      if pure_uf then assert (List.for_all (fun cmd -> match cmd.Certificate.action with
        | Certificate.LiaMicromega _ -> false | _ -> true) w.Certificate.program);
      let expected_roots = List.map (List.map Form.to_lit) premises @
        List.map (fun f -> [Form.to_lit (Form.neg f)]) conclusion in
      assert (List.map snd w.Certificate.root_claims = expected_roots);
      check name atoms forms premises conclusion w;
      incr count;
      Printf.printf "PASS %s (%d roots, %d commands)\n%!" name
        (List.length w.root_claims) (List.length w.program) in
  let negative ?limits name atoms forms premises conclusion =
    match Search.produce ?limits ~atoms ~forms ~premises:(List.map sorted premises)
      ~conclusion:(sorted conclusion) () with
    | Error _ -> incr count; Printf.printf "PASS %s (rejected)\n%!" name
    | Ok _ -> failwith (name ^ ": unexpected candidate") in
  let atoms,forms = fresh () in
  let a = bool atoms forms 0 and b = bool atoms forms 1 and c = bool atoms forms 2 in
  positive "identity" atoms forms [[a]] [a];
  positive "empty-premise-clause" atoms forms [[]] [];
  positive "resolution" atoms forms [[a;b];[Form.neg a]] [b];
  positive "resolution-common-prefix" atoms forms [[a;b];[a;Form.neg b]] [a];
  positive "multi-premise-resolution" atoms forms [[a;b];[Form.neg a;c];[Form.neg b]] [c];
  positive "ordered-duplicate-roots" atoms forms [[b];[a;b];[a;b];[Form.neg a]] [b];
  negative "premise-clause-is-not-split" atoms forms [[a;b]] [a];
  negative "missing-premise" atoms forms [] [a];
  negative "changed-conclusion" atoms forms [[a]] [b];
  let and_ab = binary forms Fand a b and or_ab = binary forms For a b in
  positive "and-projection" atoms forms [[and_ab]] [a];
  positive "bool-theory-tautology" atoms forms [] [Form.neg and_ab;a];
  positive "and-introduction" atoms forms [[a];[b]] [and_ab];
  positive "or-elimination" atoms forms [[or_ab];[Form.neg a]] [b];
  positive "or-introduction-from-whole-clause" atoms forms [[a;b]] [or_ab];
  let imp = binary forms Fimp a b in
  let not2_a = Form.get forms (Fapp (Fnot2 1,[|a|])) in
  positive "explicit-double-negation" atoms forms [] [binary forms Fiff not2_a a];
  positive "explicit-double-negation-negative" atoms forms
    [[Form.neg not2_a]] [Form.neg a];
  negative "double-negation-is-not-arbitrary" atoms forms [[not2_a]] [b];
  positive "modus-ponens" atoms forms [[imp];[a]] [b];
  let xor = binary forms Fxor a b and iff = binary forms Fiff a b in
  positive "xor" atoms forms [[xor];[a]] [Form.neg b];
  positive "iff" atoms forms [[iff];[a]] [b];
  let d = bool atoms forms 3 in
  positive "iff-nested-congruence" atoms forms
    [[binary forms Fiff a b];[binary forms Fiff c d]]
    [binary forms Fiff (binary forms Fiff a c) (binary forms Fiff b d)];
  positive "iff-transitive-congruence" atoms forms
    [[binary forms Fiff b c];[binary forms Fiff a c]]
    [binary forms Fiff (binary forms Fiff b a) (binary forms Fiff c c)];
  let e = bool atoms forms 4 and f = bool atoms forms 5 in
  let p = binary forms Fand a (binary forms For b c)
  and p' = binary forms Fand d (binary forms For e f)
  and q = binary forms For (Form.neg a) (Form.neg b)
  and q' = binary forms For (Form.neg d) (Form.neg e) in
  positive "nested-implication-congruence" atoms forms
    [[binary forms Fiff p p'];[binary forms Fiff q q']]
    [binary forms Fiff (binary forms Fimp p q) (binary forms Fimp p' q')];
  negative "nested-implication-missing-premise" atoms forms
    [[binary forms Fiff p p']]
    [binary forms Fiff (binary forms Fimp p q) (binary forms Fimp p' q')];
  let ite = Form.get forms (Fapp (Fite,[|a;b;c|])) in
  positive "ite-then" atoms forms [[ite];[a]] [b];
  positive "ite-else" atoms forms [[ite];[Form.neg a]] [c];
  positive "non-unit-propositional-refutation" atoms forms
    [[a;b];[a;Form.neg b];[Form.neg a;b];[Form.neg a;Form.neg b]] [];
  negative "invalid-and-projection" atoms forms [[or_ab]] [and_ab];
  positive "false-refutation" atoms forms [[Form.get forms Form.pform_false]] [];
  let true_form = Form.get forms Form.pform_true in
  positive "singleton-true" atoms forms [] [true_form];
  positive "boolean-equality-to-true" atoms forms []
    [binary forms Fiff (binary forms Fiff a true_form) a];
  negative ~limits:{Search.default_limits with max_clauses=1}
    "clause-budget" atoms forms [[a]] [a];
  negative ~limits:{Search.default_limits with max_resolution_pairs=0}
    "resolution-budget" atoms forms [[a]] [a];
  negative ~limits:{Search.default_limits with max_formulas=0}
    "formula-budget" atoms forms [[a]] [a];
  (match Search.produce ~atoms ~forms ~premises:[[b;a;a]] ~conclusion:[] () with
   | Error (Search.Invalid_input _) -> incr count
   | _ -> failwith "noncanonical input was not rejected");
  (* This exact kind of CPC Boolean congruence previously spent tens of
     seconds in Micromega despite having a short EUF/resolution certificate. *)
  let atoms,forms = fresh () in
  let zs = Array.init 6 (fun i -> symbol atoms i [||] SmtBtype.TZ []) in
  let eq i j = form forms (Atom.get atoms (Abop (BO_eq SmtBtype.TZ,zs.(i),zs.(j)))) in
  let left = [|eq 0 1;eq 1 2;eq 2 3;eq 2 4;eq 4 5;Form.neg (eq 0 5)|]
  and right = [|eq 0 1;eq 2 1;eq 3 2;eq 2 4;eq 4 5;Form.neg (eq 0 5)|] in
  positive ~pure_uf:true "integer-sorted-uf-nary-congruence" atoms forms
    (Array.to_list (Array.map2 (fun a b -> [binary forms Fiff a b]) left right))
    [binary forms Fiff (Form.get forms (Fapp (Fand,left))) (Form.get forms (Fapp (Fand,right)))];
  let atoms,forms = fresh () in
  let chain size =
    let atoms,forms = fresh () in
    let zs = Array.init (size+1) (fun i -> symbol atoms i [||] SmtBtype.TZ []) in
    let eq i j = form forms (Atom.get atoms (Abop (BO_eq SmtBtype.TZ,zs.(i),zs.(j)))) in
    let literals = Array.init (size+1) (fun i -> if i=size then Form.neg(eq 0 size) else eq i(i+1)) in
    atoms,forms,Form.get forms (Fapp(Fand,literals)) in
  let chain_atoms,chain_forms,root = chain 10 in
  positive ~whole_uf:true ~pure_uf:true "whole-uf-boolean-chain" chain_atoms chain_forms [[root]] [];
  let chain_atoms,chain_forms,root = chain 64 in
  let before = Form.nvars chain_forms,Array.length(Atom.to_array chain_atoms None (fun a->Some a)) in
  (match Search.compress_uf ~atoms:chain_atoms ~forms:chain_forms ~premises:[[root]] ~conclusion:[] () with
  | Error _ -> incr count
  | Ok _ -> failwith "whole-UF budget was not enforced");
  assert(before=(Form.nvars chain_forms,Array.length(Atom.to_array chain_atoms None (fun a->Some a))));
  let ty = SmtBtype.Tindex (SmtBtype.dummy_indexed_type 0) in
  let x = symbol atoms 0 [||] ty [] and y = symbol atoms 1 [||] ty []
  and z = symbol atoms 2 [||] ty [] in
  let equal x y = form forms (Atom.get atoms (Abop (BO_eq ty,x,y))) in
  let xy = equal x y and yx = equal y x and yz = equal y z and xz = equal x z in
  positive "euf-reflexivity" atoms forms [] [equal x x];
  positive "euf-symmetry" atoms forms [[xy]] [yx];
  positive "euf-transitivity" atoms forms [[xy];[yz]] [xz];
  positive "euf-theory-tautology" atoms forms [] [Form.neg xy;Form.neg yz;xz];
  positive "euf-disequality-conflict" atoms forms [[xy];[yz];[Form.neg xz]] [];
  negative "euf-missing-link" atoms forms [[xy]] [xz];
  negative "euf-satisfiable-disequality" atoms forms [[Form.neg xy]] [];
  let f x = symbol atoms 3 [|ty|] ty [x] in
  let g x y = symbol atoms 4 [|ty;ty|] ty [x;y] in
  positive "euf-congruence" atoms forms [[xy]] [equal (f x) (f y)];
  positive "euf-congruence-unchanged-argument" atoms forms [[yx]] [equal (g x z) (g y z)];
  positive "euf-nested-congruence" atoms forms [[xy];[yz]]
    [equal (f (g x x)) (f (g y z))];
  let p x = form forms (symbol atoms 5 [|ty|] SmtBtype.Tbool [x]) in
  positive "euf-predicate-congruence" atoms forms [[xy];[p x]] [p y];
  positive "euf-negative-predicate-congruence" atoms forms [[xy];[Form.neg (p x)]] [Form.neg (p y)];
  positive "euf-predicate-iff-conclusion" atoms forms [[xy]] [binary forms Fiff (p x) (p y)];
  (* Actual cvc5 1.4.2 CPC cong on (= x z) needs the equality predicate's
     congruence clause even when neither (= x z) nor (= y z) is a unit. *)
  positive "euf-equality-predicate-congruence" atoms forms [[xy]]
    [binary forms Fiff xz yz];
  positive "euf-negative-equality-predicate" atoms forms [[xy];[Form.neg xz]]
    [Form.neg yz];
  positive "euf-equality-predicate-local-clause" atoms forms []
    [Form.neg xy;Form.neg xz;yz];
  positive "euf-symmetry-iff" atoms forms [] [binary forms Fiff xy yx];
  positive "euf-conditional-transitivity-nonunit" atoms forms []
    [binary forms Fiff (binary forms Fand xy yz) (binary forms Fand xy xz)];
  positive "euf-disjunctive-congruence-root" atoms forms [[xy;xz]]
    [equal (f x) (f y);equal (f x) (f z)];
  negative "euf-nonunit-equality-is-not-assumed" atoms forms [[xy;xz]] [xy];
  negative ~limits:{Search.default_limits with max_terms=0}
    "euf-term-budget" atoms forms [[xy]] [xy];
  negative ~limits:{Search.default_limits with max_theory_rounds=0}
    "euf-theory-round-budget" atoms forms [[xy]] [yx];
  negative "euf-predicate-without-equality" atoms forms [[p x]] [p y];
  let other x = symbol atoms 6 [|ty|] ty [x] in
  negative "euf-different-function" atoms forms [[xy]] [equal (f x) (other y)];
  let other_p x = form forms (symbol atoms 7 [|ty|] SmtBtype.Tbool [x]) in
  negative "euf-different-predicate" atoms forms [[xy];[p x]] [other_p y];
  let ty2 = SmtBtype.Tindex (SmtBtype.dummy_indexed_type 1) in
  let a = symbol atoms 8 [||] ty2 [] and b = symbol atoms 9 [||] ty2 [] in
  let equal2 a b = form forms (Atom.get atoms (Abop (BO_eq ty2,a,b))) in
  let cross x a = symbol atoms 10 [|ty;ty2|] ty [x;a] in
  positive "euf-two-sort-binary-congruence" atoms forms [[xy];[equal2 a b]]
    [equal (cross x a) (cross y b)];
  let to_other x = symbol atoms 11 [|ty|] ty2 [x] in
  let from_other a = symbol atoms 12 [|ty2|] ty [a] in
  positive "euf-two-sort-nested-congruence" atoms forms [[xy]]
    [equal (from_other (to_other x)) (from_other (to_other y))];
  let atoms,forms = fresh () in
  let abool = symbol atoms 0 [||] SmtBtype.Tbool []
  and bbool = symbol atoms 1 [||] SmtBtype.Tbool []
  and cbool = symbol atoms 2 [||] SmtBtype.Tbool [] in
  let equal a b =
    if SmtBtype.HashedBtype.equal (Atom.type_of a) SmtBtype.Tbool then
      binary forms Fiff (form forms a) (form forms b)
    else form forms (Atom.get atoms (Abop (BO_eq (Atom.type_of a),a,b))) in
  let ab = equal abool bbool and bc = equal bbool cbool in
  let f a = symbol atoms 3 [|SmtBtype.Tbool|] SmtBtype.Tbool [a]
  and h a = symbol atoms 4 [|SmtBtype.Tbool|] SmtBtype.TZ [a] in
  positive "bool-uf-original" atoms forms [[ab]] [equal (f abool) (f bbool)];
  positive "bool-uf-reverse-edge" atoms forms [[equal bbool abool]]
    [equal (f abool) (f bbool)];
  positive "bool-uf-integer-result" atoms forms [[ab]] [equal (h abool) (h bbool)];
  positive "bool-uf-nested" atoms forms [[ab]] [equal (f (f abool)) (f (f bbool))];
  positive "bool-uf-transitive" atoms forms [[ab];[bc]] [equal (f abool) (f cbool)];
  positive "bool-uf-positive-predicate" atoms forms [[ab];[form forms (f abool)]]
    [form forms (f bbool)];
  positive "bool-uf-false-valued-inputs" atoms forms
    [[ab];[Form.neg (form forms abool)];[Form.neg (form forms bbool)]]
    [equal (h abool) (h bbool)];
  positive "bool-uf-negative-predicate" atoms forms [[ab];[Form.neg (form forms (f abool))]]
    [Form.neg (form forms (f bbool))];
  positive "bool-uf-conditional" atoms forms [] [Form.neg ab;equal (f abool) (f bbool)];
  let x = symbol atoms 5 [||] SmtBtype.TZ [] and y = symbol atoms 6 [||] SmtBtype.TZ [] in
  let k a x = symbol atoms 7 [|SmtBtype.Tbool;SmtBtype.TZ|] SmtBtype.TZ [a;x] in
  positive "bool-uf-mixed" atoms forms [[ab];[equal x y]]
    [equal (k abool x) (k bbool y)];
  positive "bool-uf-mixed-unchanged" atoms forms [[ab]]
    [equal (k abool x) (k bbool x)];
  negative "bool-uf-missing-edge" atoms forms [] [equal (f abool) (f bbool)];
  negative "bool-uf-false-premise-is-not-fact" atoms forms [[Form.neg ab]]
    [equal (f abool) (f bbool)];
  negative "bool-uf-injectivity" atoms forms [[equal (f abool) (f bbool)]] [ab];
  let other a = symbol atoms 8 [|SmtBtype.Tbool|] SmtBtype.Tbool [a] in
  negative "bool-uf-different-head" atoms forms [[ab]] [equal (f abool) (other bbool)];
  negative "bool-uf-nonunit-is-not-assumed" atoms forms [[ab;bc]]
    [equal (f abool) (f bbool)];
  let atoms,forms = fresh () in
  let x = symbol atoms 0 [||] SmtBtype.TZ [] in
  let zero = Atom.hatom_Z_of_int atoms 0 and one = Atom.hatom_Z_of_int atoms 1
  and two = Atom.hatom_Z_of_int atoms 2 in
  let le a b = form forms (Atom.mk_le atoms a b)
  and lt a b = form forms (Atom.mk_lt atoms a b) in
  let x0 = le x zero and x1 = le x one and strict = lt x zero in
  positive "lia-bound-weakening" atoms forms [[x0]] [x1];
  positive "lia-theory-tautology" atoms forms [] [Form.neg x0;x1];
  positive "lia-scaling" atoms forms [[x0]] [le (Atom.mk_mult atoms two x) zero];
  positive "lia-disjunctive-premise" atoms forms [[x0;strict]] [x1];
  positive "lia-inconsistent-roots" atoms forms [[x0];[lt zero x]] [];
  let iff = binary forms Fiff (lt x one) x0 in
  positive "lia-integer-gap-iff" atoms forms [] [iff];
  let xor_gap = binary forms Fxor (lt x one) x0 in
  positive "lia-integer-gap-xor" atoms forms [] [Form.neg xor_gap];
  let ite_gap = Form.get forms (Fapp (Fite,[|x0;lt x one;Form.neg (lt x one)|])) in
  positive "lia-integer-gap-ite" atoms forms [] [ite_gap];
  let arithmetic_only = {Search.default_limits with max_boolean_pairs=0} in
  let not4 = Form.get forms (Fapp (Fnot2 2,[|lt x one|])) in
  positive ~limits:arithmetic_only "lia-repeated-double-negation" atoms forms [[not4]] [x0];
  positive ~limits:arithmetic_only "lia-implication-branch-numbering" atoms forms []
    [binary forms Fimp (lt x one) x0];
  let normalized = le (Atom.mk_plus atoms x one) two in
  positive "lia-normalization-iff" atoms forms [] [binary forms Fiff normalized x1];
  let y = symbol atoms 1 [||] SmtBtype.TZ [] in
  let y0 = le y zero in
  positive "lia-sum-bounds" atoms forms [[x0];[y0]]
    [le (Atom.mk_plus atoms x y) zero];
  positive "lia-reordered-certificate-clause" atoms forms [[y0];[x0]]
    [le (Atom.mk_plus atoms x y) zero];
  positive "lia-disjunctive-conditional-iff" atoms forms [[x0;y0]]
    [binary forms Fiff (le (Atom.mk_plus atoms x one) one) x0];
  negative "lia-incorrect-integer-gap-iff" atoms forms []
    [binary forms Fiff strict x0];
  negative "lia-strict-conclusion" atoms forms [[x0]] [strict];
  negative "lia-reversed-bound" atoms forms [[x1]] [x0];
  negative "lia-missing-premise" atoms forms [] [x0];
  negative "lia-satisfiable-roots" atoms forms [[x0]] [];
  Printf.printf "%d witness search cases passed\n%!" !count

let check_shape _name _atoms _forms _premises _conclusion (w:Certificate.witness) =
  (* Sliced candidates retain every root, but allocate only retained commands. *)
  assert (w.capacity = List.length w.root_claims + List.length w.program);
  let live = Hashtbl.create 31 in
  let load id c = assert (id >= 0 && id < w.capacity && not (Hashtbl.mem live id));
    assert (c = Certificate.canonical c); Hashtbl.add live id c in
  List.iter (fun (id,c) -> load id c) w.root_claims;
  List.iteri (fun offset cmd ->
    assert (Certificate.output cmd.Certificate.action = List.length w.root_claims + offset);
    List.iter (fun id -> assert (Hashtbl.mem live id)) (Certificate.reads cmd.Certificate.action);
    assert (cmd.expected <> [0] || (match cmd.action with Certificate.CTrue _ -> true | _ -> false));
    (match cmd.action with
     | Certificate.Res (_,a,b) ->
       assert (cmd.expected = Certificate.resolve (Hashtbl.find live b) (Hashtbl.find live a))
     | _ -> ());
    load (Certificate.output cmd.action) cmd.expected) w.program;
  assert (Hashtbl.find live w.conflict = [])
