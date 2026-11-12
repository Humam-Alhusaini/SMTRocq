(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

open Common
open SmtAtom
open SmtForm
open Certificate

type limits = {
  max_clauses : int;
  max_resolution_pairs : int;
  max_boolean_pairs : int;
  max_theory_rounds : int;
  max_terms : int;
  max_formulas : int;
  max_lia_literals : int;
}
let default_limits = { max_clauses = 4096; max_resolution_pairs = 100000; max_boolean_pairs = 256;
  max_theory_rounds = 32; max_terms = 128; max_formulas = 256; max_lia_literals = 64 }
type failure = Invalid_input of string | Resource_limit of string | Unsupported
let string_of_failure = function
  | Invalid_input s -> "invalid input: " ^ s
  | Resource_limit s -> "resource limit: " ^ s
  | Unsupported -> "no local witness found"
exception Fail of failure
exception Conflict of int
let profile_sequence = ref 0
let pos f = if Form.is_pos f then f else Form.neg f
let lit = Form.to_lit
let neg l = l lxor 1
let atom_view f = if Form.is_pos f then match Form.pform f with
  | Fatom a when SmtBtype.HashedBtype.equal (Atom.type_of a) SmtBtype.Tbool -> Some a
  | _ -> None else None
let eq f = if Form.is_pos f then match Form.pform f with
  | Fatom a -> (match Atom.atom a with
    | Abop (BO_eq ty,a,b) when
        SmtBtype.HashedBtype.equal (Atom.type_of a) ty &&
        SmtBtype.HashedBtype.equal (Atom.type_of b) ty -> Some (a,b)
    | _ -> None)
  | Fapp (Fiff,xs) when Array.length xs = 2 ->
    (match atom_view xs.(0),atom_view xs.(1) with
     | Some a,Some b -> Some (a,b) | _ -> None)
  | _ -> None else None
let tautology c = List.exists (fun l -> List.mem (neg l) c) c
let rec subset a b = match a,b with
  | [],_ -> true | _,[] -> false
  | x::xs,y::ys -> if x = y then subset xs ys
    else if x > y then subset a ys else false

(* This is a producer-side prediction of the existing CNF checker, not a new
   acceptance test. All emitted predictions must be recomputed by the gate. *)
let definitions f =
  let p = lit (pos f) in
  let n = neg p in
  let def l c = (fun id -> BuildDef (id,l)), c in
  let def2 l c = (fun id -> BuildDef2 (id,l)), c in
  let projections xs mk = Array.to_list (Array.mapi (fun i x ->
      (fun id -> BuildProj (id,p,i)), mk (lit x)) xs) in
  match Form.pform f with
  | Fapp (Ftrue,_) -> [(fun id -> CTrue id), [0]]
  | Fapp (Ffalse,_) -> [(fun id -> CFalse id), [3]]
  | Fapp (Fand,xs) -> def p (p :: List.map (fun x -> neg (lit x)) (Array.to_list xs))
      :: projections xs (fun x -> [n;x])
  | Fapp (For,xs) -> def n (n :: List.map lit (Array.to_list xs))
      :: projections xs (fun x -> [p;neg x])
  | Fapp (Fimp,xs) when Array.length xs > 0 ->
    let last = Array.length xs - 1 in
    def n (n :: Array.to_list (Array.mapi (fun i x ->
      if i = last then lit x else neg (lit x)) xs)) ::
    Array.to_list (Array.mapi (fun i x ->
      (fun id -> BuildProj (id,p,i)), [p;if i = last then neg (lit x) else lit x]) xs)
  | Fapp ((Fxor | Fiff | Fite as op),xs) ->
    let a = lit xs.(0) and b = lit xs.(1) in
    let d, d2, e, e2 = match op with
      | Fxor -> [p;a;neg b], [p;neg a;b], [n;a;b], [n;neg a;neg b]
      | Fiff -> [p;neg a;neg b], [p;a;b], [n;a;neg b], [n;neg a;b]
      | Fite -> let c = lit xs.(2) in
        [p;a;neg c], [p;neg a;neg b], [n;a;c], [n;neg a;b]
      | _ -> assert false in
    [def p d;def2 p d2;def n e;def2 n e2]
  | _ -> []

let children a = match Atom.atom a with
  | Acop _ -> [] | Auop (_,a) -> [a] | Abop (_,a,b) -> [a;b]
  | Atop (_,a,b,c) -> [a;b;c] | Anop (_,xs) | Aapp (_,xs) -> Array.to_list xs
let congr_args a b = match Atom.atom a, Atom.atom b with
  | Auop (o,a), Auop (p,b) when o = p -> Some ([a],[b])
  | Abop (o,a,b), Abop (p,c,d) when o = p -> Some ([a;b],[c;d])
  | Atop (o,a,b,c), Atop(p,d,e,f) when o=p -> Some([a;b;c],[d;e;f])
  | Aapp (f,xs), Aapp (g,ys) when
      indexed_op_index f = indexed_op_index g && Array.length xs = Array.length ys ->
    Some (Array.to_list xs,Array.to_list ys)
  | _ -> None

let produce_search ?(derivation=false) ?(eager_theory_units=false) ?(limits=default_limits) ~atoms ~forms ~premises ~conclusion () =
  let profiling = Sys.getenv_opt "EUNOIA_WITNESS_PROFILE" = Some "1" in
  let sequence = if profiling then (incr profile_sequence; !profile_sequence) else 0 in
  let started = if profiling then Sys.time () else 0. in
  if profiling then begin
    let clause c = String.concat " " (List.map
      (fun f -> Format.asprintf "%a" (Form.to_smt ~debug:true) f) c) in
    Printf.eprintf "EUNOIA_WITNESS id=%d premises=[%s] conclusion=[%s]\n%!"
      sequence (String.concat "; " (List.map clause premises)) (clause conclusion)
  end;
  try
    if limits.max_clauses <= 0 || limits.max_resolution_pairs < 0 ||
       limits.max_theory_rounds < 0 || limits.max_terms < 0 || limits.max_formulas < 0 ||
       limits.max_lia_literals < 0 || limits.max_boolean_pairs < 0
    then raise (Fail (Invalid_input "negative/zero search limits"));
    let initial_forms = Form.pform_tbl forms in
    let initial_atoms = Atom.to_array atoms None (fun a -> Some a) in
    let relevant = Hashtbl.create 31 and terms = Hashtbl.create 31 in
    let remember f =
      let i = Form.index f in
      if not (Hashtbl.mem relevant i) then begin
        if Hashtbl.length relevant >= limits.max_formulas then
          raise (Fail (Resource_limit "formulas"));
        Hashtbl.add relevant i (pos f)
      end in
    let rec atom a =
      let i = Atom.index a in
      if i < 0 || i >= Array.length initial_atoms || initial_atoms.(i) <> Some (Atom.atom a)
      then raise (Fail (Invalid_input "atom is outside the supplied table"));
      if not (Hashtbl.mem terms i) then begin
        if Hashtbl.length terms >= limits.max_terms then
          raise (Fail (Resource_limit "terms"));
        Hashtbl.add terms i a; List.iter atom (children a)
      end in
    let rec visit f =
      let i = Form.index f in
      if i < 0 || i >= Array.length initial_forms || initial_forms.(i) <> Form.pform f
      then raise (Fail (Invalid_input "formula is outside the supplied table"));
      if not (Hashtbl.mem relevant i) then begin
        remember f;
        match Form.pform f with
        | Fatom a -> atom a
        | Fapp (op,xs) ->
          (match op with
           | Fxor | Fiff when Array.length xs <> 2 ->
             raise (Fail (Invalid_input "binary connective arity"))
           | Fite when Array.length xs <> 3 ->
             raise (Fail (Invalid_input "ite arity"))
           | _ -> ()); Array.iter visit xs
        | FbbT _ -> ()
      end in
    let input c =
      List.iter visit c;
      let c = List.map lit c in
      if canonical c <> c then raise (Fail (Invalid_input "noncanonical clause")); c in
    let pcs = List.map input premises and cc = input conclusion in
    let roots = if derivation then pcs else pcs @ List.map (fun l -> [neg l]) cc in
    if List.length roots > limits.max_clauses then raise (Fail (Resource_limit "roots"));
    let has_arrays = lazy (Hashtbl.fold (fun _ a found -> found || match Atom.atom a with
      | Abop ((BO_select _ | BO_diffarray _),_,_) | Atop (TO_store _,_,_,_) -> true
      | Abop (BO_eq (SmtBtype.TFArray _),_,_) -> true
      | _ -> false) terms false) in
    (* Extensionality is needed for the array equalities in the actual roots.
       Applying it again to auxiliary congruence equalities creates unrelated
       difference witnesses and an unbounded tower of read terms. *)
    let array_targets = Hashtbl.fold (fun _ f acc -> match Form.pform f with
      | Fatom a -> (match Atom.atom a with
        | Abop(BO_eq(SmtBtype.TFArray _),_,_) -> f::acc | _ -> acc)
      | _ -> acc) relevant [] in
    let root_claims = List.mapi (fun id c -> id,c) roots in
    let next = ref (List.length roots) and program = ref [] in
    let clauses = Hashtbl.create 127 and known = Hashtbl.create 127 in
    let pending = Queue.create () and units = Queue.create () in
    let index = Hashtbl.create 127 and pairs = Hashtbl.create 127 in
    let pair_count = ref 0 in
    let profile stage f =
      if not profiling then f () else begin
        let report event = Printf.eprintf
          "EUNOIA_WITNESS id=%d stage=%s event=%s cpu_s=%.6f slots=%d pairs=%d formulas=%d\n%!"
          sequence stage event (Sys.time () -. started) !next !pair_count
          (Hashtbl.length relevant) in
        report "begin";
        match f () with
        | result -> report "end"; result
        | exception e -> report "raise"; raise e
      end in
    let register id c =
      Hashtbl.add clauses id c;
      if not (Hashtbl.mem known c) then Hashtbl.add known c id;
      (* Unit propagation must see clauses which have not yet been selected
         for saturation. Otherwise units_only only compares units with units,
         leaving all Boolean propagation behind unrestricted resolution. *)
      List.iter (fun l -> Hashtbl.replace index l
        (id :: Stdlib.Option.value ~default:[] (Hashtbl.find_opt index l))) c;
      Queue.add id (if List.length c = 1 then units else pending) in
    List.iter (fun (id,c) -> register id c) root_claims;
    let subsumed ?(strict=false) c = Hashtbl.fold (fun d _ found ->
      found || ((not strict || d <> c) && subset d c)) known false in
    let finish conflict =
      (* Drop unused search work, but retain EVERY exact root claim. This only
         slices the local resolution DAG; it never omits a generated inference. *)
      let needed = Hashtbl.create 31 in
      Hashtbl.add needed conflict ();
      let program = List.fold_left (fun acc cmd ->
        if Hashtbl.mem needed (output cmd.action) then begin
          List.iter (fun id -> Hashtbl.replace needed id ()) (reads cmd.action);
          cmd::acc
        end else acc) [] !program in
      (* Pruning commands should also prune their state allocation. Keep root
         slots (including unused/duplicate roots) exactly as claimed, then
         densely relocate retained command slots and all their reads. This
         changes only the untrusted candidate; the gate checks it as usual. *)
      let relocated = Hashtbl.create (List.length program) in
      List.iter (fun (id,_) -> Hashtbl.add relocated id id) root_claims;
      let capacity = ref (List.length root_claims) in
      let slot id = Hashtbl.find relocated id in
      let program = List.map (fun cmd ->
        let p = !capacity in incr capacity;
        Hashtbl.add relocated (output cmd.action) p;
        let action = match cmd.action with
          | Res (_,a,b) -> Res (p,slot a,slot b)
          | CFalse _ -> CFalse p | CTrue _ -> CTrue p
          | BuildDef (_,l) -> BuildDef (p,l)
          | BuildDef2 (_,l) -> BuildDef2 (p,l)
          | BuildProj (_,l,i) -> BuildProj (p,l,i)
          | ImmFlatten (_,a,l) -> ImmFlatten (p,slot a,l)
          | EqTr (_,l,ls) -> EqTr (p,l,ls)
          | EqCgr (_,l,ls) -> EqCgr (p,l,ls)
          | BoolCongr (_,l,ls) -> BoolCongr (p,l,ls)
          | EqCgrP (_,a,b,ls) -> EqCgrP (p,a,b,ls)
          | LiaMicromega (_,c,proof) -> LiaMicromega (p,c,proof)
          | ArrayReadSame (_,l) -> ArrayReadSame(p,l)
          | ArrayReadOther (_,c) -> ArrayReadOther(p,c)
          | ArrayExtensionality (_,l) -> ArrayExtensionality(p,l) in
        {cmd with action}) program in
      if profiling then Printf.eprintf
        "EUNOIA_WITNESS id=%d event=finish cpu_s=%.6f searched_slots=%d capacity=%d commands=%d pairs=%d\n%!"
        sequence (Sys.time () -. started) !next !capacity (List.length program) !pair_count;
      { capacity = !capacity;root_claims;program;conflict=slot conflict } in
    let rec add mk c =
      let c = canonical c in
      let explicit_true = match mk !next with CTrue _ -> true | _ -> false in
      if (c <> [0] || explicit_true) && not (tautology c) && not (subsumed c) then begin
        if !next >= limits.max_clauses then raise (Fail (Resource_limit "clauses"));
        let id = !next in incr next;
        program := {action=mk id;expected=c} :: !program;
        register id c;
        if c = (if derivation then cc else []) then raise (Conflict id);
        (* A fresh nonunit clause must also see units already consumed from
           the propagation queue. Emit ordinary checked resolutions eagerly;
           otherwise a closing transitivity clause waits behind saturation. *)
        if eager_theory_units then
          match List.find_map (fun l ->
            Stdlib.Option.map (fun unit -> unit,[neg l]) (Hashtbl.find_opt known [neg l])) c with
          | None -> ()
          | Some (unit,unit_clause) ->
            if !pair_count >= limits.max_resolution_pairs then
              raise (Fail (Resource_limit "resolution pairs"));
            incr pair_count;
            Hashtbl.replace pairs (min id unit,max id unit) ();
            add (fun p -> Res(p,id,unit)) (resolve unit_clause c)
      end in
    let resolve_pending ?(units_only=false) ?(pair_budget=max_int) () =
      let starting_pairs = !pair_count in
      while not (Queue.is_empty units && (units_only || Queue.is_empty pending)) &&
        !pair_count - starting_pairs < pair_budget do
        let id = Queue.take (if Queue.is_empty units then pending else units) in
        let c = Hashtbl.find clauses id in
        if c = (if derivation then cc else []) then raise (Conflict id);
        (* A stronger available clause can do all resolution work of this
           superset. Keep its exact slot/root claim; only skip producer work. *)
        if not (subsumed ~strict:true c) then begin
          List.iter (fun l ->
            let partners = Stdlib.Option.value ~default:[] (Hashtbl.find_opt index (neg l)) in
            List.iter (fun other ->
              let a,b = if id < other then id,other else other,id in
              if a <> b && not (Hashtbl.mem pairs (a,b)) then begin
                if !pair_count >= limits.max_resolution_pairs then
                  raise (Fail (Resource_limit "resolution pairs"));
                incr pair_count; Hashtbl.add pairs (a,b) ();
                let ca = Hashtbl.find clauses a and cb = Hashtbl.find clauses b in
                let result = resolve cb ca in
                (* A genuine pivot exists; a tautological resolvent is useless.
                   Match the checker's order, including its fallback behavior. *)
                if canonical result = result then add (fun p -> Res (p,a,b)) result
              end) partners) c
        end
      done in
    let form_list () = Hashtbl.fold (fun _ f acc -> f::acc) relevant []
      |> List.sort (fun a b -> Int.compare (lit a) (lit b)) in
    let cnf f = List.iter (fun (mk,c) -> add mk c) (definitions f) in
    let intern_eq a b =
      let f = if SmtBtype.HashedBtype.equal (Atom.type_of a) SmtBtype.Tbool then begin
        let fa = Form.get forms (Fatom a) and fb = Form.get forms (Fatom b) in
        remember fa; remember fb;
        Form.get forms (Fapp (Fiff,[|fa;fb|]))
      end else Form.get forms (Fatom (Atom.get atoms
        (Abop (BO_eq (Atom.type_of a),a,b)))) in
      remember f; f in
    let unit_forms () = List.filter_map (fun f ->
      if Hashtbl.mem known [lit f] then Some f
      else if Hashtbl.mem known [neg (lit f)] then Some (Form.neg f) else None) (form_list ()) in
    let theory () =
      let fs = form_list () in
      let graph = Hashtbl.create 31 in
      let edge a b f = Hashtbl.replace graph (Atom.index a)
        ((b,f)::Stdlib.Option.value ~default:[] (Hashtbl.find_opt graph (Atom.index a))) in
      (* Edges are hypotheses of candidate theory clauses, not facts asserted
         by search. Keeping nonunit equality atoms allows conditional symmetry,
         transitivity and congruence lemmas; resolution must still discharge
         every edge literal against the exact local roots. *)
      List.iter (fun f -> match eq f with
        | Some (a,b) when not (Lazy.force has_arrays && Hashtbl.mem known [neg(lit f)]) ->
          edge a b f; edge b a f
        | _ -> ()) fs;
      let path ?exclude a b =
        if Atom.equal a b then Some [] else
        let seen = Hashtbl.create 31 and q = Queue.create () in
        Hashtbl.add seen (Atom.index a) (); Queue.add (a,[]) q;
        let rec loop () = if Queue.is_empty q then None else
          let x,rev = Queue.take q in
          if Atom.equal x b then Some (List.rev rev) else begin
            List.iter (fun (y,f) -> if Some (lit f) <> exclude &&
                not (Hashtbl.mem seen (Atom.index y)) then begin
              Hashtbl.add seen (Atom.index y) (); Queue.add (y,f::rev) q end)
              (Stdlib.Option.value ~default:[] (Hashtbl.find_opt graph (Atom.index x)));
            loop () end in loop () in
      let trans f path =
        (match Form.pform f with
        | Fapp (Fiff,_) ->
          (* Boolean equality paths are propositional implications. Their
             definitions and the existing checked resolutions discharge them. *)
          cnf f; List.iter cnf path
        | _ -> add (fun p -> EqTr (p,lit f,List.map lit path))
            (lit f :: List.map (fun f -> neg (lit f)) path));
        if eager_theory_units then resolve_pending ~units_only:true () in
      List.iter (fun f -> match eq f with
        | Some (a,b) when not (Hashtbl.mem known [lit f]) ->
          (* Using the target edge itself only yields a tautology and hides
             useful alternative paths, e.g. (= x y) versus (= y x). *)
          (match path ~exclude:(lit f) a b with Some es -> trans f es | None -> ())
        | _ -> ()) fs;
      let arguments a b = match congr_args a b with
        | None -> None
        | Some (xs,ys) ->
          let rec loop xs ys acc = match xs,ys with
            | [],[] -> Some (List.rev acc)
            | a::xs,b::ys when Atom.equal a b -> loop xs ys (None::acc)
            | a::xs,b::ys -> (match path a b with
              | None -> None
              | Some [f] -> loop xs ys (Some (lit f)::acc)
              | Some es -> let f = intern_eq a b in trans f es;
                loop xs ys (Some (lit f)::acc))
            | _ -> None in loop xs ys [] in
      let neg_args ls = List.filter_map (Stdlib.Option.map neg) ls in
      let targets = Hashtbl.create 31 in
      List.iter (fun f -> match eq f with
        | Some (a,b) -> Hashtbl.replace targets (Atom.index a,Atom.index b) ()
        | None -> ()) fs;
      let ts = Hashtbl.fold (fun _ a acc -> a::acc) terms []
        |> List.sort (fun a b -> Int.compare (Atom.index a) (Atom.index b)) in
      List.iteri (fun i a -> List.iteri (fun j b ->
        if i < j && SmtBtype.HashedBtype.equal (Atom.type_of a) (Atom.type_of b) &&
          (not (Lazy.force has_arrays) || match Atom.atom a with Atop(TO_store _,_,_,_) -> false | _ -> true) then
          (* Respect a requested equality's orientation rather than waiting
             another round for symmetry while resolution saturates. *)
          let a,b = if Hashtbl.mem targets (Atom.index b,Atom.index a) &&
              not (Hashtbl.mem targets (Atom.index a,Atom.index b)) then b,a else a,b in
          match arguments a b with
          | None -> ()
          | Some es -> let f = intern_eq a b in
            let needs_bridge = match Form.pform f with Fapp (Fiff,_) -> true | _ ->
              List.exists (function None -> false | Some l ->
                match Form.pform (Hashtbl.find relevant (l lsr 1)) with
                | Fapp (Fiff,_) -> true | _ -> false) es in
            if needs_bridge then begin
              match Atom.atom a,Atom.atom b with
              | Aapp _,Aapp _ ->
                add (fun p -> BoolCongr (p,lit f,es)) (lit f :: neg_args es);
                cnf f
              | _ -> ()
            end else add (fun p -> EqCgr (p,lit f,es)) (lit f :: neg_args es)) ts) ts;
      let predicates = List.filter_map (fun f -> match Form.pform f with
        (* Equality is a Boolean predicate too. In particular, a generated
           congruence on (= x z) may conclude an iff before either equality
           becomes a unit. The existing check_congr_pred handles Abop BO_eq;
           excluding it here loses precisely that local implication. *)
        | Fatom a -> Some (f,a) | _ -> None) fs in
      List.iter (fun (fa,a) -> List.iter (fun (fb,b) ->
        if not (Form.equal fa fb) then match arguments a b with
          | None -> ()
          | Some es ->
            let needs_bridge = List.exists (function None -> false | Some l ->
              match Form.pform (Hashtbl.find relevant (l lsr 1)) with
              | Fapp (Fiff,_) -> true | _ -> false) es in
            if needs_bridge then begin
              match Atom.atom a,Atom.atom b with
              | Aapp _,Aapp _ -> let f = intern_eq a b in
                add (fun p -> BoolCongr (p,lit f,es)) (lit f :: neg_args es); cnf f
              | _ -> ()
            end else add (fun p -> EqCgrP (p,lit fa,lit fb,es))
              (neg (lit fa) :: lit fb :: neg_args es)) predicates) predicates in
    let lia_count = ref 0 in
    let rec lia_form f =
      incr lia_count;
      !lia_count <= limits.max_lia_literals && match Form.pform f with
      | Fatom a -> (match Atom.atom a with
        | Abop ((BO_Zlt | BO_Zle | BO_Zge | BO_Zgt | BO_eq SmtBtype.TZ),_,_) -> true
        | _ -> false)
      | Fapp ((Ftrue | Ffalse | Fand | For | Fimp | Fiff | Fxor | Fite | Fnot2 _),xs) ->
        Array.for_all lia_form xs
      | _ -> false in
    (* Native arithmetic candidates mirror LIA.build_hform directly. Do not
       intern Boolean expansions which are only needed by certificate search. *)
    (* Integer-sorted UF variables are not arithmetic expressions. Equalities
       between uninterpreted applications need only EUF and Boolean reasoning;
       sending their Boolean expansion to Micromega can be exponentially slow.
       Any interpreted atom (including an integer literal) keeps LIA enabled.
       This only selects untrusted search; the gate still checks every command. *)
    let needs_lia = Hashtbl.fold (fun _ a needed -> needed ||
      match Atom.atom a with
      | Aapp _ | Abop (BO_eq _,_,_) | Abop ((BO_select _ | BO_diffarray _),_,_)
      | Atop (TO_store _,_,_,_) -> false
      | _ -> true) terms false in
    let try_lia c =
      (* Certificates depend on the exact traversal/variable numbering of
         their clause. Canonicalize BEFORE producing evidence, not in add. *)
      let c = List.sort_uniq (fun a b -> Int.compare (lit a) (lit b)) c in
      lia_count := 0;
      if needs_lia && List.for_all lia_form c then
        match Lia.build_lia_certif (c) with
        | None -> ()
        | Some proof -> let c = List.map lit c in
          add (fun p -> LiaMicromega (p,c,proof)) c in
    (* Candidate array laws use existing SMTCoq operations. Every generated
       term and clause is rechecked by the typed model and local gate. *)
    let rec generated_atom a =
      if not (Hashtbl.mem terms (Atom.index a)) then begin
        if Hashtbl.length terms >= limits.max_terms then raise(Fail(Resource_limit "array terms"));
        Hashtbl.add terms (Atom.index a) a;List.iter generated_atom (children a)
      end in
    let array_equality a b =
      let ty=Atom.type_of a in
      let f=Form.get forms(Fatom(Atom.get atoms(Abop(BO_eq ty,a,b)))) in
      remember f;f in
    let array_select ti te a i =
      let v=Atom.mk_select atoms ti te a i in generated_atom v;v in
    let array_axioms () =
      List.iter(fun f->match Form.pform f with
      | Fatom a -> (match Atom.atom a with
        | Abop(BO_eq(SmtBtype.TFArray(ti,te)),a,b) ->
          let diff=Atom.mk_diffarray atoms ti te a b in generated_atom diff;
          let left=array_select ti te a diff and right=array_select ti te b diff in
          let same=array_equality left right in
          let ext=Form.get forms(Fapp(For,[|f;Form.neg same|])) in remember ext;
          add(fun p->ArrayExtensionality(p,lit ext))[lit ext];cnf ext
        | _ -> ())
      | _ -> ())array_targets;
      (* Close the finite read-over-write graph before propositional saturation.
         Otherwise nested stores need a second round only after thousands of
         irrelevant resolvents have exhausted the clause budget. *)
      let rec rows () =
        let before=Hashtbl.length terms in
        let ts=Hashtbl.fold(fun _ a acc->a::acc)terms[] in
      List.iter(fun a->match Atom.atom a with
      | Abop(BO_select(ti,te),store,j) -> (match Atom.atom store with
        | Atop(TO_store(ti',te'),base,i,value) when
            SmtBtype.HashedBtype.equal ti ti' && SmtBtype.HashedBtype.equal te te' ->
          let same=array_select ti te store i in
          let same_eq=array_equality same value in
          add(fun p->ArrayReadSame(p,lit same_eq))[lit same_eq];
          if not(Atom.equal i j)then begin
            let index_eq=array_equality i j in
            let old=array_select ti te base j in
            let read_eq=array_equality a old in
            add(fun p->ArrayReadOther(p,[lit index_eq;lit read_eq]))[lit index_eq;lit read_eq];
            if SmtBtype.HashedBtype.equal ti SmtBtype.TZ then begin
              let facts=List.filter(fun f->lia_count:=0;lia_form f)(unit_forms()) in
              let guards=List.map Form.neg facts in
              try_lia(Form.neg index_eq::guards);try_lia(index_eq::guards)
            end
          end
        | _ -> ())
      | _ -> ())ts;
        if Hashtbl.length terms > before then rows () in
      rows () in
    let run () =
      if derivation then begin
        (match Hashtbl.find_opt known cc with Some id -> raise (Conflict id) | None -> ());
        (* A globally valid target needs just its existing theory clause. *)
        try_lia conclusion
      end;
      List.iter (fun (id,c) -> if c = (if derivation then cc else []) then raise (Conflict id)) root_claims;
      (* Preserve exact source trees at the outer boundary. Within the local
         proof, the existing syntactic checker can certify removal of Fnot2
         and associative Boolean nesting from singleton roots. *)
      let rec remember_tree f =
        let fresh = not (Hashtbl.mem relevant (Form.index f)) in
        remember f;
        if fresh then match Form.pform f with
          | Fapp (_,xs) -> Array.iter remember_tree xs
          | _ -> () in
      List.iteri (fun id -> function
        | [f] -> let flat = Form.flatten forms f in
          if not (Form.equal flat f) then begin
            remember_tree flat;
            add (fun p -> ImmFlatten (p,id,lit flat)) [lit flat]
          end
        | _ -> ()) (if derivation then premises else premises @ List.map (fun f -> [Form.neg f]) conclusion);
      (* Keep disjunctive premises whole for Micromega. CNF equivalences below
         connect each auxiliary disjunction back to its exact root clause. *)
      let arithmetic_inputs = List.concat premises @ conclusion in
      lia_count := 0;
      let arithmetic_clause = if needs_lia && List.for_all lia_form arithmetic_inputs then begin
        let pforms = List.map (function [f] -> f | c ->
          let f = Form.get forms (Fapp (For,Array.of_list c)) in
          remember f; f) premises in
        Some (List.map Form.neg pforms @ conclusion)
      end else None in
      profile "cnf" (fun () -> List.iter cnf (form_list ()));
      let rec rounds n =
        profile "resolve_units" (fun () -> resolve_pending ~units_only:true ());
        if n >= limits.max_theory_rounds then begin
          resolve_pending (); raise (Fail (Resource_limit "theory rounds"))
        end;
        let before = !next in
        if Lazy.force has_arrays then profile "arrays" array_axioms;
        profile "theory" theory;
        (* First propagate the new EUF/CNF units. Try the exact arithmetic
           implication before saturating unrelated nonunit Boolean clauses.
           Whole disjunctive premises remain intact in arithmetic_clause. *)
        profile "resolve_before_lia" (fun () -> resolve_pending ~units_only:true ());
        (* Propositional congruence over arithmetic terms can close using the
           already checked EUF clauses. Finish a small amount of this work
           before invoking arithmetic. Stop only between queue items, leaving
           all remaining work available to the ordinary saturation pass. *)
        if !next < limits.max_clauses - 512 then
          profile "resolve_boolean" (fun () -> resolve_pending ~pair_budget:limits.max_boolean_pairs ());
        if n = 0 then profile "lia_exact" (fun () ->
          Stdlib.Option.iter try_lia arithmetic_clause);
        profile "lia_units" (fun () ->
          try_lia (List.map Form.neg (List.filter (fun f ->
            lia_count := 0; lia_form f) (unit_forms ()))));
        (* Conditional EUF clauses must be available before unrestricted
           propositional saturation of the Boolean definitions. *)
        profile "resolve_after_lia" (fun () ->
          if Lazy.force has_arrays && !next > before && n+1 < limits.max_theory_rounds then
            resolve_pending ~units_only:true ()
          else resolve_pending ());
        if !next = before then raise (Fail Unsupported);
        rounds (n+1) in rounds 0 in
    (try run () with Conflict id -> Ok (finish id))
  with Fail e -> Error e

(* Opt-in observational tracing. Snapshots and dependency walks never change
   reification or candidate production. In particular, no indices are recycled.
   Between calls the backend can reify a result and scoped pushes; the trace
   reports that aggregate boundary without attributing it to native search. *)
let table_profile_sequence = ref 0
let produce ?(limits=default_limits) ~atoms ~forms ~premises ~conclusion () =
  if Sys.getenv_opt "EUNOIA_TABLE_PROFILE" <> Some "1" then
    produce_search ~limits ~atoms ~forms ~premises ~conclusion ()
  else begin
    incr table_profile_sequence;
    let sequence = !table_profile_sequence in
    let counts () = Array.length (Atom.to_array atoms None (fun a -> Some a)) - 1,
      Form.nvars forms in
    let before_atoms,before_forms = counts () in
    let dependencies literals =
      let aa = Atom.to_array atoms None (fun a -> Some a)
      and ff = Form.pform_tbl forms in
      let aset = Hashtbl.create 31 and fset = Hashtbl.create 31 in
      let rec atom a =
        let i = Atom.index a in
        if not (Hashtbl.mem aset i) then begin
          Hashtbl.add aset i (); List.iter atom (children a)
        end in
      let rec form i =
        if i >= 0 && i < Form.nvars forms && not (Hashtbl.mem fset i) then begin
          Hashtbl.add fset i ();
          match ff.(i) with
          | Fatom a -> atom a
          | Fapp (_,xs) -> Array.iter (fun f -> form (Form.index f)) xs
          | FbbT (a,xs) -> atom a; List.iter (fun f -> form (Form.index f)) xs
        end in
      List.iter (fun l -> form (l lsr 1)) literals;
      (* Include nested atoms, but never the default array sentinel. *)
      let indices set bound = Hashtbl.fold (fun i () acc ->
        if i >= 0 && i < bound then i::acc else acc) set [] |> List.sort Int.compare in
      indices aset (Array.length aa - 1), indices fset (Form.nvars forms) in
    let ints xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]" in
    let source_atoms,source_forms = dependencies
      (List.concat_map (List.map lit) (conclusion::premises)) in
    Printf.eprintf
      "EUNOIA_TABLE {\"id\":%d,\"event\":\"begin\",\"atoms\":%d,\"forms\":%d,\"source_atoms\":%s,\"source_forms\":%s}\n%!"
      sequence before_atoms before_forms (ints source_atoms) (ints source_forms);
    let report result =
      let after_atoms,after_forms = counts () in
      let status,literals = match result with
        | Error _ -> "error",[]
        | Ok w -> "ok", List.concat_map snd w.root_claims @
          List.concat_map (fun cmd ->
            let action = match cmd.action with
              | Res _ | CFalse _ | CTrue _ -> []
              | BuildDef (_,l) | BuildDef2 (_,l) | BuildProj (_,l,_) -> [l]
              | ImmFlatten (_,_,l) -> [l]
              | EqTr (_,l,ls) -> l::ls
              | EqCgr (_,l,ls) | BoolCongr (_,l,ls) -> l::List.filter_map Fun.id ls
              | EqCgrP (_,a,b,ls) -> a::b::List.filter_map Fun.id ls
              | LiaMicromega (_,c,_) -> c
              | ArrayReadSame (_,l) | ArrayExtensionality (_,l) -> [l]
              | ArrayReadOther (_,c) -> c in
            action @ cmd.expected) w.program in
      let retained_atoms,retained_forms = dependencies literals in
      Printf.eprintf
        "EUNOIA_TABLE {\"id\":%d,\"event\":\"end\",\"status\":\"%s\",\"atoms\":%d,\"forms\":%d,\"retained_atoms\":%s,\"retained_forms\":%s}\n%!"
        sequence status after_atoms after_forms (ints retained_atoms) (ints retained_forms)
    in
    match produce_search ~limits ~atoms ~forms ~premises ~conclusion () with
    | result -> report result; result
    | exception e ->
      let after_atoms,after_forms = counts () in
      Printf.eprintf
        "EUNOIA_TABLE {\"id\":%d,\"event\":\"exception\",\"atoms\":%d,\"forms\":%d}\n%!"
        sequence after_atoms after_forms;
      raise e
  end

(* An untrusted direct-clause candidate. The separate Rocq derivation gate
   checks every root, command and final clause; callers retain refutation fallback. *)
let produce_derivation ?(limits=default_limits) ~atoms ~forms ~premises ~conclusion () =
  let limits = {limits with max_clauses=min limits.max_clauses 512;
    max_resolution_pairs=min limits.max_resolution_pairs 512;
    max_theory_rounds=min limits.max_theory_rounds 2;
    max_boolean_pairs=min limits.max_boolean_pairs 64} in
  produce_search ~limits ~derivation:true ~atoms ~forms ~premises ~conclusion ()

(* Whole-goal UF/CNF compression is untrusted proof production. A syntactic
   screen bounds its input before search can intern any auxiliary formulas.
   It deliberately leaves arithmetic and deep function graphs to the ordinary
   CVC5 translator. The resulting local program still passes the full gate. *)
let compress_uf ~atoms ~forms ~premises ~conclusion () =
  let seen_forms = Hashtbl.create 31 and seen_terms = Hashtbl.create 31 in
  let rec term depth a =
    depth <= 4 && (Hashtbl.mem seen_terms (Atom.index a) ||
      Hashtbl.length seen_terms < 64 && match Atom.atom a with
      | Aapp (_,xs) ->
        Hashtbl.add seen_terms (Atom.index a) ();
        Array.for_all (term (depth+1)) xs
      | _ -> false)
  and formula f =
    Hashtbl.mem seen_forms (Form.index f) ||
    Hashtbl.length seen_forms < 128 && begin
      Hashtbl.add seen_forms (Form.index f) ();
      match Form.pform f with
      | Fatom a -> (match Atom.atom a with
        | Abop (BO_eq _,a,b) -> term 0 a && term 0 b
        | Aapp _ -> term 0 a
        | _ -> false)
      | Fapp (_,xs) -> Array.for_all formula xs
      | FbbT _ -> false
    end in
  if not (List.for_all (List.for_all formula) (conclusion::premises)) then Error Unsupported
  else produce_search ~eager_theory_units:true ~limits:{max_clauses=1024;
    max_resolution_pairs=4096;max_boolean_pairs=64;max_theory_rounds=8;
    max_terms=64;max_formulas=128;max_lia_literals=0}
    ~atoms ~forms ~premises ~conclusion ()


(* Reconstruct a branch proof using only ordinary checked operations. The
   temporary assumption is never installed as a root of the result. Resolution
   against that assumption aliases the other parent; every later resolution
   is recomputed on the actual clauses. Failure to obtain the discharged unit
   rejects this candidate. No branch answer is trusted. *)
let combine_array_branches ~premises ~conclusion split left right =
  try
    let roots = List.map (List.map lit) premises @ List.map (fun f->[neg(lit f)]) conclusion in
    let root_claims = List.mapi (fun i c->i,c) roots in
    let clauses=Hashtbl.create 127 and next=ref(List.length roots) and program=ref[] in
    List.iter(fun(i,c)->Hashtbl.add clauses i c) root_claims;
    let emit action expected =
      if !next>=4096 || (expected=[0] && (match action !next with CTrue _->false | _->true)) then raise Exit;
      let p= !next in incr next;
      program:={action=action p;expected}::!program;Hashtbl.add clauses p expected;p in
    let discharge w branch =
      let slots=Hashtbl.create 127 in
      List.iteri(fun i (id,_) -> Hashtbl.add slots id
        (if i=List.length premises then None
         else Some(if i<List.length premises then i else i-1))) w.root_claims;
      let slot i=Hashtbl.find slots i in
      let actual i=match slot i with Some p->p|None->raise Exit in
      List.iter(fun cmd ->
        let result=match cmd.action with
        | Res(_,a,b) -> (match slot a,slot b with
          | None,None -> raise Exit
          | None,p | p,None -> p
          | Some a,Some b -> Some(emit(fun p->Res(p,a,b))
              (resolve(Hashtbl.find clauses b)(Hashtbl.find clauses a))))
        | a ->
          let action p=match a with
          | CTrue _->CTrue p | CFalse _->CFalse p
          | BuildDef(_,l)->BuildDef(p,l) | BuildDef2(_,l)->BuildDef2(p,l)
          | BuildProj(_,l,i)->BuildProj(p,l,i)
          | ImmFlatten(_,a,l)->ImmFlatten(p,actual a,l)
          | EqTr(_,l,ls)->EqTr(p,l,ls) | EqCgr(_,l,ls)->EqCgr(p,l,ls)
          | BoolCongr(_,l,ls)->BoolCongr(p,l,ls)
          | EqCgrP(_,a,b,ls)->EqCgrP(p,a,b,ls)
          | LiaMicromega(_,c,proof)->LiaMicromega(p,c,proof)
          | ArrayReadSame(_,l)->ArrayReadSame(p,l)
          | ArrayReadOther(_,c)->ArrayReadOther(p,c)
          | ArrayExtensionality(_,l)->ArrayExtensionality(p,l)
          | Res _->assert false in
          Some(emit action cmd.expected) in
        Hashtbl.replace slots (output cmd.action) result) w.program;
      let result=actual w.conflict in
      let clause=Hashtbl.find clauses result in
      if clause<>[neg branch] && clause<>[] then raise Exit;
      result in
    let a=discharge left (lit split) in
    let conflict=if Hashtbl.find clauses a=[] then a else
      let b=discharge right (neg(lit split)) in
      if Hashtbl.find clauses b=[] then b else emit(fun p->Res(p,a,b)) [] in
    Some {capacity= !next;root_claims;program=List.rev !program;conflict}
  with Exit | Not_found -> None

(* Whole-goal array compilation is selected only for actual array goals.
   A bounded case split on read/write index equalities avoids unrestricted
   resolution blow-up. Both branches are reconstructed into one ordinary
   certificate; no temporary branch root survives in the submitted witness. *)
let compress_arrays ~atoms ~forms ~premises ~conclusion () =
  let limits={max_clauses=512;max_resolution_pairs=4096;max_boolean_pairs=32;
    max_theory_rounds=6;max_terms=256;max_formulas=1024;max_lia_literals=64} in
  let calls=ref 0 in
  let profile = Sys.getenv_opt "EUNOIA_ARRAY_PROFILE"=Some "1" in
  let report s=if profile then Printf.eprintf "ARRAY_SEARCH %s\n%!" s in
  let rec search depth premises =
    incr calls;
    if !calls>15 then Error(Resource_limit "array branches") else
    match produce_search ~eager_theory_units:true ~limits ~atoms ~forms ~premises ~conclusion () with
    | Ok _ as result->report(Printf.sprintf "depth=%d success" depth);result
    | Error e as failure ->
      report(Printf.sprintf "depth=%d failure=%s" depth (string_of_failure e));
      if depth=0 then failure else
      let roots=List.map (List.map lit) premises @ List.map(fun f->[neg(lit f)]) conclusion in
      let assigned f=List.exists(fun c->c=[lit f] || c=[neg(lit f)])roots in
      let seen=Hashtbl.create 31 and candidates=ref[] in
      let rec visit a=
        if Hashtbl.length seen<256 && not(Hashtbl.mem seen (Atom.index a))then begin
          Hashtbl.add seen (Atom.index a)();
          (match Atom.atom a with
          | Abop(BO_select(ti,te),store,j)->(match Atom.atom store with
            | Atop(TO_store _,base,i,_) ->
              if not(Atom.equal i j)then begin
                let f=Form.get forms(Fatom(Atom.get atoms(Abop(BO_eq ti,i,j)))) in
                if not(assigned f)then candidates:=f::!candidates
              end;
              visit(Atom.mk_select atoms ti te base j)
            | _->())
          | Abop(BO_eq(SmtBtype.TFArray(ti,te)),a,b)->
            let d=Atom.mk_diffarray atoms ti te a b in
            visit(Atom.mk_select atoms ti te a d);visit(Atom.mk_select atoms ti te b d)
          | _->());List.iter visit(children a)
        end in
      let rec formula f=match Form.pform f with
        | Fatom a->visit a | Fapp(_,xs)->Array.iter formula xs | _->() in
      List.iter(List.iter formula)(conclusion::premises);
      match List.sort_uniq(fun a b->Int.compare(lit a)(lit b))!candidates with
      | []->failure
      | split::_->
        report(Printf.sprintf "depth=%d split=%s" depth (Format.asprintf "%a" (Form.to_smt ~debug:true) split));
        match search (depth-1) (premises@[[split]]) with
        | Error _->failure
        | Ok left->match search (depth-1) (premises@[[Form.neg split]]) with
          | Error _->failure
          | Ok right->match combine_array_branches ~premises ~conclusion split left right with
            | None->report "reconstruction failure";failure | Some w->Ok w in
  search 3 premises
