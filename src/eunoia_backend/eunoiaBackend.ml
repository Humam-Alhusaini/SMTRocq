open Common
open SmtAtom
module R = RocqInterface
module C = EunoiaRocq
module E = EunoiaElaborate
let adapter n = "SMTCoq.checker.eunoia.EunoiaAdapter.EunoiaAdapter." ^ n
let local n = "SMTCoq.checker.eunoia.EunoiaLocal.EunoiaLocal." ^ n
let core n = "SMTCoq.checker.eunoia.EunoiaChecker.EunoiaChecker." ^ n
let scoped n = "SMTCoq.checker.eunoia.EunoiaScopedAdapter.EunoiaScopedAdapter." ^ n
let scope n = "SMTCoq.checker.eunoia.EunoiaScope.EunoiaScope." ^ n
let tactic_api n = "SMTCoq.checker.eunoia.EunoiaTactic.EunoiaTactic." ^ n
let state n = "SMTCoq.checker.fol.State." ^ n
let std n = "Stdlib." ^ n
let mkint = R.mkInt
let clause c = C.list (Lazy.force CoqTerms.cint) (List.map (fun f -> mkint (Form.to_lit f)) c)
let clause_ty () = SmtMisc.mklApp CoqTerms.clist [|(Lazy.force CoqTerms.cint)|]
let clauses cs = C.list (clause_ty ()) (List.map clause cs)
let pair a b x y = SmtMisc.mklApp CoqTerms.cpair [|a;b;x;y|]
let pair_ty a b = SmtMisc.mklApp CoqTerms.cprod [|a;b|]
let claims cs = C.list (pair_ty (Lazy.force CoqTerms.cint) (clause_ty ()))
  (List.map (fun (i,c) -> pair (Lazy.force CoqTerms.cint) (clause_ty ()) (mkint i) (clause c)) cs)

type tables = {
  sorts : SmtBtype.reify_tbl; functions : Op.reify_tbl;
  atoms : Atom.reify_tbl; forms : Form.reify;
}
type witness_producer =
  atoms:Atom.reify_tbl -> forms:Form.reify ->
  premises:Form.t list list -> conclusion:Form.t list -> (R.constr,string) result
let create_tables () = {sorts=SmtBtype.create ();functions=Op.create ();
  atoms=Atom.create ();forms=Form.create ()}
let name_sort i = "Tindex_" ^ string_of_int i
let name_function i = "op_" ^ string_of_int i
let sort ty = match ty with
  | SmtBtype.Tbool -> E.Symbol "Bool"
  | SmtBtype.TZ -> E.Symbol "Int"
  | SmtBtype.Tindex i -> E.Symbol (name_sort (SmtBtype.indexed_type_index i))
  | _ -> R.raise_error "Eunoia: only QF_UF and QF_LIA sorts supported"
let declarations t =
  List.map (fun (i,_) -> E.{name=name_sort i;typ=Symbol "Type"}) (SmtBtype.to_list t.sorts) @
  List.map (fun (i,args,ret,_) -> E.{name=name_function i;
    typ=if Array.length args=0 then sort ret else app "->" (List.map sort (Array.to_list args) @ [sort ret])})
    (Op.to_list t.functions)
let names t =
  let str_ty = C.global (std "Strings.String.string") in
  let ns xs = C.list (pair_ty (Lazy.force CoqTerms.cint) str_ty) (List.map (fun (i,s) ->
    pair (Lazy.force CoqTerms.cint) str_ty (mkint i) (C.string s)) xs) in
  C.call (adapter "Naming") [
    ns (List.map (fun (i,_) -> i,name_sort i) (SmtBtype.to_list t.sorts));
    ns (List.map (fun (i,_,_,_) -> i,name_function i) (Op.to_list t.functions))]
let snapshot t =
  let ti = make_t_i t.sorts in
  [ti;make_t_func t.functions ti;Atom.interp_tbl t.atoms;snd (Form.interp_tbl t.forms)]
let register_instances env t =
  (* Intermediate carriers need CompDec even when no source equality mentions
     that carrier. Reuse actual context proof terms before snapshot can create
     delayed cuts; never submit an undeclared CompDec variable to VM reduction. *)
  let source_sorts = List.map (fun (i,_) -> SmtBtype.get_coq_type_op i)
    (SmtBtype.to_list t.sorts) in
  List.iter (fun d ->
    let head,args = R.decompose_app_list (Context.Named.Declaration.get_type d) in
    match args with
    | [ty] when R.eq_constr head (Lazy.force CoqTerms.cCompDec) &&
        List.exists (R.eq_constr ty) source_sorts ->
      ignore (SmtBtype.of_coq_compdec t.sorts ty
        (R.mkVar (Context.Named.Declaration.get_id d)))
    | _ -> ()) (Environ.named_context env)

let export ?(env=Global.env ()) t roots =
  register_instances env t;
  ignore (declarations t);
  let b = Buffer.create 4096 in
  let fmt = Format.formatter_of_buffer b in
  Format.fprintf fmt "(set-logic QF_UFLIA)@.";
  List.iter (fun (i,_) -> Format.fprintf fmt "(declare-sort %s 0)@." (name_sort i))
    (SmtBtype.to_list t.sorts);
  List.iter (fun (i,args,ret,_) ->
    Format.fprintf fmt "(declare-fun %s (%a) %a)@." (name_function i)
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_space fmt ()) SmtBtype.to_smt)
      (Array.to_list args) SmtBtype.to_smt ret) (Op.to_list t.functions);
  (* Export the same surface representation that the checked adapter binds.
     The legacy printer changes signed literals such as -3 into (- 3), which
     cvc5 faithfully retains in source assumptions. Both are integer terms,
     but they are different CPC trees. *)
  let tables = snapshot t and ns = names t in
  List.iter (fun f ->
    let encoded = C.compute_term_option env (C.call (adapter "encode_clause")
      (tables @ [ns;CoqTerms.mkNat 10000;clause [f]])) in
    match encoded with
    | Some term -> Format.fprintf fmt "(assert %a)@." E.pp_term term
    | None -> R.raise_error "Eunoia: exported root has no exact adapter encoding") roots;
  Format.fprintf fmt "(check-sat)@.(exit)@."; Format.pp_print_flush fmt (); Buffer.contents b

(* Translate syntax into the existing SMT-LIB reifier, never declarations or
   interpretations. Exact adapter binding is subsequently checked in Rocq. *)
let reify t term =
  let module A = Smtlib2.Smtlib2_ast in
  let loc = Lexing.dummy_pos,Lexing.dummy_pos in
  let ident s = A.QualIdentifierId(loc,A.IdSymbol(loc,A.Symbol(loc,s))) in
  let rec ast term = match E.spine term with
    | E.Symbol s,[] when String.length s > 0 &&
        (s.[0]='-' || (s.[0]>='0' && s.[0]<='9')) ->
      (try ignore (Big_int.big_int_of_string s)
        with _ -> R.raise_error "Eunoia: invalid generated integer %s" s);
      A.TermSpecConst(loc,A.SpecConstNum(loc,s))
    | E.Symbol s,[] -> A.TermQualIdentifier(loc,ident s)
    | E.Symbol (("+" | "*") as s), (a::b::c::rest) ->
      let rec chain x = function
        | [] -> ast x
        | y::ys -> A.TermQualIdTerm(loc,ident s,(loc,[ast x;chain y ys])) in
      chain a (b::c::rest)
    | E.Symbol s,xs -> A.TermQualIdTerm(loc,ident s,(loc,List.map ast xs))
    | _ -> R.raise_error "Eunoia: higher-order generated result unsupported" in
  Smtlib2_genConstr.make_root ~eqsym:false ~preserve_not:true t.atoms t.forms (ast term)

type prepared = {
  table_args : R.constr list;
  common_args : R.constr list;
  roots_arg : R.constr;
  tail_args : R.constr list;
  diagnose : unit -> unit;
  checker_api : string -> string;
}

let prepare ?(fuel=10000) ~witness env t roots parsed =
  if roots=[] || fuel<=0 || fuel>100000 then R.raise_error "Eunoia: invalid roots or computation fuel";
  register_instances env t;
  let ns = names t in
  let fuel = CoqTerms.mkNat fuel in
  let table_args = snapshot t in
  if SmtBtype.get_cuts t.sorts <> [] then
    R.raise_error "Eunoia: missing CompDec for an intermediate carrier; supply an existing instance";
  let encode c = match C.compute_term_option env
      (C.call (adapter "encode_clause") (table_args @ [ns;fuel;clause c])) with
    | Some x -> x
    | None -> R.raise_error "Eunoia: exported root has no exact adapter encoding" in
  let root_terms = List.map (fun r -> encode [r]) roots in
  let query = C.call (adapter "typeof")
    [List.nth table_args 0;List.nth table_args 1;ns;fuel] in
  let derive rule args premises =
    C.compute_term_option env (C.call "SMTCoq.checker.eunoia.CpcGenerated.derive"
      [fuel;query;C.string rule;C.term_list args;C.term_list premises]) in
  let derive_assuming rule assumption args premises =
    C.compute_term_option env (C.call "SMTCoq.checker.eunoia.CpcGenerated.derive_assuming"
      [fuel;query;C.string rule;C.term assumption;C.term_list args;C.term_list premises]) in
  let metadata_literals = Hashtbl.create 17 in
  let is_metadata_literal s =
    (* Lexical prefilter only. Actual admission is EoArithmetic's exact
       normalization/category contract, with source spelling retained. *)
    let numeric = String.length s > 0 &&
      (s.[0]='-' || (s.[0]>='0' && s.[0]<='9')) &&
      String.for_all (fun c -> (c>='0' && c<='9') || c='-' || c='.' || c='/') s in
    numeric && match Hashtbl.find_opt metadata_literals s with
      | Some b -> b
      | None ->
        let b = Stdlib.Option.is_some (C.compute_term_option env
          (C.call "SMTCoq.checker.eunoia.EoArithmetic.normalize" [C.term (E.Symbol s)])) in
        Hashtbl.add metadata_literals s b; b in
  let proof = E.elaborate ~signature_names:(C.signature_names env) ~is_metadata_literal
    ~declarations:(declarations t) ~roots:root_terms ~derive ~derive_assuming parsed in
  SmtMaps.clear ();
  List.iter (fun (i,ty) -> SmtMaps.add_btype (name_sort i) (SmtBtype.Tindex ty))
    (SmtBtype.to_list t.sorts);
  List.iter (fun (i,_,_,op) -> SmtMaps.add_fun (name_function i) op) (Op.to_list t.functions);
  Fun.protect ~finally:SmtMaps.clear (fun () ->
    let mapped = Hashtbl.create proof.capacity in
    List.iter2 (fun (i,_) r -> Hashtbl.add mapped i [r]) proof.roots roots;
    let checked_steps = ref [] in
    let result_clause st =
      if st.E.result=E.Symbol "false" then [] else [reify t st.result] in
    let evidence st syntax_cs cs c =
      let w = match witness ~atoms:t.atoms ~forms:t.forms ~premises:cs ~conclusion:c with
        | Ok w -> w
        | Error e -> R.raise_error
            "Eunoia: local witness failed at %s (%s): %s; source premises: %a; result: %a"
            st.E.name st.rule e
            (Format.pp_print_list ~pp_sep:Format.pp_print_space E.pp_term) st.premise_terms
            E.pp_term st.result in
      checked_steps := (st,syntax_cs,cs,c,w)::!checked_steps;
      Hashtbl.add mapped st.id c; w in
    let witness_ty = C.global (local "witness") in
    let rule_ty = C.global (adapter "rule_payload") in
    let parameters = [rule_ty;rule_ty;witness_ty] in
    let payload st c = C.call (adapter "Payload") [C.string st.E.rule;
      C.term_list st.arguments;C.term_list st.premise_terms;C.term st.result;clause c] in
    let ordinary st =
      let cs = List.map (Hashtbl.find mapped) st.E.premises in
      let c = result_clause st in
      let w = evidence st cs cs c in
      C.call (core "Step") [rule_ty;witness_ty;mkint st.id;
        C.list (Lazy.force CoqTerms.cint) (List.map mkint st.premises);payload st c;clause c;w] in
    let rec nested = function
      | E.Done -> C.call (scope "Done") parameters
      | E.Next(st,rest) ->
        let node = ordinary st in
        let tail = nested rest in
        C.call (scope "Next") (parameters @ [node;tail])
      | E.Push(slot,assumption,body,st,rest) ->
        let pushed = reify t assumption in
        let saved = Hashtbl.copy mapped in
        Hashtbl.add mapped slot [pushed];
        let body = nested body in
        let endpoint = match st.premises with
          | [id] -> id | _ -> R.raise_error "Eunoia: discharge needs exactly one endpoint" in
        let endpoint_clause = Hashtbl.find mapped endpoint in
        let guarded = List.sort_uniq (fun a b -> Int.compare (Form.to_lit a) (Form.to_lit b))
          (Form.neg pushed :: endpoint_clause) in
        let c = result_clause st in
        let w = evidence st [endpoint_clause] [guarded] c in
        let discharge = C.call (scope "Discharge") [rule_ty;witness_ty;
          mkint endpoint;mkint st.id;payload st c;clause c;w] in
        Hashtbl.clear mapped; Hashtbl.iter (Hashtbl.add mapped) saved;
        Hashtbl.add mapped st.id c;
        let tail = nested rest in
        let some = SmtMisc.mklApp CoqTerms.cSome [|C.global (scoped "discharge");discharge|] in
        C.call (scope "Push") (parameters @ [mkint slot;mkint (Form.to_lit pushed);body;some;tail]) in
    let has_scopes = List.exists (fun c -> match c.Eunoia_frontend.EunoiaProof.command with
      | Eunoia_frontend.EunoiaProof.Assume_push _ -> true | _ -> false) parsed.commands in
    let trace = if has_scopes then nested proof.trace else
      C.list (C.call (core "step") [rule_ty;witness_ty]) (List.map ordinary proof.steps) in
    (* Witness search may intern auxiliary equalities. Snapshot only after all
       results and witness candidates have populated the authoritative tables. *)
    let tables = snapshot t in
    let root_clauses = List.map (fun r -> [r]) roots in
    (* Recompute individual stages only after the final checker rejects. These
       diagnostics cannot turn rejection into acceptance or omit a step. *)
    let diagnose () =
      let check context computation =
        match R.vm_conv Conversion.CUMUL env computation (Lazy.force CoqTerms.ctrue) with
        | Result.Ok () -> ()
        | Result.Error () -> R.raise_error "Eunoia: %s" context in
      check "invalid final reification tables"
        (C.call (adapter "tables_wf") (tables @ [ns]));
      check "CPC roots differ from the authoritative formulas"
        (C.call (adapter "bind_terms") (tables @ [ns;fuel;clauses root_clauses;C.term_list root_terms]));
      List.iter (fun (st,syntax_cs,cs,c,evidence) ->
        let context stage = Printf.sprintf "%s at %s (%s)" stage st.E.name st.rule in
        check (context "premise syntax binding failed")
          (C.call (adapter "bind_terms") (tables @ [ns;fuel;clauses syntax_cs;C.term_list st.premise_terms]));
        check (context "conclusion syntax binding failed")
          (C.call (adapter "binds") (tables @ [ns;fuel;clause c;C.term st.result]));
        let gate = C.call (local "gate") (tables @ [clauses cs;clause c;evidence]) in
        (match R.vm_conv Conversion.CUMUL env gate (Lazy.force CoqTerms.ctrue) with
        | Result.Ok () -> ()
        | Result.Error () ->
          let machine_ty = C.global (local "machine") in
          let option_ty = SmtMisc.mklApp CoqTerms.coption [|machine_ty|] in
          let machine computation =
            match R.decompose_app_list (R.cbv_vm env computation option_ty) with
            | h,[_;m] when R.eq_constr h (Lazy.force CoqTerms.cSome) -> Some m
            | _ -> None in
          let roots = C.call (local "local_roots") [clauses cs;clause c] in
          let initial = C.call (local "initial") [C.call (local "capacity") [evidence]] in
          let loaded = C.call (local "load_roots")
            [mkint (Array.length (Form.pform_tbl t.forms));initial;roots;
             C.call (local "root_claims") [evidence]] in
          let command_ty = C.global (local "command") in
          let commands_ty = SmtMisc.mklApp CoqTerms.clist [|command_ty|] in
          let rec decode_commands list = match R.decompose_app_list list with
            | h,[_] when R.eq_constr h (Lazy.force CoqTerms.cnil) -> []
            | h,[_;x;xs] when R.eq_constr h (Lazy.force CoqTerms.ccons) -> x::decode_commands xs
            | _ -> R.raise_error "Eunoia: malformed computed local program" in
          let commands = decode_commands (R.cbv_vm env
            (C.call (local "program") [evidence]) commands_ty) in
          let rec inspect i m = function
            | [] -> ()
            | cmd::rest -> match machine (C.call (local "execute") (tables @ [m;cmd])) with
              | Some m -> inspect (i+1) m rest
              | None ->
                let action = C.call (local "action") [cmd] in
                let action = R.cbv_vm env action
                  (C.global "SMTCoq.checker.MainChecker.Checker_Ext.step") in
                let printed = Pp.string_of_ppcmds
                  (Printer.pr_constr_env env (Evd.from_env env) action) in
                R.raise_error "Eunoia: %s, local command %d: %s; source result: %a"
                  (context "local semantic certificate failed") i printed E.pp_term st.result in
          Stdlib.Option.iter (fun m -> inspect 0 m commands) (machine loaded);
          R.raise_error "Eunoia: %s; source result: %a"
            (context "local semantic certificate failed") E.pp_term st.result)) (List.rev !checked_steps) in
    {table_args=tables;
     common_args=tables @ [ns;fuel;mkint proof.capacity];
     roots_arg=clauses root_clauses;
     tail_args=[C.term_list root_terms;
       claims (List.map2 (fun (i,_) c -> i,c) proof.roots root_clauses);
       trace;mkint proof.conflict];diagnose;
     checker_api=(if has_scopes then scoped else tactic_api)})

let refutation env p =
  let args = p.common_args @ [p.roots_arg] @ p.tail_args in
  let accepted = C.checked_true ~on_failure:p.diagnose env (C.call (p.checker_api "checker") args) in
  let proof = C.call (p.checker_api "checker_correct") (args @ [accepted]) in
  ignore (Typing.type_of env (Evd.from_env env) (EConstr.of_constr proof));
  proof

let build_refutation_from_cpc ?fuel ~witness env t roots parsed =
  refutation env (prepare ?fuel ~witness env t roots parsed)

let tactic_using produce ?fuel ?(preprocess=Tactics.intros) ~witness ?(lemmas=[]) () =
  R.tclTHEN preprocess (R.mk_tactic (fun env sigma goal ->
    (* Introduced polymorphic carriers have fresh levels in the proof's evar
       map. VM conversion uses a kernel environment, so carry those levels
       and their constraints into it before evaluating any table or gate. *)
    let env = Environ.push_context_set (Evd.universe_context_set sigma) env in
    try
      let h,args = R.decompose_app_list goal in
      let a,b = match args with
        | [ty;a;b] when R.eq_constr h (Lazy.force CoqTerms.ceq) && R.eq_constr ty (Lazy.force CoqTerms.cbool) -> a,b
        | [a] when R.eq_constr h (Lazy.force CoqTerms.cis_true) -> a,(Lazy.force CoqTerms.ctrue)
        | _ -> R.raise_error "Eunoia: preprocess the goal to Boolean equality/is_true" in
      let t = create_tables () in
      let logic = SmtMisc.SL.of_list [SmtMisc.LUF;SmtMisc.LLia] in
      let reify = Form.of_coq (Atom.of_coq t.sorts t.functions t.atoms logic env sigma) t.forms in
      let fa = reify a and fb = reify b in
      let boolean_result = R.eq_constr b (Lazy.force CoqTerms.ctrue) ||
        R.eq_constr b (Lazy.force CoqTerms.cfalse) in
      let ng = if boolean_result && lemmas=[] then
        if R.eq_constr b (Lazy.force CoqTerms.ctrue) then Form.neg fa else fa
        else Form.neg (Form.get t.forms (SmtForm.Fapp(SmtForm.Fiff,[|fa;fb|]))) in
      let ls = List.map (fun p ->
        let ty = R.retyping_get_type_of env sigma p in
        let head,args = R.decompose_app_list ty in
        match args with
        | [v] when R.eq_constr head (Lazy.force CoqTerms.cis_true) -> reify v,p,v
        | [ty;v;b] when R.eq_constr head (Lazy.force CoqTerms.ceq) &&
            R.eq_constr ty (Lazy.force CoqTerms.cbool) && R.eq_constr b (Lazy.force CoqTerms.ctrue) -> reify v,p,v
        | _ -> R.raise_error "Eunoia: lemma must prove a quantifier-free Boolean fact") lemmas in
      if SmtBtype.get_cuts t.sorts <> [] then
        R.raise_error "Eunoia: supply CompDec instances through existing preprocessing";
      let roots = ng :: List.map (fun (f,_,_) -> f) ls in
      let parsed = produce env t roots in
      let prepared = prepare ?fuel ~witness env t roots parsed in
      if lemmas=[] then begin
        let name,args = if boolean_result then
          "checker_b",[Form.to_coq fa;b]
        else "checker_eq",[Form.to_coq fa;Form.to_coq fb;Form.to_coq ng] in
        let args = prepared.common_args @ args @ prepared.tail_args in
        let accepted = C.checked_true ~on_failure:prepared.diagnose env (C.call (prepared.checker_api name) args) in
        let proof = C.call (prepared.checker_api (name ^ "_correct")) (args @ [accepted]) in
        Tactics.exact_check (EConstr.of_constr proof)
      end else begin
      let refutation = refutation env prepared in
      let tables = prepared.table_args in
      let rho = C.call (local "valuation") tables in
      let valid = C.call (state "C.valid") [rho] in
      let cty = clause_ty () in
      let eqb = SmtMisc.mklApp CoqTerms.ceqb [|a;b|] in
      let hfalse = R.mkRel 1 in
      let f = R.mkLambda(R.mkName "b",(Lazy.force CoqTerms.cbool),
        SmtMisc.mklApp CoqTerms.corb [|SmtMisc.mklApp CoqTerms.cnegb [|R.mkRel 1|];
          Lazy.force CoqTerms.cfalse|]) in
      let neg_valid = C.call ("Corelib.Init.Logic.f_equal")
        [(Lazy.force CoqTerms.cbool);(Lazy.force CoqTerms.cbool);f;R.lift 1 eqb;Lazy.force CoqTerms.cfalse;hfalse] in
      let lemma_valid (_,p,v) =
        let f = R.mkLambda(R.mkName "b",(Lazy.force CoqTerms.cbool),
          SmtMisc.mklApp CoqTerms.corb [|R.mkRel 1;Lazy.force CoqTerms.cfalse|]) in
        C.call ("Corelib.Init.Logic.f_equal") [(Lazy.force CoqTerms.cbool);(Lazy.force CoqTerms.cbool);f;v;(Lazy.force CoqTerms.ctrue);p] in
      let root_cs = List.map (fun r -> [r]) roots in
      let ps = List.map (fun l -> R.lift 1 (lemma_valid l)) ls in
      let roots_proof =
        (* Lift tables and lemma proofs below the false-equality binder. *)
        let valid = R.lift 1 valid in
        let rec build cs ps = match cs,ps with
          | [],[] -> C.call ("Corelib.Lists.ListDef.Forall_nil") [cty;valid]
          | c::cs,p::ps -> C.call ("Corelib.Lists.ListDef.Forall_cons")
            [cty;valid;clause c;clauses cs;p;build cs ps]
          | _ -> R.raise_error "Eunoia: root proof length mismatch" in
        build root_cs (neg_valid::ps) in
      let contradiction = R.mkApp (R.lift 1 refutation,[|roots_proof|]) in
      let hty = SmtMisc.mklApp CoqTerms.ceq [|(Lazy.force CoqTerms.cbool);eqb;Lazy.force CoqTerms.cfalse|] in
      let not_false = R.mkLambda(R.mkName "eunoia_false",hty,contradiction) in
      let is_true = C.call (std "Bool.Bool.not_false_is_true") [eqb;not_false] in
      let proof = C.call (std "Bool.Bool.eqb_prop") [a;b;is_true] in
      Tactics.exact_check (EConstr.of_constr proof)
      end
    with
    | EunoiaSolver.Error s | E.Error s | Failure s | Invalid_argument s ->
      R.raise_error "Eunoia: %s" s))

let build_refutation ?limits ?fuel ~witness env t roots =
  let parsed = EunoiaSolver.run ?limits (export ~env t roots) in
  build_refutation_from_cpc ?fuel ~witness env t roots parsed

let tactic ?limits = tactic_using (fun env t roots ->
  EunoiaSolver.run ?limits (export ~env t roots))
let tactic_from_cpc parsed = tactic_using (fun _ _ _ -> parsed)
