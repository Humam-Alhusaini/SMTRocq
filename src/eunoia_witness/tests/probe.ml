(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

(* Optional integration probe, loaded after a Rocq file defines [witness_gate]
   as the local gate specialized to its irrelevant interpretation tables. No
   proof constants or unchecked casts are installed by this test module. *)
open Common
open Eunoia_witness

let lookup name = UnivGen.constr_of_monomorphic_global (Global.env ())
  (Nametab.locate (Libnames.qualid_of_string name))

let check name atoms forms premises conclusion w =
  Witness_cases.check_shape name atoms forms premises conclusion w;
  let open RocqInterface in
  let app c xs = mkApp (c,Array.of_list xs) in
  let int_ty = Lazy.force CoqTerms.cint in
  let list ty f xs = List.fold_right (fun x tl ->
    app (Lazy.force CoqTerms.ccons) [ty;f x;tl]) xs
    (app (Lazy.force CoqTerms.cnil) [ty]) in
  let clause = list int_ty (fun f -> mkInt (SmtAtom.Form.to_lit f)) in
  let clause_ty = app (Lazy.force CoqTerms.clist) [int_ty] in
  let local s = lookup ("EunoiaLocal.EunoiaLocal." ^ s) in
  let step s = lookup ("SMTCoq.checker.MainChecker.Checker_Ext." ^ s) in
  let wterm w = Certificate.to_coq ~local ~step w in
  (* Supply real signatures and total denotations, then require Atom.wt in
     witness_gate. Empty/default-Boolean function tables mask type errors. *)
  let signatures = Hashtbl.create 17 in
  let rec visit a = match SmtAtom.Atom.atom a with
    | SmtAtom.Aapp (f,xs) ->
      Hashtbl.replace signatures (SmtAtom.indexed_op_index f)
        (Array.to_list (Array.map SmtAtom.Atom.type_of xs),SmtAtom.Atom.type_of a);
      Array.iter visit xs
    | SmtAtom.Auop (_,a) -> visit a
    | SmtAtom.Abop (_,a,b) -> visit a; visit b
    | SmtAtom.Atop (_,a,b,c) -> visit a; visit b; visit c
    | SmtAtom.Anop (_,xs) -> Array.iter visit xs
    | SmtAtom.Acop _ -> () in
  (* Include every function reachable from the final formula table. *)
  Array.iter (function SmtForm.Fatom a -> visit a | _ -> ()) (SmtAtom.Form.pform_tbl forms);
  let type_ty = lookup "SMTCoq.checker.fol.Terms.Typ.type" in
  let value args result = app (lookup "witness_value")
    [list type_ty SmtBtype.to_coq args;SmtBtype.to_coq result] in
  let default = value [] SmtBtype.Tbool in
  let bound = Hashtbl.fold (fun i _ n -> max n (i+1)) signatures 0 in
  let values = Array.init (bound+1) (fun i -> match Hashtbl.find_opt signatures i with
    | None -> default | Some (args,result) -> value args result) in
  let value_ty = app (lookup "SMTCoq.checker.fol.Terms.Atom.tval")
    [lookup "witness_probe_types"] in
  let functions = CoqTerms.mkArray (value_ty,values) in
  let eval premises conclusion w =
    let term = app (lookup "witness_gate") [functions;SmtAtom.Atom.interp_tbl atoms;
      snd (SmtAtom.Form.interp_tbl forms);list clause_ty clause premises;
      clause conclusion;wterm w] in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let term = EConstr.of_constr term in
    let sigma, _ = Typing.type_of env sigma term in
    let result = Vnorm.cbv_vm env sigma term (EConstr.of_constr (Lazy.force CoqTerms.cbool)) in
    eq_constr (EConstr.to_constr sigma result) (Lazy.force CoqTerms.ctrue) in
  if not (eval premises conclusion w) then failwith (name ^ ": local gate rejected candidate");
  if eval premises conclusion {w with Certificate.capacity=0} then
    failwith (name ^ ": gate accepted bad capacity");
  if w.root_claims <> [] && eval premises conclusion {w with root_claims=List.tl w.root_claims}
  then failwith (name ^ ": gate accepted missing root");
  (match w.root_claims with
   | (i,a)::(j,b)::rest when a <> b ->
     if eval premises conclusion {w with root_claims=(i,b)::(j,a)::rest} then
       failwith (name ^ ": gate accepted reordered root contents")
   | _ -> ());
  (match w.program with
   | [] -> ()
   | cmd::rest ->
     let changed = if cmd.expected = [] then [0] else [] in
     if eval premises conclusion {w with program={cmd with expected=changed}::rest} then
       failwith (name ^ ": gate accepted altered expected clause"));
  (* Keep the candidate fixed, but change the implication's premises. *)
  if premises <> [] && eval (List.tl premises) conclusion w then
    failwith (name ^ ": gate accepted changed premises");
  if conclusion <> [] && eval premises [] w then
    failwith (name ^ ": gate accepted changed conclusion");
  (* Corrupt a theory operation's evidence while preserving its claimed output
     and every root. This must be caught by actual EUF recomputation. *)
  let corrupted = ref false in
  let program = List.map (fun cmd ->
    if !corrupted then cmd else match cmd.Certificate.action with
    | Certificate.EqTr (p,l,_::_) ->
      corrupted := true; {cmd with action=Certificate.EqTr (p,l,[])}
    | Certificate.EqCgr (p,l,es) when List.exists Stdlib.Option.is_some es ->
      corrupted := true;
      {cmd with action=Certificate.EqCgr (p,l,List.map (fun _ -> None) es)}
    | Certificate.BoolCongr (p,l,es) when List.exists Stdlib.Option.is_some es ->
      corrupted := true;
      {cmd with action=Certificate.BoolCongr (p,l,List.map (fun _ -> None) es)}
    | Certificate.EqCgrP (p,a,b,es) when List.exists Stdlib.Option.is_some es ->
      corrupted := true;
      {cmd with action=Certificate.EqCgrP (p,a,b,List.map (fun _ -> None) es)}
    | _ -> cmd) w.program in
  if !corrupted && eval premises conclusion {w with program} then
    failwith (name ^ ": gate accepted corrupted EUF evidence");
  if name = "lia-scaling" then begin
    let program = List.map (fun cmd -> match cmd.Certificate.action with
      | Certificate.LiaMicromega (p,c,_) ->
        {cmd with action=Certificate.LiaMicromega (p,c,[])}
      | _ -> cmd) w.program in
    if eval premises conclusion {w with program} then
      failwith (name ^ ": gate accepted missing Micromega certificate")
  end

let run () = Witness_cases.run ~check
