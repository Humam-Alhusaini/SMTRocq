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
  let eval premises conclusion w =
    let term = app (lookup "witness_gate") [SmtAtom.Atom.interp_tbl atoms;
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
  if name = "lia-scaling" then begin
    let program = List.map (fun cmd -> match cmd.Certificate.action with
      | Certificate.LiaMicromega (p,c,_) ->
        {cmd with action=Certificate.LiaMicromega (p,c,[])}
      | _ -> cmd) w.program in
    if eval premises conclusion {w with program} then
      failwith (name ^ ": gate accepted missing Micromega certificate")
  end

let run () = Witness_cases.run ~check
