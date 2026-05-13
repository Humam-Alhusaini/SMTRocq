(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2026                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


open SmtMisc
open CoqTerms
open SmtForm
open SmtAtom
open SmtTrace
open SmtCertif

let ra = Atom.create ()
let rf = Form.create ()


let compute_roots roots last_root =
  let r = ref last_root in
  while (has_prev !r) do
    r := prev !r
  done;

  let rec find_root i root = function
    | [] -> assert false
    | t::q -> if Form.equal t root then i else find_root (i+1) root q in

  let rec used_roots acc r =
    if isRoot r.kind then
      match r.value with
        | Some [root] ->
           let j = find_root 0 root roots in
           used_roots (j::acc) (next r)
        | _ -> assert false
    else acc
  in

  used_roots [] !r


(* Bound variables are given fresh names to avoid variable capture *)
let gen_rel_name =
  let num = ref (-1) in
  fun () -> incr num; "SMTCoqRelName"^(string_of_int !num)

let warn_discarding_lemma =
  CWarnings.create ~name:"SMTCoq-discarding-lemma" ~category:CoqInterface.smtcoq_cat
    Pp.(fun clemma ->
        str "Discarding the following lemma (unsupported):" ++ spc() ++
        str (SmtMisc.string_coq_constr clemma))

let of_coq_lemma rt ro ra_quant rf_quant env sigma solver_logic clemma : Form.t option =
  let warn () =
    warn_discarding_lemma clemma;
    None
  in

  let rel_context, qf_lemma = Term.decompose_prod_decls clemma in
  let rel_context = List.map (fun rel -> Context.Rel.Declaration.set_name (Names.Name.mk_name (Names.Id.of_string (gen_rel_name ()))) rel) rel_context in

  let env_lemma = Environ.push_rel_context rel_context env in
  let f, args = CoqInterface.decompose_app_list qf_lemma in
  let _ = Feedback.msg_notice (Printer.pr_constr_env env_lemma sigma qf_lemma) in
  let _ = Feedback.msg_notice (Printer.pr_context_unlimited env_lemma sigma) in
  let core_f =
    if CoqInterface.eq_constr f (Lazy.force cis_true) then
      match args with
      | [a] -> Some a
      | _ -> Pp.str "Does not have is_true _ structure" |> Feedback.msg_notice; warn ()
    else if CoqInterface.eq_constr f (Lazy.force ceq) then
      match args with
      | [ty; arg1; arg2] when CoqInterface.eq_constr ty (Lazy.force cbool) &&
                                CoqInterface.eq_constr arg2 (Lazy.force ctrue) ->
         Some arg1
      | _ -> Pp.str "Does not have (_ =? _ = true) structure" |> Feedback.msg_notice; warn ()
    else let _ = Pp.str "has neither" |> Feedback.msg_notice in warn () in
  let core_smt =
    match core_f with
      | Some core_f ->
         (try
            Some (Form.of_coq (Atom.of_coq ~eqsym:true rt ro ra_quant solver_logic env_lemma sigma) rf_quant core_f)
          with
          | Atom.UnknownUnderForall -> Pp.str "unkown atom" |> Feedback.msg_notice; warn ()
         )
      | None -> None
  in
  let forall_args =
    let fmap r = let n, t = CoqInterface.destruct_rel_decl r in
                 CoqInterface.string_of_name n, SmtBtype.of_coq rt solver_logic t in
    List.map fmap rel_context
  in
  match forall_args with
    | [] -> core_smt
    | _ ->
       (match core_smt with
          | Some core_smt -> Some (Form.get rf_quant (Fapp (Fforall forall_args, [|core_smt|])))
          | None -> None)

let string_logic l =
    Printf.sprintf "QF_%s%s%s%s"
    (if SL.mem LArrays l then "A" else "")
    (if SL.mem LUF l || SL.mem LLia l then "UF" else "")
    (if SL.mem LBitvectors l then "BV" else "")
    (if SL.mem LLia l then "LIA" else "");;

let cvc4_logic =
  SL.of_list [LUF; LLia; LBitvectors; LArrays];;

let export_to_string rt ro l =
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  Format.fprintf fmt "(set-logic %s)@." (string_logic cvc4_logic);
  List.iter (fun (i,t) ->
    let s = "Tindex_"^(string_of_int i) in
    SmtMaps.add_btype s (SmtBtype.Tindex t);
    Format.fprintf fmt "(declare-sort %s 0)@." s
  ) (SmtBtype.to_list rt);
  List.iter (fun (i,cod,dom,op) ->
    let s = "op_"^(string_of_int i) in
    SmtMaps.add_fun s op;
    Format.fprintf fmt "(declare-fun %s (" s;
    let is_first = ref true in
    Array.iter (fun t ->
        if !is_first then is_first := false
        else Format.fprintf fmt " "; SmtBtype.to_smt fmt t
      ) cod;
    Format.fprintf fmt ") %a)@." SmtBtype.to_smt dom;
  ) (Op.to_list ro);
  Format.fprintf fmt "(assert (not %a))@\n(check-sat)@\n(exit)@."
    (Form.to_smt ~debug:false) l;
  Format.pp_print_flush fmt ();
  Buffer.contents buf;;

let rearrange_of_coq_lemma rt ro ra_quant rf_quant solver_logic env sigma clemma : unit Proofview.tactic =
  let opt = of_coq_lemma rt ro ra_quant rf_quant env sigma solver_logic clemma in
  match opt with
  | None -> warn_discarding_lemma clemma; Proofview.tclUNIT ();
  | Some form -> export_to_string rt ro form |> Pp.str |> Feedback.msg_notice;
  Proofview.tclUNIT ();;

let reify () =
  let rt = SmtBtype.create () in
  let ro = Op.create () in
  Atom.clear ra;
  Form.clear rf;
  CoqInterface.mk_tactic (rearrange_of_coq_lemma rt ro ra rf cvc4_logic);;
