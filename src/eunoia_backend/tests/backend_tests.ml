open Eunoia_backend
open EunoiaElaborate
module P = Eunoia_frontend.EunoiaProof
let parse s = match P.parse_string s with
  | Ok p -> p | Error d -> failwith (Format.asprintf "%a" P.pp_diagnostic d)
let rejected f = try ignore (f ()); failwith "unexpected acceptance" with Error _ -> ()
let decl = [{name="p";typ=Symbol "Bool"}]
let p = Symbol "p"
let np = app "not" [p]
(* Deliberately a test callback, not a production CPC implementation. *)
let derive name args premises = match name,args,premises with
  | "contra",[],[x;y] when y=app "not" [x] -> Some (Symbol "false")
  | "copy",[x],[] -> Some x
  | _ -> None
let run ?(declarations=decl) ?(roots=[p;np]) s =
  elaborate ~declarations ~roots ~derive (parse s)
let prefix = "(declare-const p Bool)(assume a p)(assume b (not p))"
let () =
  let proof = run (prefix ^ "(step c false :rule contra :premises (a b))") in
  assert (proof.capacity=3 && proof.conflict=2);
  assert ((List.hd proof.steps).premises=[0;1]);
  rejected (fun () -> run (prefix ^ "(step c :rule contra :premises (b a))"));
  rejected (fun () -> run (prefix ^ "(step c p :rule contra :premises (a b))"));
  rejected (fun () -> run (prefix ^ "(step unused :rule trust)(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ~roots:[np;p] (prefix ^ "(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ~declarations:[{name="p";typ=Symbol "Int"}]
    (prefix ^ "(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ("(assume a true)(step c false :rule contra :premises (a a))"));
  rejected (fun () -> run (prefix ^ "(assume-push z true)(step-pop d :rule copy :args (false))"));
  let macros = "(declare-const p Bool)(define n ((x Bool)) (not x))" ^
    "(define q () (let ((u p)) u))(assume a q)(assume b (n p))" ^
    "(step c false :rule contra :premises (a b))" in
  ignore (run macros);
  rejected (fun () -> elaborate ~max_expansion:2 ~declarations:decl ~roots:[p;np] ~derive (parse macros));
  (* Every unused definition is inspected, not only the final dependency cone. *)
  rejected (fun () -> run ("(define unused () mystery)" ^ prefix ^
    "(step c false :rule contra :premises (a b))"));
  (* Parallel let values see the outer bindings, never earlier siblings. *)
  let lets = "(declare-const p Bool)(define x () true)" ^
    "(assume a (let ((x p)(y x)) y))(assume b (not true))" ^
    "(step c false :rule contra :premises (a b))" in
  ignore (run ~roots:[Symbol "true"; app "not" [Symbol "true"]] lets);
  Printf.printf "elaboration: positive and 10 corruption/resource cases passed\n%!";
  let solver_input = "(set-logic QF_UF)(declare-fun op_0 () Bool)" ^
    "(assert op_0)(assert (not op_0))(check-sat)(exit)" in
  let raw = EunoiaSolver.run solver_input in
  assert (raw.envelope=P.Unsat_parenthesized);
  let solver_rejected input = try ignore (EunoiaSolver.run input);
    failwith "solver unexpectedly accepted" with EunoiaSolver.Error _ -> () in
  solver_rejected "(set-logic QF_UF)(assert true)(check-sat)(exit)";
  solver_rejected "(set-logic QF_UF)(assert malformed)(check-sat)(exit)";
  (try ignore (EunoiaSolver.run
     ~limits:{EunoiaSolver.default_limits with max_bytes=1} solver_input);
     failwith "output limit not enforced" with EunoiaSolver.Error _ -> ());
  Printf.printf "private cvc5: unsat parsed; sat, malformed input, oversized output rejected\n%!"
