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
  let previous = Sys.getenv_opt "EUNOIA_TOOLCHAIN_ROOT" in
  Fun.protect ~finally:(fun () -> Unix.putenv "EUNOIA_TOOLCHAIN_ROOT"
    (Stdlib.Option.value ~default:"" previous)) (fun () ->
    Unix.putenv "EUNOIA_TOOLCHAIN_ROOT" "/tmp/smtrocq-config-test";
    assert (EunoiaSolver.binary () =
      "/tmp/smtrocq-config-test/cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5");
    Unix.putenv "EUNOIA_TOOLCHAIN_ROOT" "relative/path";
    (try ignore (EunoiaSolver.binary ()); failwith "relative solver root accepted"
     with EunoiaSolver.Error _ -> ()));
  let previous = Sys.getenv_opt "EUNOIA_CVC5_PROFILE" in
  Fun.protect ~finally:(fun () -> Unix.putenv "EUNOIA_CVC5_PROFILE"
    (Stdlib.Option.value ~default:"" previous)) (fun () ->
    Unix.putenv "EUNOIA_CVC5_PROFILE" "default";
    assert (EunoiaSolver.profile_options () = [||]);
    Unix.putenv "EUNOIA_CVC5_PROFILE" "reduced";
    assert (Array.mem "--simplification=none" (EunoiaSolver.profile_options ()));
    Unix.putenv "EUNOIA_CVC5_PROFILE" "default --proof-allow-trust";
    (try ignore (EunoiaSolver.profile_options ()); failwith "unknown solver profile accepted"
     with EunoiaSolver.Error _ -> ()));
  let proof = run (prefix ^ "(step c false :rule contra :premises (a b))") in
  assert (proof.capacity=3 && proof.conflict=2);
  assert ((List.hd proof.steps).premises=[0;1]);
  let duplicate = run ~roots:[p;p;np] (prefix ^ "(step c false :rule contra :premises (a b))") in
  assert (duplicate.roots=[0,p;1,p;2,np]);
  assert ((List.hd duplicate.steps).premises=[0;2]);
  let repeated_source = run ~roots:[p;p;np]
    ("(declare-const p Bool)(assume a p)(assume duplicate p)" ^
     "(assume b (not p))(step c false :rule contra :premises (duplicate b))") in
  assert ((List.hd repeated_source.steps).premises=[1;2]);
  rejected (fun () -> run (prefix ^ "(step c :rule contra :premises (b a))"));
  rejected (fun () -> run (prefix ^ "(step c p :rule contra :premises (a b))"));
  rejected (fun () -> run (prefix ^ "(step unused :rule trust)(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ~roots:[np;p] (prefix ^ "(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ~declarations:[{name="p";typ=Symbol "Int"}]
    (prefix ^ "(step c :rule contra :premises (a b))"));
  rejected (fun () -> run ("(assume a true)(step c false :rule contra :premises (a a))"));
  rejected (fun () -> run (prefix ^ "(assume-push z true)(step-pop d :rule copy :args (false))"));
  let macros = "(declare-const p Bool)(define @t1 ((x Bool)) (not x))" ^
    "(define @t2 () (let ((u p)) u))(assume a @t2)(assume b (@t1 p))" ^
    "(step c false :rule contra :premises (a b))" in
  ignore (run macros);
  rejected (fun () -> elaborate ~max_expansion:2 ~declarations:decl ~roots:[p;np] ~derive (parse macros));
  (* Every unused definition is inspected, not only the final dependency cone. *)
  rejected (fun () -> run ("(define @t1 () mystery)" ^ prefix ^
    "(step c false :rule contra :premises (a b))"));
  (* Parallel let values see the outer bindings, never earlier siblings. *)
  let lets = "(declare-const p Bool)(define @t1 () true)" ^
    "(assume a (let ((@t1 p)(y @t1)) y))(assume b (not true))" ^
    "(step c false :rule contra :premises (a b))" in
  ignore (run ~roots:[Symbol "true"; app "not" [Symbol "true"]] lets);
  rejected (fun () -> run ("(define true () false)" ^ prefix ^
    "(step c false :rule contra :premises (a b))"));
  (* Syntax-only scope callbacks: real generated checking is covered by Proof.v. *)
  let derive_assuming name a args ps = match name,args,ps with
    | "scope",[],[c] -> Some (app "=>" [a;c]) | _ -> None in
  let scoped body = elaborate ~declarations:decl ~roots:[p;np] ~derive
    ~derive_assuming (parse (prefix ^ body)) in
  let inner = "(assume-push x p)(step local :rule copy :args (false))" ^
    "(step-pop exported :rule scope :premises (local))" in
  let final = "(step c :rule contra :premises (a b))" in
  let scoped_proof = scoped (inner ^ final) in
  (match scoped_proof.trace with
  | Push(2,Symbol "p",Next(local,Done),exported,Next(last,Done)) ->
    assert (local.id=3 && exported.id=4 && last.id=5 && exported.premises=[3])
  | _ -> failwith "scope occurrence/slot mapping changed");
  (match P.parse_string (prefix ^ inner ^ "(step c :rule contra :premises (a local))") with
  | Error _ -> () | Ok _ -> failwith "expired scope premise parsed");
  rejected (fun () -> scoped ("(assume-push x p)" ^
    "(step-pop exported :rule scope :premises (a b))" ^ final));
  rejected (fun () -> scoped ("(assume-push x p)(step unused :rule trust)" ^
    "(step-pop exported :rule scope :premises (x))" ^ final));
  rejected (fun () -> scoped ("(assume-push x p)(step local :rule copy :args (false))" ^
    "(step-pop exported :rule scope :premises (local))"));
  rejected (fun () -> run ("(define @t1 () |123|)" ^ prefix ^ final));
  rejected (fun () -> run ("(define @t1 ((p Bool)) p)" ^ prefix ^ final));
  rejected (fun () -> elaborate ~declarations:decl ~roots:[p;np] ~derive
    ~signature_names:["@list"]
    (parse ("(define @t1 ((@list Bool)) @list)" ^ prefix ^ final)));
  ignore (elaborate ~declarations:decl ~roots:[p;np] ~derive
    ~signature_names:["@list";"@list.nil"]
    (parse ("(define @t1 () (@list true @list.nil))" ^ prefix ^ final)));
  (* A mock validator tests only elaboration's callback boundary. Production
     uses the loaded EoArithmetic normalizer, never this finite test set. *)
  let metadata s = List.mem s ["1/2";"0.5"] in
  let metadata_defs = "(define @t1 () 1/2)(define @t2 () 0.5)" in
  rejected (fun () -> run (metadata_defs ^ prefix ^ final));
  ignore (elaborate ~declarations:decl ~roots:[p;np] ~derive
    ~is_metadata_literal:metadata (parse (metadata_defs ^ prefix ^ final)));
  rejected (fun () -> elaborate ~declarations:decl ~roots:[p;np] ~derive
    ~is_metadata_literal:metadata
    (parse ("(define @t1 () 1/3)" ^ prefix ^ final)));
  List.iter (fun number ->
    rejected (fun () -> elaborate
      ~declarations:({name=number;typ=Symbol "Int"}::decl) ~roots:[p;np] ~derive
      ~is_metadata_literal:metadata
      (parse ("(declare-const |" ^ number ^ "| Int)" ^ prefix ^ final)));
    rejected (fun () -> elaborate ~declarations:decl ~roots:[p;np] ~derive
      ~is_metadata_literal:metadata
      (parse ("(define @t1 ((|" ^ number ^ "| Bool)) |" ^ number ^ "|)" ^ prefix ^ final))))
    ["1/2";"0.5"];
  Printf.printf "elaboration: scope-free/scoped positives and corruption/resource cases passed\n%!";
  let solver_input = "(set-logic QF_UF)(declare-fun op_0 () Bool)" ^
    "(assert op_0)(assert (not op_0))(check-sat)(exit)" in
  let temporaries () = Sys.readdir (Filename.get_temp_dir_name ()) |> Array.to_list |>
    List.filter (fun s -> String.starts_with ~prefix:"smtrocq-eunoia-" s) |> List.sort String.compare in
  let before = temporaries () in
  let raw = EunoiaSolver.run solver_input in
  assert (raw.envelope=P.Unsat_parenthesized);
  let solver_rejected input = try ignore (EunoiaSolver.run input);
    failwith "solver unexpectedly accepted" with EunoiaSolver.Error _ -> () in
  solver_rejected "(set-logic QF_UF)(assert true)(check-sat)(exit)";
  solver_rejected "(set-logic QF_UF)(assert malformed)(check-sat)(exit)";
  (try ignore (EunoiaSolver.run
     ~limits:{EunoiaSolver.default_limits with max_bytes=1} solver_input);
     failwith "output limit not enforced" with EunoiaSolver.Error _ -> ());
  (try ignore (EunoiaSolver.run
     ~limits:{EunoiaSolver.default_limits with wall_seconds=1e-9} solver_input);
     failwith "wall limit not enforced" with EunoiaSolver.Error _ -> ());
  assert (before=temporaries ());
  Printf.printf "private cvc5: unsat parsed; sat, malformed input, oversized output and wall timeout rejected; temporary files cleaned\n%!"
