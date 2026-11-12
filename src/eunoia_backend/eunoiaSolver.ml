module P = Eunoia_frontend.EunoiaProof

type limits = {
  wall_seconds : float;
  solver_milliseconds : int;
  resources : int;
  max_bytes : int;
}
let default_limits = {
  wall_seconds = 65.; solver_milliseconds = 60000;
  resources = 10000000; max_bytes = 32 * 1024 * 1024;
}
exception Error of string
let fail fmt = Format.kasprintf (fun s -> raise (Error s)) fmt
let toolchain_root () =
  let nonempty name = match Sys.getenv_opt name with Some s when s <> "" -> Some s | _ -> None in
  let root = match nonempty "EUNOIA_TOOLCHAIN_ROOT" with
    | Some s -> s
    | None ->
      let cache = match nonempty "XDG_CACHE_HOME" with
        | Some s -> s
        | None -> match nonempty "HOME" with
          | Some s -> Filename.concat s ".cache"
          | None -> fail "Eunoia: set EUNOIA_TOOLCHAIN_ROOT (HOME is unavailable)" in
      Filename.concat cache "smtrocq" in
  if Filename.is_relative root then fail "Eunoia: EUNOIA_TOOLCHAIN_ROOT/cache path must be absolute";
  root
let binary () = Filename.concat (toolchain_root ()) "cvc5-1.4.2/cvc5-Linux-x86_64-static/bin/cvc5"
let signature () = Filename.concat (toolchain_root ()) "cvc5-1.4.2/cvc5-cvc5-1.4.2/proofs/eo/cpc/Cpc.eo"
let use_declared_conclusions () = Sys.getenv_opt "EUNOIA_DECLARED_CONCLUSIONS" <> Some "0"
let profile_options () =
  match Sys.getenv_opt "EUNOIA_CVC5_PROFILE" with
  | None | Some "" | Some "default" -> [||]
  | Some "reduced" -> [|"--simplification=none"; "--no-static-learning";
      "--no-ite-simp"; "--no-unconstrained-simp"; "--no-repeat-simp"|]
  | Some name -> fail "Unknown EUNOIA_CVC5_PROFILE %S (expected default or reduced)" name
let remove f = try Sys.remove f with Sys_error _ -> ()
let read_file path limit =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () ->
    really_input_string ic (min limit (in_channel_length ic)))

let run ?(limits=default_limits) input =
  let profile = profile_options () in
  if limits.wall_seconds <= 0. || not (Float.is_finite limits.wall_seconds) ||
     limits.solver_milliseconds <= 0 || limits.resources <= 0 || limits.max_bytes <= 0
  then fail "Invalid Eunoia solver resource limits";
  let binary = binary () in
  (try Unix.access binary [Unix.X_OK] with Unix.Unix_error _ ->
    fail "Eunoia: pinned cvc5 is unavailable at %s; run python3 scripts/eunoia/install_toolchain.py or set EUNOIA_TOOLCHAIN_ROOT" binary);
  let files = ref [] in
  let temp suffix =
    let f, oc = Filename.open_temp_file "smtrocq-eunoia-" suffix in
    files := f :: !files; close_out oc; f in
  let pid = ref None in
  let stop () = match !pid with
    | None -> ()
    | Some p ->
      (* setsid gives the solver a private process group. Also kill p directly
         in case an exception happened before the child called setsid. *)
      (try Unix.kill (-p) Sys.sigkill with Unix.Unix_error _ -> ());
      (try Unix.kill p Sys.sigkill with Unix.Unix_error _ -> ());
      let rec reap () = try ignore (Unix.waitpid [] p) with
        | Unix.Unix_error (Unix.EINTR, _, _) -> reap ()
        | Unix.Unix_error (Unix.ECHILD, _, _) -> () in
      reap (); pid := None in
  Fun.protect ~finally:(fun () -> stop (); List.iter remove !files) (fun () ->
    let src = temp ".smt2" and out = temp ".cpc" and err = temp ".stderr" in
    let oc = open_out_bin src in
    Fun.protect ~finally:(fun () -> close_out_noerr oc)
      (fun () -> output_string oc input);
    let argv = Array.concat [[|binary; "--lang=smt2"; "--dump-proofs"; "--proof-format=cpc";
      "--proof-granularity=dsl-rewrite"; "--no-proof-allow-trust";
      "--proof-check=eager"; "--check-proofs-complete"|]; profile;
      (if use_declared_conclusions () then [|"--proof-print-conclusion"|] else [||]);
      [|"--tlimit=" ^ string_of_int limits.solver_milliseconds;
        "--rlimit=" ^ string_of_int limits.resources; src|]] in
    let started = Unix.gettimeofday () in
    let child = Unix.fork () in
    if child = 0 then begin
      (try
        ignore (Unix.setsid ());
        let infd = Unix.openfile "/dev/null" [Unix.O_RDONLY] 0 in
        let outfd = Unix.openfile out [Unix.O_WRONLY; Unix.O_TRUNC] 0 in
        let errfd = Unix.openfile err [Unix.O_WRONLY; Unix.O_TRUNC] 0 in
        Unix.dup2 infd Unix.stdin; Unix.dup2 outfd Unix.stdout;
        Unix.dup2 errfd Unix.stderr;
        List.iter Unix.close [infd; outfd; errfd];
        Unix.execv binary argv
      with _ -> Unix._exit 127)
    end;
    pid := Some child;
    let rec wait () =
      if (Unix.stat out).Unix.st_size > limits.max_bytes ||
         (Unix.stat err).Unix.st_size > limits.max_bytes
      then fail "cvc5 output exceeded %d bytes" limits.max_bytes;
      if Unix.gettimeofday () -. started > limits.wall_seconds
      then fail "cvc5 exceeded the %.3gs wall limit" limits.wall_seconds;
      match Unix.waitpid [Unix.WNOHANG] child with
      | 0, _ -> ignore (Unix.select [] [] [] 0.01); wait ()
      | _, status ->
        (try Unix.kill (-child) Sys.sigkill with Unix.Unix_error _ -> ());
        pid := None; status
      | exception Unix.Unix_error (Unix.EINTR, _, _) -> wait () in
    let status = wait () in
    (* Recheck after exit: a small fast process can finish between polls. *)
    if (Unix.stat out).Unix.st_size > limits.max_bytes ||
       (Unix.stat err).Unix.st_size > limits.max_bytes
    then fail "cvc5 output exceeded %d bytes" limits.max_bytes;
    (match status with
    | Unix.WEXITED 0 -> ()
    | _ ->
      let why = match status with
        | Unix.WEXITED n -> "exit " ^ string_of_int n
        | Unix.WSIGNALED n -> "signal " ^ string_of_int n
        | Unix.WSTOPPED n -> "stopped " ^ string_of_int n in
      fail "cvc5 failed (%s): %s" why (read_file err 4096));
    match P.parse_file ~limits:{P.default_limits with max_bytes=limits.max_bytes} out with
    | Error d -> fail "cvc5 CPC parse failed: %a; stdout: %s; stderr: %s"
        P.pp_diagnostic d (read_file out 4096) (read_file err 4096)
    | Ok ({P.envelope=P.Unsat_parenthesized; _} as p) -> p
    | Ok _ -> fail "cvc5 did not return an unsat CPC envelope")
