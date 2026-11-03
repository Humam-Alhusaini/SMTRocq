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

open Eunoia_frontend.EunoiaProof

let count = ref 0
let test name run =
  incr count;
  try run () with exn ->
    Printf.eprintf "FAIL %s: %s\n%!" name (Printexc.to_string exn);
    exit 1
let check message b = if not b then failwith message
let contains s sub =
  let rec go i = i + String.length sub <= String.length s
    && (String.sub s i (String.length sub) = sub || go (i + 1)) in
  go 0
let ok ?check_directive text = match parse_string ?check_directive text with
  | Ok proof -> proof
  | Error d -> failwith (Format.asprintf "%a" pp_diagnostic d)
let bad ?limits ?check_directive message text =
  match parse_string ?limits ?check_directive text with
  | Ok _ -> failwith ("unexpected parse success: " ^ text)
  | Error d ->
      check ("expected diagnostic containing " ^ message ^ ", got " ^ d.message)
        (contains d.message message);
      d
let reject message text = ignore (bad message text)
let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in_noerr channel)
    (fun () -> really_input_string channel (in_channel_length channel))
let replace_once text before after =
  let rec go i =
    if i + String.length before > String.length text then failwith ("missing mutation " ^ before)
    else if String.sub text i (String.length before) = before then
      String.sub text 0 i ^ after ^
      String.sub text (i + String.length before) (String.length text - i - String.length before)
    else go (i + 1)
  in go 0
let steps proof = List.filter_map (fun c -> match c.command with
  | Step step | Step_pop (_, step) -> Some step | _ -> None) proof.commands
let assumes proof = List.filter_map (fun c -> match c.command with
  | Assume a | Assume_push (_, a) -> Some a | _ -> None) proof.commands
let final_step proof = match List.rev (steps proof) with s :: _ -> s | [] -> failwith "no step"
let command_at proof n = (List.nth proof.commands n).command
let is_name text = function { view = Name (name, _); _ } -> name.text = text | _ -> false
let () =
  let uf = read "fixtures/uf4.cpc" in
  let lia = read "fixtures/lia-small.cpc" in
  let scoped_lia = read "fixtures/lia1.cpc" in
  test "actual UF envelope and complete step stream" (fun () ->
    let p = ok uf in
    check "unsat wrapper" (p.envelope = Unsat_parenthesized);
    check "all commands" (List.length p.commands = 27);
    check "all steps" (List.length (steps p) = 15);
    check "root" (List.length (assumes p) = 1);
    check "final false preserved" (Option.fold ~none:false ~some:(is_name "false") (final_step p).conclusion);
    let root = List.hd (assumes p) in
    let use = List.find (fun s -> s.name.text = "@p6") (steps p) in
    check "premise resolved" ((List.hd use.premises).target = root.id);
    check "source line" (root.name.loc.start.line = 14));
  test "actual LIA steps and multiple roots" (fun () ->
    let p = ok lia in
    check "two input assumptions" (List.length (assumes p) = 2);
    check "seven steps" (List.length (steps p) = 7);
    check "arithmetic rule unchanged"
      (List.exists (fun s -> s.rule.text = "arith-leq-norm") (steps p));
    check "final false" (Option.fold ~none:false ~some:(is_name "false") (final_step p).conclusion));
  test "actual LIA nested scopes and nonmonotonic CPC IDs" (fun () ->
    let p = ok scoped_lia in
    let pushes = List.filter_map (fun c -> match c.command with Assume_push (id, _) -> Some id | _ -> None) p.commands in
    let pops = List.filter_map (fun c -> match c.command with Step_pop (id, _) -> Some id | _ -> None) p.commands in
    check "six scopes" (List.length pushes = 6 && List.length pops = 6);
    check "each popped once" (List.sort compare pushes = List.sort compare pops);
    let s = List.find (fun s -> s.name.text = "@p132") (steps p) in
    let p80 = List.find (fun s -> s.name.text = "@p80") (steps p) in
    check "premise is ID, not suffix or stack offset" ((List.hd s.premises).target = p80.id));
  test "bare and wrapper-only command streams" (fun () ->
    let text = "(assume a true) (step b false :rule r :premises (a))" in
    let bare = ok text and wrapped = ok ("(" ^ text ^ ")") in
    check "bare" (bare.envelope = Bare);
    check "wrapped" (wrapped.envelope = Parenthesized);
    check "same commands with shifted spans"
      (List.length bare.commands = List.length wrapped.commands));
  test "empty streams carry no validity claim" (fun () ->
    List.iter (fun text -> check "empty AST" ((ok text).commands = [])) [""; "(); comment"; "unsat\n()"]);
  test "quoted names have decoded identity" (fun () ->
    let p = ok "(assume |p with space| true)(step q :rule r :premises (|p with space|))" in
    let a = List.hd (assumes p) and s = final_step p in
    check "quoted spelling" a.name.quoted;
    check "quoted premise" ((List.hd s.premises).target = a.id);
    reject "duplicate name" "(assume x true)(step |x| :rule r)";
    let p = ok "(assume |x| true)(step y :rule r :premises (x))" in
    check "quoted and bare lookup" ((List.hd (final_step p).premises).target = (List.hd (assumes p)).id));
  test "all literal spellings and SMT string escapes preserved" (fun () ->
    let text = {|(step p :rule r :args (12 -12 1.25 -1.25 1/2 -1/2 #b001 #x1f "a""b\u{a}\n" |a b;()"|))|} in
    let p = ok text in
    let literals = List.filter_map (fun t -> match t.view with Literal x -> Some x | _ -> None) (final_step p).args in
    check "literal kinds and exact spellings" (literals =
      [Numeral "12"; Numeral "-12"; Decimal "1.25"; Decimal "-1.25";
       Rational "1/2"; Rational "-1/2"; Binary "#b001"; Hexadecimal "#x1f";
       String {|a""b\u{a}\n|}]);
    check "quoted symbol remains symbol" (is_name {|a b;()"|} (List.nth (final_step p).args 9)));
  test "sharing IDs and chronological term binding" (fun () ->
    let p = ok "(declare-sort U 0)(declare-const x U)(define t () x)(assume a (= t x))" in
    match command_at p 0, command_at p 1, command_at p 2, command_at p 3 with
    | Declare u, Declare x, Define t, Assume { formula = { view = Apply (_, [tuse; xuse]); _ }; _ } ->
        (match x.kind, t.body.view, tuse.view, xuse.view with
        | Const { view = Name (_, Some uid); _ }, Name (_, Some xid), Name (_, Some tid), Name (_, Some xid2) ->
            check "sort reference" (uid = u.binding);
            check "definition capture" (xid = x.binding && xid2 = x.binding);
            check "sharing reference" (tid = t.binding)
        | _ -> failwith "missing term links")
    | _ -> failwith "missing commands");
  test "parameterized macros retain typed lexical binders" (fun () ->
    let p = ok "(declare-sort U 0)(declare-fun f (U U) U)(define swap ((x U) (y U)) (f y x))(assume p (swap a b))" in
    match command_at p 2 with
    | Define { parameters = [x; y]; body = { view = Apply (_, [a; b]); _ }; _ } ->
        (match a.view, b.view with
        | Name (_, Some yid), Name (_, Some xid) -> check "macro lexical links" (xid = x.binding && yid = y.binding)
        | _ -> failwith "unbound parameters")
    | _ -> failwith "bad macro");
  test "parallel let bindings and lexical shadowing" (fun () ->
    let p = ok "(declare-const x Int)(assume a (let ((x 1) (y x)) (= x y)))" in
    match command_at p 0, (List.hd (assumes p)).formula.view with
    | Declare outer, Let ([x; y], { view = Apply (_, [a; b]); _ }) ->
        (match y.value.view, a.view, b.view with
        | Name (_, Some outer_id), Name (_, Some xid), Name (_, Some yid) ->
            check "RHS reads outer x" (outer_id = outer.binding);
            check "body sees lexical x/y" (xid = x.binding && yid = y.binding)
        | _ -> failwith "bad let links")
    | _ -> failwith "bad let");
  test "nested scopes restore proof and declaration environments" (fun () ->
    let p = ok "(declare-const x Int)(assume a true)(assume-push b true)(declare-const y Int)(define t () y)(assume-push c true)(step d :rule r :premises (a b c) :args (t))(step-pop e :rule scope :premises (d))(step-pop f false :rule scope :premises (e))(step g :rule r :premises (a f) :args (x y t))" in
    let s = final_step p in
    check "result in root scope" (s.scope = None);
    (match s.args with
    | [{ view = Name (_, Some _); _ }; { view = Name (_, None); _ }; { view = Name (_, None); _ }] -> ()
    | _ -> failwith "local term environments not restored");
    match command_at p 3, command_at p 4 with
    | Declare d, Define f -> check "local scope tagged" (d.scope <> None && d.scope = f.scope)
    | _ -> failwith "missing local commands");
  test "closed branches reuse names with fresh IDs" (fun () ->
    let p = ok "(assume-push a true)(step b :rule r)(step-pop c :rule scope :premises (b))(assume-push a false)(step b :rule r)(step-pop d :rule scope :premises (b))" in
    let bs = List.filter (fun s -> s.name.text = "b") (steps p) in
    check "same spelling, fresh identity" ((List.nth bs 0).id <> (List.nth bs 1).id);
    check "reference resolves to current branch" ((List.hd (final_step p).premises).target = (List.nth bs 1).id));
  test "step fields retain permutation, premise multiplicity and claimed conclusion" (fun () ->
    let p = ok "(assume a true)(step b false :args (1) :premises (a a) :rule r)" in
    let s = final_step p in
    check "duplicate premises are not fields" (List.length s.premises = 2);
    check "claimed conclusion" (Option.fold ~none:false ~some:(is_name "false") s.conclusion));
  test "parsing does not validate rules, conclusion or refutation" (fun () ->
    let p = ok "(step p true :rule unknown_rule)(step q false :rule trust :args (false))" in
    check "unknown rule is retained for generated checker" ((List.hd (steps p)).rule.text = "unknown_rule");
    check "trust is retained, never skipped" ((final_step p).rule.text = "trust"));
  test "default include/reference denial" (fun () ->
    reject "directive rejected" "(include \"Cpc.eo\")";
    reject "directive rejected" "(reference \"problem.smt2\")");
  test "explicit directive policy retains every directive without filesystem reads" (fun () ->
    let checked = ref [] in
    let check_directive d = checked := d :: !checked; match d with
      | Include "pinned-Cpc.eo" | Reference "checked-input.smt2" -> Ok ()
      | _ -> Error "not pinned" in
    let p = ok ~check_directive "(include \"pinned-Cpc.eo\")(reference \"checked-input.smt2\")(assume a true)" in
    check "policy saw both" (List.length !checked = 2);
    check "directives retained" (match command_at p 0, command_at p 1 with
      | Directive (Include "pinned-Cpc.eo"), Directive (Reference "checked-input.smt2") -> true | _ -> false);
    ignore (bad ~check_directive "not pinned" "(include \"untrusted.eo\")"));
  let accepted_directive _ = Ok () in
  List.iter (fun (name, message, text) -> test name (fun () -> reject message text)) [
    "unknown command", "unsupported command", "(set-option :check false)";
    "no assert dropping", "unsupported command", "(assert false)";
    "unsupported push", "unsupported command", "(push 1)";
    "unsupported pop", "unsupported command", "(pop 1)";
    "unsupported datatype", "unsupported command", "(declare-datatype U ((c)))";
    "unsupported binder", "unsupported binder", "(assume p (forall ((x Int)) (= x x)))";
    "unsupported annotation", "unsupported binder", "(assume p (! true :named n))";
    "unexpected closing paren", "closing parenthesis", "(assume p true))";
    "unclosed list", "unclosed parenthesis", "(assume p true";
    "unclosed string", "unterminated string", "(assume p \"abc)";
    "unclosed quoted name", "unterminated quoted symbol", "(assume |p true)";
    "quoted symbol escape", "unsupported escape", "(assume |p\\q| true)";
    "adjacent string token", "missing delimiter", "(assume p \"a\"x)";
    "adjacent quoted token", "missing delimiter", "(assume p |a|x)";
    "sexp block comment rejected", "missing delimiter", "#| hidden |# (assume a true)";
    "sexp discard comment rejected", "malformed token", "#;(assume a false)(assume b true)";
    "keyword term", "keyword is not a term", "(assume p :foo)";
    "empty term", "empty list is not a term", "(assume p ())";
    "empty application", "empty application", "(assume p (f))";
    "malformed binary", "malformed token", "(assume p #b012)";
    "malformed hex", "malformed token", "(assume p #xz)";
    "malformed numeral", "malformed token", "(assume p 12x)";
    "zero rational denominator", "zero denominator", "(assume p 1/00)";
    "control byte", "malformed token", "(assume p \001)";
    "literal name", "expected symbol", "(assume 5 true)";
    "string name", "expected symbol", "(declare-const \"x\" Int)";
    "keyword name", "expected symbol", "(assume :p true)";
    "missing rule", "missing :rule", "(step p false :args ())";
    "literal rule", "expected symbol", "(step p :rule 1)";
    "duplicate rule", "duplicate step field", "(step p :rule r :rule s)";
    "duplicate args", "duplicate step field", "(step p :rule r :args () :args ())";
    "duplicate premises", "duplicate step field", "(step p :rule r :premises () :premises ())";
    "unknown field", "unsupported step field", "(step p :rule r :other ())";
    "missing field value", "missing its value", "(step p :rule)";
    "malformed args", "expected parenthesized list", "(step p :rule r :args x)";
    "malformed premise list", "expected parenthesized list", "(step p :rule r :premises x)";
    "premise expression", "expected symbol", "(step p :rule r :premises ((q)))";
    "malformed assumption", "malformed or unsupported", "(assume a true extra)";
    "declaration attribute", "unsupported declaration attributes", "(declare-const x Int :global)";
    "definition attribute", "malformed or unsupported", "(define t () true :type Bool)";
    "negative sort arity", "nonnegative sort arity", "(declare-sort U -1)";
    "huge sort arity", "integer range", "(declare-sort U 999999999999999999999999999999)";
    "duplicate declaration", "duplicate name", "(declare-const x Int)(declare-const x Bool)";
    "duplicate definition", "duplicate name", "(define t () true)(define t () false)";
    "duplicate proof ID", "duplicate name", "(assume p true)(step p :rule r)";
    "proof/term collision", "duplicate name", "(declare-const x Int)(assume x true)";
    "self premise", "not a visible proof premise", "(step p :rule r :premises (p))";
    "future premise", "unknown or future", "(step p :rule r :premises (q))(assume q true)";
    "dangling premise", "unknown or future", "(step p :rule r :premises (missing))";
    "term used as proof", "not a visible proof premise", "(declare-const x Bool)(step p :rule r :premises (x))";
    "expired assumption", "not a visible proof premise", "(assume-push a true)(step-pop b :rule scope :premises (a))(step c :rule r :premises (a))";
    "expired step", "not a visible proof premise", "(assume-push a true)(step b :rule r)(step-pop c :rule scope :premises (b))(step d :rule r :premises (b))";
    "unbalanced pop", "without matching", "(step-pop p :rule scope)";
    "unclosed scope", "unclosed assume-push", "(assume-push p true)";
    "global assumption in scope", "global assumptions must precede", "(assume-push p true)(assume q false)";
    "late global assumption", "global assumptions must precede", "(step p :rule r)(assume q false)";
    "recursive definition", "recursive definitions", "(define f ((x Int)) (f x))";
    "duplicate parameters", "duplicate definition parameter", "(define f ((x Int)(x Int)) x)";
    "parameter attribute", "expected typed parameter", "(define f ((x Int :list)) x)";
    "malformed let", "expected let binding", "(assume a (let ((x)) x))";
    "duplicate let names", "duplicate let binding", "(assume a (let ((x 1)(x 2)) x))";
    "empty let", "empty let binding", "(assume a (let () true))";
    "bare unsat", "exactly one parenthesized", "unsat";
    "unsat plus bare proof", "exactly one parenthesized", "unsat (assume p true) (step q :rule r)";
    "multiple solver responses", "exactly one parenthesized", "unsat () unsat ()";
    "sat response", "expected parenthesized list", "sat ()";
    "unknown response", "expected parenthesized list", "unknown ()";
    "solver error", "unsupported command", "(error \"bad input\")";
    "trailing token", "expected parenthesized list", "(assume p true) trailing";
    "trailing wrapped data", "unquoted command name", "((assume p true)) (assume q true)";
    "quoted command", "unquoted command name", "(|assume| p true)";
  ];
  List.iter (fun (name, message, text) -> test name (fun () ->
    ignore (bad ~check_directive:accepted_directive message text))) [
    "duplicate include", "duplicate include", "(include \"a\")(include \"a\")";
    "duplicate reference", "duplicate reference", "(reference \"a\")(reference \"b\")";
    "late include", "directives must precede", "(declare-const x Int)(include \"Cpc.eo\")";
    "late reference", "directives must precede", "(assume a true)(reference \"a\")";
    "reference normalization", "malformed or unsupported", "(reference \"a\" normalize)";
    "nonstring include", "expected string path", "(include Cpc.eo)";
    "include arity", "malformed or unsupported", "(include \"a\" \"b\")";
    "escaped include path", "escaped or control-bearing", {|(include "a\nb")|};
    "doubled quote path", "escaped or control-bearing", {|(include "a""b")|};
  ];
  List.iter (fun (name, before, after, message) -> test name (fun () ->
    reject message (replace_once uf before after))) [
    "mutated actual UF premise", ":premises (@p3)", ":premises (@p999)", "unknown or future";
    "mutated actual UF duplicate field", ":rule evaluate", ":rule evaluate :rule trust", "duplicate step field";
    "mutated actual UF duplicate ID", "(step @p2", "(step @p1", "duplicate name";
    "mutated actual UF unknown command", "(step @p2", "(skip @p2", "unsupported command";
    "mutated actual UF malformed args", ":args ((not true))", ":args (())", "empty list is not a term";
  ];
  test "mutated actual scoped LIA expired reference" (fun () ->
    reject "not a visible proof premise"
      (replace_once scoped_lia "(step-pop @p133 :rule scope :premises (@p132))"
         "(step-pop @p133 :rule scope :premises (@p80))"));
  test "exact diagnostic line/column and source" (fun () ->
    let text = "; comment\n(assume p true)\n(step q :rule r :premises (future))" in
    match parse_string ~source:"input.cpc" text with
    | Ok _ -> failwith "unexpected parse success"
    | Error d ->
        check "location" (d.source = "input.cpc" && d.span.start.line = 3 && d.span.start.column = 28);
        check "byte range" (String.sub text d.span.start.offset (d.span.stop.offset - d.span.start.offset) = "future");
        check "formatted diagnostic" (contains (Format.asprintf "%a" pp_diagnostic d) "input.cpc:3:28:"));
  test "comments at EOF and CRLF positions" (fun () ->
    let p = ok ";a\r\n(assume p true);EOF" in
    check "CRLF line" ((List.hd (assumes p)).name.loc.start.line = 2));
  test "input and command limits" (fun () ->
    ignore (bad ~limits:{ default_limits with max_bytes = 4 } "byte limit" "(assume p true)");
    ignore (bad ~limits:{ default_limits with max_commands = 1 } "command limit" "(assume p true)(step q :rule r)"));
  test "nesting and node limits" (fun () ->
    ignore (bad ~limits:{ default_limits with max_depth = 2 } "nesting limit" "(assume p (not (not true)))");
    ignore (bad ~limits:{ default_limits with max_nodes = 3 } "node limit" "(assume p true)");
    ignore (bad ~limits:{ default_limits with max_nodes = 0 } "must be positive" ""));
  test "file/channel APIs and channel size limit" (fun () ->
    (match parse_file "fixtures/uf4.cpc" with Ok p -> check "file" (List.length (steps p) = 15)
      | Error d -> failwith (Format.asprintf "%a" pp_diagnostic d));
    let channel = open_in_bin "fixtures/uf4.cpc" in
    Fun.protect ~finally:(fun () -> close_in_noerr channel) (fun () ->
      match parse_channel ~limits:{ default_limits with max_bytes = 100 } channel with
      | Error d -> check "channel bytes" (contains d.message "byte limit")
      | Ok _ -> failwith "missing channel limit");
    match parse_file "fixtures/does-not-exist.cpc" with
    | Error d -> check "file IO diagnostic" (contains d.message "input error")
    | Ok _ -> failwith "missing file error");
  test "policy callback errors propagate, never become successful parses" (fun () ->
    match parse_string ~check_directive:(fun _ -> failwith "policy unavailable") "(include \"a\")" with
    | exception Failure message -> check "policy exception" (message = "policy unavailable")
    | _ -> failwith "policy failure hidden");
  test "wide command stream remains bounded without OCaml stack growth" (fun () ->
    let commands = 100_000 in
    let b = Buffer.create (commands * 22) in
    for i = 1 to commands do
      Printf.bprintf b "(step p%d :rule r)\n" i
    done;
    let p = ok (Buffer.contents b) in
    check "all wide-stream commands retained" (List.length p.commands = commands));
  test "wide argument list retains order without stack growth" (fun () ->
    let n = 100_000 in
    let b = Buffer.create (n * 2) in
    Buffer.add_string b "(step p :rule r :args (";
    for i = 1 to n do Printf.bprintf b "%d " i done;
    Buffer.add_string b "))";
    let args = (final_step (ok (Buffer.contents b))).args in
    check "all wide args" (List.length args = n);
    check "first arg" ((List.hd args).view = Literal (Numeral "1"));
    check "last arg" ((List.hd (List.rev args)).view = Literal (Numeral (string_of_int n))));
  test "all incomplete actual UF response prefixes fail" (fun () ->
    let final_close = String.rindex uf ')' in
    for length = 1 to final_close do
      match parse_string (String.sub uf 0 length) with
      | Error _ -> ()
      | Ok _ -> failwith (Printf.sprintf "accepted incomplete response prefix of length %d" length)
    done);
  Printf.printf "CPC text frontend: %d regression cases passed (parsing only).\n%!" !count
