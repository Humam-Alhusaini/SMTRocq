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

(* Untrusted text frontend. No inference, rule evaluation or proof acceptance. *)
type position = { offset : int; line : int; column : int }
type span = { start : position; stop : position }
type diagnostic = { source : string; span : span; message : string }
let pp_diagnostic fmt d =
  Format.fprintf fmt "%s:%d:%d: %s" d.source d.span.start.line
    d.span.start.column d.message

type symbol = { text : string; quoted : bool; loc : span }
type literal = Numeral of string | Decimal of string | Rational of string
             | Binary of string | Hexadecimal of string | String of string
type binding_id = int
type proof_id = int
type scope_id = int
type term = { loc : span; view : term_view }
and term_view = Name of symbol * binding_id option | Literal of literal
              | Apply of term * term list | Let of let_binding list * term
and let_binding = { binding : binding_id; name : symbol; value : term }
type parameter = { binding : binding_id; name : symbol; sort : term }
type declaration_kind = Sort of int | Const of term | Fun of term list * term
type declaration = {
  binding : binding_id; name : symbol; scope : scope_id option;
  kind : declaration_kind;
}
type definition = {
  binding : binding_id; name : symbol; scope : scope_id option;
  parameters : parameter list; body : term;
}
type assumption = {
  id : proof_id; name : symbol; scope : scope_id option; formula : term;
}
type premise = { name : symbol; target : proof_id }
type step = {
  id : proof_id; name : symbol; scope : scope_id option; rule : symbol;
  args : term list; premises : premise list; conclusion : term option;
}
type directive = Include of string | Reference of string
type command_view = Declare of declaration | Define of definition
                  | Assume of assumption | Assume_push of scope_id * assumption
                  | Step of step | Step_pop of scope_id * step
                  | Directive of directive
type command = { loc : span; command : command_view }
type envelope = Bare | Parenthesized | Unsat_parenthesized
type proof = { envelope : envelope; commands : command list }
type limits = {
  max_bytes : int; max_depth : int; max_nodes : int; max_commands : int;
}
let default_limits = {
  max_bytes = 64 * 1024 * 1024; max_depth = 512;
  max_nodes = 2_000_000; max_commands = 1_000_000;
}
type directive_check = directive -> (unit, string) result

exception Parse_error of diagnostic
let origin = { offset = 0; line = 1; column = 1 }
let initial_span = { start = origin; stop = origin }
let fail source span message = raise (Parse_error { source; span; message })
let check_limits source limits =
  if limits.max_bytes <= 0 || limits.max_depth <= 0 || limits.max_nodes <= 0
     || limits.max_commands <= 0 then
    fail source initial_span "reader limits must be positive"

(* Separate token classes prevent strings/keywords from becoming names. *)
type atom = Sym of string * bool | Lit of literal | Keyword of string
type sexp = { at : span; sexp : sexp_view }
and sexp_view = Atom of atom | List of sexp list

type lexer = {
  input : string; source : string; limits : limits;
  mutable offset : int; mutable line : int; mutable column : int;
  mutable nodes : int;
}
let position l = { offset = l.offset; line = l.line; column = l.column }
let peek l = if l.offset < String.length l.input then Some l.input.[l.offset] else None
let advance l =
  let c = l.input.[l.offset] in
  l.offset <- l.offset + 1;
  if c = '\n' then (l.line <- l.line + 1; l.column <- 1)
  else l.column <- l.column + 1
let whitespace = function ' ' | '\t' | '\r' | '\n' -> true | _ -> false
let rec skip l =
  match peek l with
  | Some c when whitespace c -> advance l; skip l
  | Some ';' ->
      while (match peek l with Some c when c <> '\n' -> true | _ -> false) do
        advance l
      done;
      skip l
  | _ -> ()
let delimiter = function '(' | ')' | ';' | '"' | '|' -> true | c -> whitespace c
let range c a b = c >= a && c <= b
let digit c = range c '0' '9'
let hex c = digit c || range c 'a' 'f' || range c 'A' 'F'
let symbol_start c =
  range c 'a' 'z' || range c 'A' 'Z'
  || String.contains "~!@$%^&*_-+=<>.?/" c
let symbol_char c = symbol_start c || digit c
let all_from pred s start =
  let rec go i = i = String.length s || (pred s.[i] && go (i + 1)) in
  start < String.length s && go start
let classify l at s =
  let bad () = fail l.source at ("unsupported or malformed token " ^ s) in
  let length = String.length s in
  let signed_start = if s.[0] = '-' then 1 else 0 in
  let numeric_part sep make =
    match String.split_on_char sep s with
    | [a; b] ->
        let start = if String.length a > 0 && a.[0] = '-' then 1 else 0 in
        if all_from digit a start && all_from digit b 0 then Some (make b)
        else None
    | _ -> None
  in
  if s.[0] = ':' then
    if length > 1 && all_from symbol_char s 1 then Keyword s else bad ()
  else if s.[0] = '#' then
    if length > 2 && s.[1] = 'b'
       && all_from (fun c -> c = '0' || c = '1') s 2 then Lit (Binary s)
    else if length > 2 && s.[1] = 'x' && all_from hex s 2 then Lit (Hexadecimal s)
    else bad ()
  else if all_from digit s signed_start then Lit (Numeral s)
  else match numeric_part '.' (fun _ -> Decimal s) with
    | Some v -> Lit v
    | None -> match numeric_part '/' (fun denominator ->
        if all_from (fun c -> c = '0') denominator 0 then
          fail l.source at "zero denominator in rational literal";
        Rational s) with
      | Some v -> Lit v
      | None ->
          if symbol_start s.[0] && all_from symbol_char s 0 then Sym (s, false)
          else bad ()

let read_atom l start =
  let at () = { start; stop = position l } in
  let separated () =
    match peek l with
    | Some c when not (whitespace c || c = '(' || c = ')' || c = ';') ->
        fail l.source (at ()) "missing delimiter after quoted token"
    | _ -> ()
  in
  match peek l with
  | Some '"' ->
      advance l;
      let body_start = l.offset in
      let rec scan () =
        match peek l with
        | None -> fail l.source (at ()) "unterminated string literal"
        | Some '"' ->
            let body_end = l.offset in
            advance l;
            if peek l = Some '"' then (advance l; scan ()) else body_end
        | Some c when Char.code c < 32 && not (whitespace c) ->
            fail l.source (at ()) "unsupported control byte in string"
        | Some '\127' -> fail l.source (at ()) "unsupported control byte in string"
        | Some _ -> advance l; scan ()
      in
      let body_end = scan () in
      separated ();
      Lit (String (String.sub l.input body_start (body_end - body_start)))
  | Some '|' ->
      advance l;
      let body_start = l.offset in
      while (match peek l with Some c when c <> '|' ->
        if c = '\\' || Char.code c < 32 || c = '\127' then
          fail l.source (at ()) "unsupported escape or control byte in quoted symbol";
        advance l; true | _ -> false) do () done;
      let body_end = l.offset in
      if peek l = None then fail l.source (at ()) "unterminated quoted symbol";
      advance l;
      separated ();
      Sym (String.sub l.input body_start (body_end - body_start), true)
  | _ ->
      let body_start = l.offset in
      while (match peek l with Some c when not (delimiter c) -> advance l; true
           | _ -> false) do () done;
      if body_start = l.offset then fail l.source (at ()) "expected atom";
      let s = String.sub l.input body_start (l.offset - body_start) in
      separated ();
      classify l (at ()) s

let rec read_sexp l depth =
  skip l;
  let start = position l in
  let at () = { start; stop = position l } in
  if depth > l.limits.max_depth then fail l.source (at ()) "nesting limit exceeded";
  l.nodes <- l.nodes + 1;
  if l.nodes > l.limits.max_nodes then fail l.source (at ()) "syntax node limit exceeded";
  let sexp = match peek l with
    | None -> fail l.source (at ()) "unexpected end of input"
    | Some ')' -> fail l.source (at ()) "unexpected closing parenthesis"
    | Some '(' ->
        advance l;
        let rec contents acc =
          skip l;
          match peek l with
          | None -> fail l.source (at ()) "unclosed parenthesis"
          | Some ')' -> advance l; List (List.rev acc)
          | _ -> let item = read_sexp l (depth + 1) in contents (item :: acc)
        in contents []
    | _ -> Atom (read_atom l start)
  in { at = at (); sexp }

(* Avoid stack growth on wide terms and large command streams in OCaml 4.14. *)
let map f xs = List.rev (List.rev_map f xs)

module Names = Map.Make (String)
module Seen = Set.Make (String)
type frame = {
  scope_id : scope_id; opened_at : span;
  terms_before : binding_id Names.t; proofs_before : proof_id Names.t;
}
type state = {
  source : string;
  check_directive : directive_check;
  mutable next_id : int;
  mutable terms : binding_id Names.t;
  mutable proofs : proof_id Names.t;
  mutable seen : span Names.t;
  mutable frames : frame list;
  mutable started_proof : bool;
  mutable started_body : bool;
  mutable includes : Seen.t;
  mutable referenced : bool;
}
let fresh s = let id = s.next_id in s.next_id <- id + 1; id
let error s x message = fail s.source x.at message
let symbol s x = match x.sexp with
  | Atom (Sym (text, quoted)) -> { text; quoted; loc = x.at }
  | _ -> error s x "expected symbol (not a literal, keyword or list)"
let list s x = match x.sexp with List xs -> xs | _ -> error s x "expected parenthesized list"
let plain x text = match x.sexp with Atom (Sym (s, false)) -> s = text | _ -> false
let keyword x = match x.sexp with Atom (Keyword _) -> true | _ -> false
let scope s = match s.frames with [] -> None | f :: _ -> Some f.scope_id
let reserve s name =
  let previous = if Names.mem name.text s.terms || Names.mem name.text s.proofs
    then Names.find_opt name.text s.seen else None in
  match previous with
  | Some first -> fail s.source name.loc
      (Printf.sprintf "duplicate name %s (first introduced at %d:%d)"
         name.text first.start.line first.start.column)
  | None -> s.seen <- Names.add name.text name.loc s.seen

(* The binder grammar is deliberately small. Operator applications themselves
   remain uninterpreted and must be elaborated against the generated signature. *)
let rec term s env x =
  let view = match x.sexp with
    | Atom (Sym _) -> let name = symbol s x in Name (name, Names.find_opt name.text env)
    | Atom (Lit literal) -> Literal literal
    | Atom (Keyword _) -> error s x "keyword is not a term"
    | List [] -> error s x "empty list is not a term"
    | List (head :: rest) when plain head "let" ->
        (match rest with
        | [bindings; body] ->
            let bindings = list s bindings in
            if bindings = [] then error s x "empty let binding list is unsupported";
            let seen = ref Seen.empty in
            let bindings = map (fun b -> match list s b with
              | [name; value] ->
                  let name = symbol s name in
                  if Seen.mem name.text !seen then fail s.source name.loc "duplicate let binding";
                  seen := Seen.add name.text !seen;
                  let value = term s env value in
                  { binding = fresh s; name; value }
              | _ -> error s b "expected let binding (name value)") bindings in
            let body_env = List.fold_left (fun env (b : let_binding) ->
              Names.add b.name.text b.binding env) env bindings in
            Let (bindings, term s body_env body)
        | _ -> error s x "expected (let ((name value) ...) body)")
    | List (head :: _) when List.exists (plain head)
        ["forall"; "exists"; "lambda"; "match"; "par"; "!"] ->
        error s x "unsupported binder or annotated term"
    | List (head :: args) ->
        if args = [] then error s x "empty application is unsupported";
        let head = term s env head in
        let args = map (term s env) args in
        Apply (head, args)
  in { loc = x.at; view }

let parameters s env x =
  let seen = ref Seen.empty in
  (* Parameters are sequential typed binders; the body sees all of them. *)
  List.fold_left (fun (rev, env) p -> match list s p with
    | [name; ty] ->
        let name = symbol s name in
        if Seen.mem name.text !seen then fail s.source name.loc "duplicate definition parameter";
        seen := Seen.add name.text !seen;
        let sort = term s env ty in
        let binding = fresh s in
        ({ binding; name; sort } :: rev, Names.add name.text binding env)
    | _ -> error s p "expected typed parameter (name sort)") ([], env) (list s x)
  |> fun (rev, env) -> List.rev rev, env

let premise s x =
  let name = symbol s x in
  match Names.find_opt name.text s.proofs with
  | Some target -> { name; target }
  | None ->
      let reason = if Names.mem name.text s.seen then "not a visible proof premise"
        else "unknown or future proof premise" in
      fail s.source name.loc (reason ^ ": " ^ name.text)

let step_fields s ctx rest =
  let conclusion, fields = match rest with
    | c :: rest when not (keyword c) -> Some (term s s.terms c), rest
    | _ -> None, rest
  in
  let rule = ref None and args = ref [] and premises = ref [] in
  let seen = ref Seen.empty in
  let rec fields_loop = function
    | [] -> ()
    | field :: value :: rest ->
        let key = match field.sexp with
          | Atom (Keyword k) -> k
          | _ -> error s field "expected step field keyword"
        in
        if Seen.mem key !seen then error s field ("duplicate step field " ^ key);
        seen := Seen.add key !seen;
        (match key with
        | ":rule" -> rule := Some (symbol s value)
        | ":args" -> args := map (term s s.terms) (list s value)
        | ":premises" -> premises := map (premise s) (list s value)
        | _ -> error s field ("unsupported step field " ^ key));
        fields_loop rest
    | [field] -> error s field "step field is missing its value"
  in
  fields_loop fields;
  let rule = match !rule with Some r -> r | None -> error s ctx "missing :rule field" in
  rule, !args, !premises, conclusion

let parse_command s x =
  let fields = list s x in
  let command = match fields with
    | head :: rest ->
        let head = match head.sexp with Atom (Sym (name, false)) -> name
          | _ -> error s head "expected unquoted command name" in
        (match head, rest with
        | "declare-sort", [name; arity] ->
            s.started_body <- true;
            let name = symbol s name in
            let arity = match arity.sexp with
              | Atom (Lit (Numeral n)) when n.[0] <> '-' ->
                  (match int_of_string_opt n with Some n -> n
                  | None -> error s arity "sort arity exceeds reader integer range")
              | _ -> error s arity "expected nonnegative sort arity"
            in
            reserve s name;
            let binding = fresh s in
            s.terms <- Names.add name.text binding s.terms;
            Declare { binding; name; scope = scope s; kind = Sort arity }
        | ("declare-const" | "declare-fun"), name :: rest ->
            s.started_body <- true;
            let name = symbol s name in
            let kind = match head, rest with
              | "declare-const", [ty] -> Const (term s s.terms ty)
              | "declare-fun", [args; ty] ->
                  let args = map (term s s.terms) (list s args) in
                  Fun (args, term s s.terms ty)
              | _ -> error s x "malformed declaration or unsupported declaration attributes"
            in
            reserve s name;
            let binding = fresh s in
            s.terms <- Names.add name.text binding s.terms;
            Declare { binding; name; scope = scope s; kind }
        | "define", [name; params; body] ->
            s.started_body <- true;
            let name = symbol s name in
            reserve s name;
            let parameters, env = parameters s s.terms params in
            let body = term s env body in
            let rec recursive t = match t.view with
              | Name (n, None) -> n.text = name.text
              | Name (_, Some _) | Literal _ -> false
              | Apply (f, args) -> recursive f || List.exists recursive args
              | Let (bs, t) -> List.exists (fun (b : let_binding) -> recursive b.value) bs || recursive t
            in
            if recursive body then error s x "recursive definitions are unsupported";
            let binding = fresh s in
            s.terms <- Names.add name.text binding s.terms;
            Define { binding; name; scope = scope s; parameters; body }
        | ("assume" | "assume-push"), [name; formula] ->
            s.started_body <- true;
            if head = "assume" && (s.started_proof || s.frames <> []) then
              error s x "global assumptions must precede proof steps and scopes";
            let name = symbol s name in
            let formula = term s s.terms formula in
            reserve s name;
            let id = fresh s in
            let pushed = if head = "assume-push" then (
              s.started_proof <- true;
              let scope_id = fresh s in
              s.frames <- { scope_id; opened_at = x.at; terms_before = s.terms;
                proofs_before = s.proofs } :: s.frames;
              Some scope_id) else None in
            s.proofs <- Names.add name.text id s.proofs;
            let a = { id; name; scope = scope s; formula } in
            (match pushed with None -> Assume a | Some scope -> Assume_push (scope, a))
        | ("step" | "step-pop"), name :: rest ->
            s.started_body <- true;
            s.started_proof <- true;
            let name = symbol s name in
            reserve s name;
            let rule, args, premises, conclusion = step_fields s x rest in
            let closed = if head = "step-pop" then match s.frames with
              | [] -> error s x "step-pop without matching assume-push"
              | f :: rest ->
                  s.frames <- rest;
                  s.terms <- f.terms_before;
                  s.proofs <- f.proofs_before;
                  Some f.scope_id
              else None in
            let id = fresh s in
            s.proofs <- Names.add name.text id s.proofs;
            let step = { id; name; scope = scope s; rule; args; premises; conclusion } in
            (match closed with None -> Step step | Some scope -> Step_pop (scope, step))
        | ("include" | "reference"), [path] ->
            if s.started_body || s.frames <> [] then
              error s x "directives must precede declarations, assumptions and steps";
            let path = match path.sexp with
              | Atom (Lit (String path)) ->
                  if path = "" || String.contains path '\\' || String.contains path '"'
                     || String.exists (fun c -> Char.code c < 32 || c = '\127') path then
                    error s x "empty, escaped or control-bearing directive path is unsupported";
                  path
              | _ -> error s path "expected string path in directive"
            in
            if head = "include" && Seen.mem path s.includes then error s x "duplicate include";
            if head = "reference" && s.referenced then error s x "duplicate reference";
            let directive = if head = "include" then Include path else Reference path in
            (match s.check_directive directive with
            | Error message -> error s x ("directive rejected: " ^ message)
            | Ok () -> ());
            if head = "include" then s.includes <- Seen.add path s.includes
            else s.referenced <- true;
            Directive directive
        | ("declare-sort" | "declare-const" | "declare-fun" | "define"
          | "assume" | "assume-push" | "step" | "step-pop" | "include" | "reference"), _ ->
            error s x ("malformed or unsupported " ^ head ^ " command")
        | _ -> error s x ("unsupported command " ^ head))
    | [] -> error s x "empty command"
  in { loc = x.at; command }

let reject_directive _ = Error "no explicit checked directive policy supplied"
let parse_string ?(source = "<string>") ?(limits = default_limits)
    ?(check_directive = reject_directive) input =
  try
    check_limits source limits;
    if String.length input > limits.max_bytes then fail source initial_span "input byte limit exceeded";
    let l = { input; source; limits; offset = 0; line = 1; column = 1; nodes = 0 } in
    let rec read_all acc =
      skip l;
      match peek l with None -> List.rev acc
      | _ -> let x = read_sexp l 1 in read_all (x :: acc)
    in
    let sexps = read_all [] in
    let envelope, sexps = match sexps with
      | [status; { sexp = List commands; _ }] when plain status "unsat" ->
          Unsat_parenthesized, commands
      | status :: _ when plain status "unsat" ->
          fail source status.at "unsat must be followed by exactly one parenthesized proof"
      | [{ sexp = List (({ sexp = List _; _ } :: _) as commands); _ }] ->
          Parenthesized, commands
      | [{ sexp = List []; _ }] -> Parenthesized, []
      | commands -> Bare, commands
    in
    let s = { source; check_directive; next_id = 0; terms = Names.empty;
      proofs = Names.empty; seen = Names.empty; frames = []; started_proof = false;
      started_body = false; includes = Seen.empty; referenced = false } in
    let count = ref 0 in
    let commands = map (fun x ->
      incr count;
      if !count > limits.max_commands then error s x "command limit exceeded";
      parse_command s x) sexps in
    (match s.frames with [] -> ()
    | frame :: _ -> fail source frame.opened_at "unclosed assume-push scope");
    Ok { envelope; commands }
  with Parse_error d -> Error d

let parse_channel ?(source = "<channel>") ?(limits = default_limits)
    ?check_directive channel =
  let contents = try
    check_limits source limits;
    let b = Buffer.create 4096 and chunk = Bytes.create 4096 in
    let rec read () =
      let n = input channel chunk 0 (Bytes.length chunk) in
      if n > 0 then (
        if n > limits.max_bytes - Buffer.length b then
          fail source initial_span "input byte limit exceeded";
        Buffer.add_subbytes b chunk 0 n;
        read ())
    in
    read ();
    Ok (Buffer.contents b)
  with
  | Parse_error d -> Error d
  | Sys_error message -> Error { source; span = initial_span; message = "input error: " ^ message }
  in
  match contents with
  | Error d -> Error d
  | Ok input -> parse_string ~source ~limits ?check_directive input

let parse_file ?(limits = default_limits) ?check_directive path =
  match (try Ok (open_in_bin path) with Sys_error message ->
    Error { source = path; span = initial_span; message = "input error: " ^ message }) with
  | Error d -> Error d
  | Ok channel ->
      Fun.protect ~finally:(fun () -> close_in_noerr channel)
        (fun () -> parse_channel ~source:path ~limits ?check_directive channel)
