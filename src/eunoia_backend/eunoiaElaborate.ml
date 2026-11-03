module P = Eunoia_frontend.EunoiaProof
type term = Symbol of string | Apply of term * term
let app s = List.fold_left (fun f a -> Apply (f,a)) (Symbol s)
let spine t =
  let rec go xs = function Apply (f,a) -> go (a::xs) f | h -> h,xs in
  go [] t
let rec pp_term fmt t = match spine t with
  | Symbol s, [] -> Format.pp_print_string fmt s
  | h, xs -> Format.fprintf fmt "(%a%a)" pp_term h
      (fun fmt -> List.iter (fun x -> Format.fprintf fmt " %a" pp_term x)) xs

type declaration = { name : string; typ : term }
type step = {
  id : int; name : string; rule : string; arguments : term list;
  premises : int list; premise_terms : term list; result : term;
}
type trace = Done | Next of step * trace
  | Push of int * term * trace * step * trace
type proof = { roots : (int * term) list; steps : step list; trace : trace;
  capacity : int; conflict : int }
exception Error of string
let fail fmt = Format.kasprintf (fun s -> raise (Error s)) fmt
let builtins = ["Type"; "Bool"; "Int"; "true"; "false"; "->";
  "="; "not"; "and"; "or"; "xor"; "=>"; "ite"; "distinct";
  "+"; "-"; "*"; "<"; "<="; ">"; ">="]
let numeral s =
  let first = if String.length s > 0 && s.[0]='-' then 1 else 0 in
  String.length s > first &&
  let rec digits i = i=String.length s ||
    (s.[i]>='0' && s.[i]<='9' && digits (i+1)) in
  digits first

type value = Value of term | Macro of P.definition
let elaborate ?(max_expansion=1000000) ?(signature_names=[])
    ?(derive_assuming=(fun _ _ _ _ -> None))
    ~declarations ~roots ~derive (parsed:P.proof) =
  if max_expansion <= 0 then fail "Invalid elaboration expansion limit";
  let budget = ref max_expansion in
  let spend () = decr budget; if !budget < 0 then fail "CPC expansion limit exceeded" in
  let env = Hashtbl.create 100 and proofs = Hashtbl.create 100 in
  let remaining = ref declarations in
  let steps = ref [] and next = ref 0 in
  let started = ref false in
  let reserved s = List.mem s builtins || List.mem s signature_names ||
    List.exists (fun (d:declaration) -> d.name=s) declarations in
  let binder (s:P.symbol) =
    if reserved s.text || numeral s.text then fail "CPC binder shadows reserved name %s" s.text in
  let alloc () = let i = !next in incr next; i in
  (* cvc5 prints identical assertions once. Retain every authoritative root
     claim/slot, but match its source assumption to the first exact occurrence. *)
  let root_claims = List.map (fun t -> alloc (),t) roots in
  let seen_roots = Hashtbl.create (List.length roots) in
  let distinct_roots = List.filter (fun (_,t) ->
    if Hashtbl.mem seen_roots t then false
    else (Hashtbl.add seen_roots t (); true)) root_claims in
  let source_root_count = List.fold_left (fun n (c:P.command) ->
    match c.command with P.Assume _ -> n+1 | _ -> n) 0 parsed.commands in
  let expected_roots = ref (if source_root_count=List.length root_claims
    then root_claims else distinct_roots) in
  let rec term locals (t:P.term) =
    spend ();
    match t.view with
    | P.Name (s, Some id) ->
      (match List.assoc_opt id locals with
      | Some t -> t
      | None -> match Hashtbl.find_opt env id with
        | Some (Value t) -> t
        | Some (Macro d) when d.parameters = [] -> term locals d.body
        | Some (Macro _) -> fail "Unapplied CPC definition %s" s.text
        | None -> fail "Unbound CPC binding %s" s.text)
    | P.Name (s, None) ->
      if not s.quoted && (List.mem s.text builtins || List.mem s.text signature_names || numeral s.text)
      then Symbol s.text else fail "Unknown CPC symbol %s" s.text
    | P.Literal (P.Numeral s) -> Symbol s
    | P.Literal _ -> fail "Unsupported non-integer CPC literal"
    | P.Apply (h,args) ->
      let values = List.map (term locals) args in
      (match h.view with
      | P.Name (_, Some id) when not (List.mem_assoc id locals) ->
        (match Hashtbl.find_opt env id with
        | Some (Macro d) ->
          if List.length d.parameters <> List.length values then
            fail "CPC definition %s arity mismatch" d.name.text;
          let bound = List.map2 (fun (p:P.parameter) v -> p.binding,v) d.parameters values in
          term (bound @ locals) d.body
        | _ -> List.fold_left (fun f a -> spend (); Apply(f,a)) (term locals h) values)
      | _ -> List.fold_left (fun f a -> spend (); Apply(f,a)) (term locals h) values)
    | P.Let (bs, body) ->
      let vs = List.map (fun (b:P.let_binding) -> binder b.name; b.binding,term locals b.value) bs in
      term (vs @ locals) body in
  let read t = term [] t in
  let declare (d:P.declaration) =
    let typ = match d.kind with
      | P.Sort 0 -> Symbol "Type"
      | P.Sort _ -> fail "Parametric CPC sort unsupported"
      | P.Const t -> read t
      | P.Fun (args,ret) -> if args=[] then read ret
          else app "->" (List.map read args @ [read ret]) in
    let name = d.name.text in
    if List.mem name builtins || List.mem name signature_names || numeral name then
      fail "CPC declaration shadows signature name %s" name;
    (match List.find_opt (fun (x:declaration) -> x.name = name) !remaining with
    | Some x when x.typ = typ -> remaining := List.filter (fun (x:declaration) -> x.name <> name) !remaining
    | _ -> fail "CPC declaration %s differs from the exported tables" name);
    Hashtbl.add env d.binding (Value (Symbol name)) in
  let restore table saved = Hashtbl.clear table;
    Hashtbl.iter (Hashtbl.add table) saved in
  let step assuming (s:P.step) =
    started := true;
    if !expected_roots <> [] then fail "CPC steps precede exported roots";
    let arguments = List.map read s.args in
    let ps = List.map (fun (p:P.premise) -> match Hashtbl.find_opt proofs p.target with
      | Some v -> v | None -> fail "CPC premise %s unavailable" p.name.text) s.premises in
    let premise_terms = List.map snd ps in
    let generated = match assuming with
      | None -> derive s.rule.text arguments premise_terms
      | Some a ->
        if List.length ps <> 1 then fail "CPC discharge %s needs exactly one endpoint" s.name.text;
        derive_assuming s.rule.text a arguments premise_terms in
    let result = match generated with
      | Some t -> t
      | None -> fail "Generated CPC derivation rejected %s (%s)" s.name.text s.rule.text in
    (match s.conclusion with
    | Some t when read t <> result -> fail "CPC claimed result differs at %s" s.name.text
    | _ -> ());
    let st = {id=alloc (); name=s.name.text; rule=s.rule.text; arguments;
      premises=List.map fst ps; premise_terms; result} in
    steps := st::!steps; st in
  let rec commands closing = function
    | [] ->
      if closing <> None then fail "Unclosed CPC scope";
      Done, None, []
    | (command:P.command)::rest -> match command.command with
    | P.Declare d -> declare d; commands closing rest
    | P.Define d ->
      let name = d.name.text in
      if reserved name || String.length name <= 2 || String.sub name 0 2 <> "@t" ||
         not (String.for_all (fun c -> c>='0' && c<='9')
           (String.sub name 2 (String.length name-2))) then
        fail "CPC definition %s is outside the private @t<digits> alias namespace" name;
      (* Eagerly inspect unused definitions, including binder sorts and names. *)
      let locals = List.map (fun (p:P.parameter) ->
        binder p.name; ignore (read p.sort); p.binding,Symbol p.name.text) d.parameters in
      ignore (term locals d.body); Hashtbl.add env d.binding (Macro d);
      commands closing rest
    | P.Assume a ->
      if !started || closing <> None then fail "CPC root assumption appears after a proof step/scope";
      let t = read a.formula in
      let id = match !expected_roots with
      | (id,x)::xs when x=t -> expected_roots := xs; id
      | _ -> fail "CPC root %s differs from exported root order/content" a.name.text in
      Hashtbl.add proofs a.id (id,t);
      commands closing rest
    | P.Step s ->
      let st = step None s in
      Hashtbl.add proofs s.id (st.id,st.result);
      let tail,d,rest = commands closing rest in Next(st,tail),d,rest
    | P.Assume_push (scope,a) ->
      started := true;
      if !expected_roots <> [] then fail "CPC scope precedes exported roots";
      let pushed = read a.formula and slot = alloc () in
      let saved_env = Hashtbl.copy env and saved_proofs = Hashtbl.copy proofs in
      Hashtbl.add proofs a.id (slot,pushed);
      let body,discharge,rest = commands (Some (scope,pushed)) rest in
      let source,st = match discharge with Some d -> d | None -> fail "Missing CPC discharge" in
      restore env saved_env; restore proofs saved_proofs;
      Hashtbl.add proofs source (st.id,st.result);
      let tail,d,rest = commands closing rest in
      Push(slot,pushed,body,st,tail),d,rest
    | P.Step_pop (scope,s) ->
      (match closing with
      | Some (expected,a) when scope=expected ->
        let st = step (Some a) s in Done,Some(s.id,st),rest
      | _ -> fail "Unmatched CPC discharge %s" s.name.text)
    | P.Directive _ -> fail "CPC directives unsupported by this backend" in
  let trace,_,_ = commands None parsed.commands in
  if !remaining <> [] then fail "CPC omitted exported declarations";
  if !expected_roots <> [] then fail "CPC omitted exported root assumptions";
  (* A local conflict cannot serve as a parent conflict. All commands still ran. *)
  let live = Hashtbl.create !next in
  Hashtbl.iter (fun _ (slot,_) -> Hashtbl.replace live slot ()) proofs;
  let final = List.find_opt (fun st -> Hashtbl.mem live st.id) !steps in
  match final with
  | Some {id;result=Symbol "false";_} ->
    {roots=root_claims; steps=List.rev !steps; trace; capacity= !next; conflict=id}
  | _ -> fail "CPC final step is not a derived false"
