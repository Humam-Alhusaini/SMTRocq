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
type proof = { roots : (int * term) list; steps : step list; capacity : int; conflict : int }
exception Error of string
let fail fmt = Format.kasprintf (fun s -> raise (Error s)) fmt
let builtins = ["Type"; "Bool"; "Int"; "true"; "false"; "->";
  "="; "not"; "and"; "or"; "xor"; "=>"; "ite"; "distinct";
  "+"; "-"; "*"; "<"; "<="; ">"; ">="]
let numeral s = String.length s > 0 &&
  String.for_all (fun c -> c >= '0' && c <= '9') s

type value = Value of term | Macro of P.definition
let elaborate ?(max_expansion=1000000) ~declarations ~roots ~derive (parsed:P.proof) =
  if max_expansion <= 0 then fail "Invalid elaboration expansion limit";
  let budget = ref max_expansion in
  let spend () = decr budget; if !budget < 0 then fail "CPC expansion limit exceeded" in
  let env = Hashtbl.create 100 and proofs = Hashtbl.create 100 in
  let remaining = ref declarations and expected_roots = ref roots in
  let root_acc = ref [] and steps = ref [] and next = ref 0 in
  let alloc () = let i = !next in incr next; i in
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
      if (not s.quoted && List.mem s.text builtins) || numeral s.text
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
      let vs = List.map (fun (b:P.let_binding) -> b.binding,term locals b.value) bs in
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
    (match List.find_opt (fun (x:declaration) -> x.name = name) !remaining with
    | Some x when x.typ = typ -> remaining := List.filter (fun (x:declaration) -> x.name <> name) !remaining
    | _ -> fail "CPC declaration %s differs from the exported tables" name);
    Hashtbl.add env d.binding (Value (Symbol name)) in
  List.iter (fun (command:P.command) -> match command.command with
    | P.Declare d -> declare d
    | P.Define d ->
      (* Eagerly inspect unused definitions too, with symbolic formal binders. *)
      let locals = List.map (fun (p:P.parameter) ->
        ignore (read p.sort); p.binding,Symbol p.name.text) d.parameters in
      ignore (term locals d.body); Hashtbl.add env d.binding (Macro d)
    | P.Assume a ->
      if !steps <> [] then fail "CPC root assumption appears after a proof step";
      let t = read a.formula in
      (match !expected_roots with
      | x::xs when x=t -> expected_roots := xs
      | _ -> fail "CPC root %s differs from exported root order/content" a.name.text);
      let id = alloc () in
      root_acc := (id,t)::!root_acc; Hashtbl.add proofs a.id (id,t)
    | P.Step s ->
      if !expected_roots <> [] then fail "CPC steps precede exported roots";
      let arguments = List.map read s.args in
      let ps = List.map (fun (p:P.premise) -> match Hashtbl.find_opt proofs p.target with
        | Some v -> v | None -> fail "CPC premise %s unavailable" p.name.text) s.premises in
      let premise_terms = List.map snd ps in
      let result = match derive s.rule.text arguments premise_terms with
        | Some t -> t
        | None -> fail "Generated CPC derivation rejected %s (%s)" s.name.text s.rule.text in
      (match s.conclusion with
      | Some t when read t <> result -> fail "CPC claimed result differs at %s" s.name.text
      | _ -> ());
      let id = alloc () in
      let st = {id; name=s.name.text; rule=s.rule.text; arguments;
        premises=List.map fst ps; premise_terms; result} in
      steps := st::!steps; Hashtbl.add proofs s.id (id,result)
    | P.Assume_push _ | P.Step_pop _ -> fail "CPC scopes require the proved scoped checker"
    | P.Directive _ -> fail "CPC directives unsupported by this backend") parsed.commands;
  if !remaining <> [] then fail "CPC omitted exported declarations";
  if !expected_roots <> [] then fail "CPC omitted exported root assumptions";
  match !steps with
  | {id;result=Symbol "false";_}::_ ->
    {roots=List.rev !root_acc; steps=List.rev !steps; capacity= !next; conflict=id}
  | _ -> fail "CPC final step is not a derived false"
