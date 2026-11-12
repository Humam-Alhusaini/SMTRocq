(* Untrusted helper-cache hints. The Rocq validator recomputes every selected
   entry under the exact source query and fuel before using any of them. *)
open Common
module C = EunoiaRocq
module R = RocqInterface
module E = EunoiaElaborate
let api name = "SMTCoq.checker.eunoia.EoCheckedMemo.EoCheckedMemo." ^ name
let rec decode_nat value =
  match R.decompose_app_list value with
  | h,[] when R.eq_constr h (C.global "Corelib.Init.Datatypes.O") -> 0
  | h,[n] when R.eq_constr h (C.global "Corelib.Init.Datatypes.S") -> 1 + decode_nat n
  | _ -> R.raise_error "Eunoia: malformed helper-cache depth"
let decode_entry value = match R.decompose_app_list value with
  | h,[depth;name;args;result] when R.eq_constr h (C.global (api "Entry")) ->
    decode_nat depth,C.decode_string name,C.decode_list C.decode_term args,C.decode_term result
  | _ -> R.raise_error "Eunoia: malformed helper-cache entry"
let rec size = function E.Symbol _ -> 1 | E.Apply (a,b) -> 1 + size a + size b
let create env fuel query =
  if Sys.getenv_opt "EUNOIA_HELPER_CACHE" <> Some "1" then
    (fun _ _ _ compute -> compute ()),(fun _ -> [])
  else
  let observed = Hashtbl.create 127 and collected = Hashtbl.create 127 in
  let derive rule args premises _compute = begin
    let key = rule,args,premises in
    let previous = if Sys.getenv_opt "EUNOIA_DISABLE_DERIVE_CACHE" = Some "1" then None
      else Hashtbl.find_opt collected key in
    let result,entries = match previous with
      | Some pair -> pair
      | None ->
        let option_ty = SmtMisc.mklApp CoqTerms.coption [|C.term_type ()|] in
        let list_ty = SmtMisc.mklApp CoqTerms.clist [|C.global (api "cache_entry")|] in
        let ty = SmtMisc.mklApp CoqTerms.cprod [|option_ty;list_ty|] in
        let tm = C.call "SMTCoq.checker.eunoia.CpcMemoCollector.derive_context_logged"
          [C.global "SMTCoq.checker.eunoia.CpcGenerated.default_primitive";fuel;query;
           C.string rule;SmtMisc.mklApp CoqTerms.cNone [|C.term_type ()|];
           C.term_list args;C.term_list premises] in
        let result,entries = match R.decompose_app_list (R.cbv_vm env tm ty) with
          | h,[_;_;value;entries] when R.eq_constr h (Lazy.force CoqTerms.cpair) ->
            let result = match R.decompose_app_list value with
              | h,[_;t] when R.eq_constr h (Lazy.force CoqTerms.cSome) -> Some (C.decode_term t)
              | h,[_] when R.eq_constr h (Lazy.force CoqTerms.cNone) -> None
              | _ -> R.raise_error "Eunoia: malformed collected candidate" in
            result,C.decode_list decode_entry entries
          | _ -> R.raise_error "Eunoia: malformed helper collection" in
        if Sys.getenv_opt "EUNOIA_DISABLE_DERIVE_CACHE" <> Some "1" &&
           Hashtbl.length collected < 4096 then Hashtbl.add collected key (result,entries);
        result,entries in
    List.iter (fun (depth,name,args,value) ->
      let key = depth,name,args in
      match Hashtbl.find_opt observed key with
      | Some (count,old) -> Hashtbl.replace observed key (count+1,old)
      | None -> if Hashtbl.length observed < 4096 then Hashtbl.add observed key (1,value)) entries;
    result
  end in
  let finish encode =
    let selected = Hashtbl.fold (fun (depth,name,args) (count,value) selected ->
      let weight = List.fold_left (fun n t -> n + size t) 0 args in
      if count >= 2 && weight >= 4 then (count * weight,depth,name,args,value)::selected else selected)
      observed []
      |> List.sort (fun (wa,da,na,aa,_) (wb,db,nb,ab,_) ->
        let c = Int.compare wb wa in if c<>0 then c else Stdlib.compare (da,na,aa) (db,nb,ab)) in
    let rec take n = function [] -> [] | _ when n=0 -> [] | x::xs -> x::take (n-1) xs in
    (* Children have strictly greater depth, so tail-first validation can use
       them when checking a parent. Selection does not establish validity. *)
    take 128 selected
    |> List.sort (fun (_,da,na,aa,_) (_,db,nb,ab,_) -> Stdlib.compare (da,na,aa) (db,nb,ab))
    |> List.map (fun (_,depth,name,args,value) -> C.call (api "Entry")
      [CoqTerms.mkNat depth;C.string name;C.list (C.term_type ()) (List.map encode args);encode value]) in
  derive,finish
