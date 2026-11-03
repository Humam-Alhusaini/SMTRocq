open Common
module R = RocqInterface
let global name =
  let reference = try Nametab.locate (Libnames.qualid_of_string name)
    with Not_found -> R.raise_error "Eunoia: required Rocq constant not loaded: %s" name in
  UnivGen.constr_of_monomorphic_global (Global.env ()) reference
let call name args = R.mkApp (global name,Array.of_list args)
let list ty xs = List.fold_right (fun x tail ->
  SmtMisc.mklApp CoqTerms.ccons [|ty;x;tail|]) xs
  (SmtMisc.mklApp CoqTerms.cnil [|ty|])
let string s =
  let chars = ref (global "Stdlib.Strings.String.EmptyString") in
  for i = String.length s - 1 downto 0 do
    let n = Char.code s.[i] in
    let bits = Array.init 8 (fun b -> Lazy.force
      (if n land (1 lsl b) <> 0 then CoqTerms.ctrue else CoqTerms.cfalse)) in
    let c = R.mkApp (global "Stdlib.Strings.Ascii.Ascii",bits) in
    chars := call "Stdlib.Strings.String.String" [c;!chars]
  done; !chars
let syntax = "SMTCoq.checker.eunoia.EoSyntax."
let term_type () = global (syntax ^ "term")
let rec term = function
  | EunoiaElaborate.Symbol s -> call (syntax ^ "Symbol") [string s]
  | EunoiaElaborate.Apply(f,a) -> call (syntax ^ "Apply") [term f;term a]
let term_list xs = list (term_type ()) (List.map term xs)
let decode_string t =
  let buf = Buffer.create 32 in
  let rec go t = match R.decompose_app_list t with
    | h,[] when R.eq_constr h (global "Stdlib.Strings.String.EmptyString") -> Buffer.contents buf
    | h,[c;tail] when R.eq_constr h (global "Stdlib.Strings.String.String") ->
      (match R.decompose_app_list c with
      | h,bits when R.eq_constr h (global "Stdlib.Strings.Ascii.Ascii") && List.length bits=8 ->
        let n = List.fold_left (fun (i,n) b ->
          let bit = if R.eq_constr b (Lazy.force CoqTerms.ctrue) then 1
            else if R.eq_constr b (Lazy.force CoqTerms.cfalse) then 0
            else R.raise_error "Eunoia: malformed computed character" in
          i+1,n lor (bit lsl i)) (0,0) bits |> snd in
        Buffer.add_char buf (Char.chr n); go tail
      | _ -> R.raise_error "Eunoia: malformed computed character")
    | _ -> R.raise_error "Eunoia: malformed computed string" in
  go t
let rec decode_term t = match R.decompose_app_list t with
  | h,[s] when R.eq_constr h (global (syntax ^ "Symbol")) -> EunoiaElaborate.Symbol(decode_string s)
  | h,[f;a] when R.eq_constr h (global (syntax ^ "Apply")) -> EunoiaElaborate.Apply(decode_term f,decode_term a)
  | _ -> R.raise_error "Eunoia: malformed computed generated term"
let compute_term_option env tm =
  let ty = SmtMisc.mklApp CoqTerms.coption [|term_type ()|] in
  let v = R.cbv_vm env tm ty in
  match R.decompose_app_list v with
  | h,[_;t] when R.eq_constr h (Lazy.force CoqTerms.cSome) -> Some (decode_term t)
  | h,[_] when R.eq_constr h (Lazy.force CoqTerms.cNone) -> None
  | _ -> R.raise_error "Eunoia: malformed computed option"
let checked_true ?(on_failure=(fun () -> ())) env computation =
  match R.vm_conv Conversion.CUMUL env computation (Lazy.force CoqTerms.ctrue) with
  | Result.Error () ->
    on_failure ();
    R.raise_error "Eunoia: generated checker rejected the certificate"
  | Result.Ok () ->
    R.mkCast (CoqTerms.eq_refl_true (),R.vmcast,
      SmtMisc.mklApp CoqTerms.ceq
        [|Lazy.force CoqTerms.cbool;computation;Lazy.force CoqTerms.ctrue|])

let rec decode_list decode t = match R.decompose_app_list t with
  | h,[_] when R.eq_constr h (Lazy.force CoqTerms.cnil) -> []
  | h,[_;x;xs] when R.eq_constr h (Lazy.force CoqTerms.ccons) ->
    decode x :: decode_list decode xs
  | _ -> R.raise_error "Eunoia: malformed computed metadata list"

(* Read the metadata from the loaded generated module, never the proof file.
   This is syntactic admission only: generated typing/derivation and the exact
   semantic gate must still succeed for every inference. *)
let signature_names env =
  let generated n = global ("SMTCoq.checker.eunoia.CpcGenerated." ^ n) in
  let str_ty = global "Stdlib.Strings.String.string" in
  let list_ty ty = SmtMisc.mklApp CoqTerms.clist [|ty|] in
  let strings n = decode_list decode_string
    (R.cbv_vm env (generated n) (list_ty str_ty)) in
  let pair_ty = SmtMisc.mklApp CoqTerms.cprod [|str_ty;term_type ()|] in
  let pairs n = decode_list (fun p -> match R.decompose_app_list p with
    | h,[_;_;s;t] when R.eq_constr h (Lazy.force CoqTerms.cpair) ->
      decode_string s,decode_term t
    | _ -> R.raise_error "Eunoia: malformed generated metadata pair")
    (R.cbv_vm env (generated n) (list_ty pair_ty)) in
  let rec symbols = function
    | EunoiaElaborate.Symbol s -> [s]
    | EunoiaElaborate.Apply(f,a) -> symbols f @ symbols a in
  List.sort_uniq String.compare
    (strings "cpc_blocked_operators" @ strings "cpc_binary_operators" @
     List.concat_map (fun n -> List.concat_map (fun (s,t) -> s::symbols t) (pairs n))
       ["cpc_aliases";"cpc_surface_names";"cpc_operators"])
