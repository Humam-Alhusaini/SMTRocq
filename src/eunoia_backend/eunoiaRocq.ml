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
  (* Resolve constructors once per call. These bindings never outlive the
     current Rocq environment and share no computed proof or checker result. *)
  let ascii = global "Stdlib.Strings.Ascii.Ascii" in
  let cons = global "Stdlib.Strings.String.String" in
  let chars = ref (global "Stdlib.Strings.String.EmptyString") in
  for i = String.length s - 1 downto 0 do
    let n = Char.code s.[i] in
    let bits = Array.init 8 (fun b -> Lazy.force
      (if n land (1 lsl b) <> 0 then CoqTerms.ctrue else CoqTerms.cfalse)) in
    let c = R.mkApp (ascii,bits) in
    chars := R.mkApp (cons,[|c;!chars|])
  done; !chars
let syntax = "SMTCoq.checker.eunoia.EoSyntax."
let term_type () = global (syntax ^ "term")
let rec term = function
  | EunoiaElaborate.Symbol s -> call (syntax ^ "Symbol") [string s]
  | EunoiaElaborate.Apply(f,a) -> call (syntax ^ "Apply") [term f;term a]
let term_list xs = list (term_type ()) (List.map term xs)

(* Immutable producer syntax, shared only within one proof invocation.
   Generated computation and semantic checking still process every step. *)
let make_term_encoder () =
  if Sys.getenv_opt "EUNOIA_DISABLE_TERM_CACHE" = Some "1" then term else
  let symbols = Hashtbl.create 127 and terms = Hashtbl.create 1021 in
  let symbol = global (syntax ^ "Symbol") and apply = global (syntax ^ "Apply") in
  let ascii = global "Stdlib.Strings.Ascii.Ascii" in
  let cons = global "Stdlib.Strings.String.String" in
  let empty = global "Stdlib.Strings.String.EmptyString" in
  let chars = Array.init 256 (fun n ->
    R.mkApp (ascii, Array.init 8 (fun b -> Lazy.force
      (if n land (1 lsl b) <> 0 then CoqTerms.ctrue else CoqTerms.cfalse)))) in
  let encode_string s = match Hashtbl.find_opt symbols s with
    | Some c -> c
    | None ->
      let c = ref empty in
      for i = String.length s - 1 downto 0 do
        c := R.mkApp (cons,[|chars.(Char.code s.[i]);!c|])
      done;
      if Hashtbl.length symbols < 4096 then Hashtbl.add symbols s !c;
      !c in
  let rec encode t = match Hashtbl.find_opt terms t with
    | Some c -> c
    | None ->
      let c = match t with
        | EunoiaElaborate.Symbol s -> R.mkApp (symbol,[|encode_string s|])
        | EunoiaElaborate.Apply(f,a) -> R.mkApp (apply,[|encode f;encode a|]) in
      if Hashtbl.length terms < 16384 then Hashtbl.add terms t c;
      c in
  encode
let decode_string t =
  let empty = global "Stdlib.Strings.String.EmptyString" in
  let cons = global "Stdlib.Strings.String.String" in
  let ascii = global "Stdlib.Strings.Ascii.Ascii" in
  let buf = Buffer.create 32 in
  let rec go t = match R.decompose_app_list t with
    | h,[] when R.eq_constr h empty -> Buffer.contents buf
    | h,[c;tail] when R.eq_constr h cons ->
      (match R.decompose_app_list c with
      | h,bits when R.eq_constr h ascii && List.length bits=8 ->
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
  let str_ty = global "Stdlib.Strings.String.string" in
  let list_ty = SmtMisc.mklApp CoqTerms.clist [|str_ty|] in
  let inventory = global "SMTCoq.checker.eunoia.CpcGenerated.cpc_signature_names" in
  List.sort_uniq String.compare
    (decode_list decode_string (R.cbv_vm env inventory list_ty))
