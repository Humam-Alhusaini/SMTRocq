open Common
module R = RocqInterface
module C = EunoiaRocq
(* Only proved facts about actual Rocq functions; these are not new SMT-LIB
   operators. Every emitted fact remains a proof argument to the checked tactic. *)
let collect env ~equalities terms =
  (* Preprocessing may represent a proved Boolean fact as [b <-> true].
     Unwrap only proved truth, never false polarity or arbitrary connectives. *)
  let rec unwrap depth (proof,value) =
    if depth=0 then proof,value else
    let head,args = R.decompose_app_list value in
    match args with
    | [a;b] when R.eq_constr head (Lazy.force CoqTerms.ceqb) ->
      let truth = Lazy.force CoqTerms.ctrue in
      let apply name value = unwrap (depth-1)
        (C.call ("SMTCoq.checker.eunoia.EunoiaDivision.EunoiaDivision." ^ name) [value;proof],value) in
      if R.eq_constr b truth then apply "boolean_eq_true" a
      else if R.eq_constr a truth then apply "boolean_true_eq" b
      else proof,value
    | _ -> proof,value in
  let equalities = List.map (unwrap 8) equalities in
  let div = C.global "Stdlib.ZArith.BinInt.Z.div"
  and modulo = C.global "Stdlib.ZArith.BinInt.Z.modulo"
  and abs = C.global "Stdlib.ZArith.BinInt.Z.abs"
  and min = C.global "Stdlib.ZArith.BinInt.Z.min"
  and max = C.global "Stdlib.ZArith.BinInt.Z.max"
  and sgn = C.global "Stdlib.ZArith.BinInt.Z.sgn" in
  let z0 = Lazy.force CoqTerms.cZ0 and zpos = Lazy.force CoqTerms.cZpos
  and zneg = Lazy.force CoqTerms.cZneg in
  let rec positive t = match R.decompose_app_list t with
    | h,[] -> R.eq_constr h (Lazy.force CoqTerms.cxH)
    | h,[p] when R.eq_constr h (Lazy.force CoqTerms.cxO) ||
        R.eq_constr h (Lazy.force CoqTerms.cxI) -> positive p
    | _ -> false in
  let rec numeral t = match R.decompose_app_list t with
    | h,[] -> R.eq_constr h z0
    | h,[p] when R.eq_constr h zpos || R.eq_constr h zneg -> positive p
    | h,[x] when R.eq_constr h (Lazy.force CoqTerms.copp) -> numeral x
    | h,[x;y] when List.exists (R.eq_constr h)
        (List.map Lazy.force [CoqTerms.cadd;CoqTerms.csub;CoqTerms.cmul]) -> numeral x && numeral y
    | _ -> false in
  let seen = ref [] and facts = ref [] and budget = ref 100000 in
  let emit_at namespace name args =
    let proof = C.call ("SMTCoq.checker.eunoia." ^ namespace ^ "." ^ namespace ^ "." ^ name) args in
    if List.length !facts < 64 && not (List.exists (R.eq_constr proof) !facts) then
      facts := proof :: !facts in
  let emit = emit_at "EunoiaDivision" in
  let integer = emit_at "EunoiaIntegerFacts" in
  let normalize t = if numeral t then Some (R.cbv_vm env t (Lazy.force CoqTerms.cZ)) else None in
  let sign d = match R.decompose_app_list d with
    | h,[p] when R.eq_constr h zpos -> Some ("positive",p)
    | h,[p] when R.eq_constr h zneg -> Some ("negative",p)
    | _ -> None in
  let normalize_application head args =
    R.cbv_vm env (R.mkApp (head,Array.of_list args)) (Lazy.force CoqTerms.cZ) in
  (* These proofs apply general standard-library identities. Ground products
     in their types convert to the observed offsets/divisors; no equality is
     assumed from this producer-side recognition. Final exact_check and Qed
     still check each proof application and root binding. *)
  let algebra head x d = match sign d with
    | None -> ()
    | Some (direction,p) ->
      let shift base k =
        emit (direction ^ (if R.eq_constr head div then "_division_shift" else "_modulo_shift")) [base;k;p] in
      let h,args = R.decompose_app_list x in
      (match args with
       | [base;offset] when R.eq_constr h (Lazy.force CoqTerms.cadd) ||
           R.eq_constr h (Lazy.force CoqTerms.csub) ->
         let offset = if R.eq_constr h (Lazy.force CoqTerms.csub) then
           R.mkApp (Lazy.force CoqTerms.copp,[|offset|]) else offset in
         (match normalize offset with
          | Some offset when R.eq_constr (normalize_application modulo [offset;d]) z0 ->
            shift base (normalize_application div [offset;d])
          | _ -> ())
       | _ -> ());
      (match args with
       | [base;inner] when R.eq_constr head div && R.eq_constr h div && direction="positive" ->
         (match normalize inner with
          | Some inner -> (match sign inner with
            | Some (inner_direction,q) -> emit ("nested_" ^ inner_direction ^ "_positive") [base;q;p]
            | None -> ())
          | None -> ())
       | _ -> ()) in
  let known_value head x d =
    let instantiate y equality =
      if numeral y && List.length !facts < 64 then begin
        let value = normalize_application head [y;d] in
        emit (if R.eq_constr head div then "quotient_value" else "remainder_value")
          [x;y;d;value;equality;CoqTerms.eq_refl_true ()]
      end in
    if numeral x then instantiate x (C.call "Stdlib.ZArith.BinInt.Z.eqb_refl" [x]);
    List.iter (fun (proof,value) ->
      let h,args = R.decompose_app_list value in
      match args with
      | [a;b] when R.eq_constr h (Lazy.force CoqTerms.ceqbZ) ->
        if R.eq_constr a x then instantiate b proof
        else if R.eq_constr b x then instantiate a
          (C.call "SMTCoq.checker.eunoia.EunoiaDivision.EunoiaDivision.eqb_swap" [a;b;proof])
      | _ -> ()) equalities in
  let add_ground head x divisor =
    if List.length !facts < 64 && numeral divisor then begin
      let d = R.cbv_vm env divisor (Lazy.force CoqTerms.cZ) in
      if not (List.exists (fun (old_x,old_d) -> R.eq_constr x old_x && R.eq_constr d old_d) !seen) then begin
        let law = match R.decompose_app_list d with
          | h,[] when R.eq_constr h z0 -> Some ("zero_laws",[x])
          | h,[p] when R.eq_constr h zpos -> Some ("positive_laws",[x;p])
          | h,[p] when R.eq_constr h zneg -> Some ("negative_laws",[x;p])
          | _ -> None in
        match law with
        | None -> ()
        | Some (name,args) ->
          seen := (x,d)::!seen;
          emit name args
      end;
      algebra head x d;
      known_value head x d
    end in
  (* Resolve only a supplied, proved equality to a ground divisor. The actual
     proof is an argument of the linking lemma and is checked by Rocq. *)
  let known_divisor d =
    List.find_map (fun (proof,value) ->
      let h,args = R.decompose_app_list value in
      match args with
      | [a;b] when R.eq_constr h (Lazy.force CoqTerms.ceqbZ) ->
        if R.eq_constr a d && numeral b then Some (b,proof)
        else if R.eq_constr b d && numeral a then Some (a,
          C.call "SMTCoq.checker.eunoia.EunoiaDivision.EunoiaDivision.eqb_swap" [a;b;proof])
        else None
      | _ -> None) equalities in
  let symbolic_seen = ref [] and operation_seen = ref [] in
  let add head x d =
    if numeral d then add_ground head x d
    else if List.length !facts < 64 && not (List.exists (fun (h,a,b) ->
        R.eq_constr h head && R.eq_constr a x && R.eq_constr b d) !symbolic_seen) then begin
      symbolic_seen := (head,x,d) :: !symbolic_seen;
      match known_divisor d with
      | Some (n,proof) ->
        integer (if R.eq_constr head div then "known_quotient_divisor" else "known_remainder_divisor") [x;d;n;proof];
        add_ground head x n
      | None ->
        if R.eq_constr head modulo then begin
          integer "symbolic_positive_modulo" [x;d];
          integer "symbolic_negative_modulo" [x;d]
        end;
        integer "symbolic_zero_division" [x;d]
    end in
  let operation t head args =
    if List.length !facts < 64 && not (List.exists (R.eq_constr t) !operation_seen) then begin
      operation_seen := t :: !operation_seen;
      match args with
      | [x] when R.eq_constr head abs -> integer "abs_laws" [x]
      | [x] when R.eq_constr head sgn -> integer "sign_laws" [x]
      | [x;y] when R.eq_constr head min -> integer "min_laws" [x;y]
      | [x;y] when R.eq_constr head max -> integer "max_laws" [x;y]
      | _ -> ()
    end in
  let rec visit t =
    if !budget > 0 then begin
      decr budget;
      match Constr.kind t with
      | Constr.App _ ->
        let head,args = R.decompose_app_list t in
        List.iter visit args;
        (match args with
         | [x;d] when R.eq_constr head div || R.eq_constr head modulo -> add head x d
         | _ -> if R.eq_constr head abs || R.eq_constr head sgn || R.eq_constr head min || R.eq_constr head max then operation t head args)
      | Constr.Cast (body,_,_) -> visit body
      (* Skip binders and branches: their local variables cannot be used as
         new outer proof assumptions. The public preprocessor introduces binders. *)
      | _ -> ()
    end in
  List.iter visit terms; List.rev !facts
