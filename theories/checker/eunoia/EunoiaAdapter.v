(**************************************************************************)
(*     SMTCoq                                                             *)
(*     Distributed under the terms of the CeCILL-C licence (see LICENSE). *)
(**************************************************************************)

From Stdlib Require Import List String Bool Ascii ZArith DecimalString Uint63.
From SMTCoq.utils Require Import Misc PArray CompDec.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EoSyntax EoArithmetic CpcGenerated EunoiaChecker EunoiaBridge.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope uint63_scope.
Local Open Scope array_scope.

Module EunoiaAdapter.

Definition app (s : string) (ts : list term) : term :=
  fold_left Apply ts (Symbol s).

Fixpoint traverse {A B : Type} (f : A -> option B) (xs : list A)
    : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs =>
    match f x, traverse f xs with
    | Some y, Some ys => Some (y :: ys)
    | _, _ => None
    end
  end.

  Fixpoint spine (t : term) (args : list term) : term * list term :=
    match t with
    | Symbol _ => (t, args)
    | Apply f a => spine f (a :: args)
    end.


(* The CPC payload always retains its original source term. Integer addition
   and multiplication have n-ary surface notation but binary SMTCoq atoms.
   Lower only applications with at least three arguments, to a fixed right
   fold, preserving every operand, order, duplicate and binary subtree. *)
Fixpoint lower_arithmetic (fuel : nat) (t : term) : option term :=
  match fuel with
  | O => None
  | S k =>
    let '(head, args) := spine t [] in
    match head, traverse (lower_arithmetic k) args with
    | Symbol s, Some xs =>
      if String.eqb s "@purify" then
        (* CPC purification names the original term. Keep raw syntax for
           generated rule evaluation; only the table-binding view unfolds it.
           Every resulting local implication is still certified by the gate. *)
        match xs with [x] => Some x | _ => None end
      else if String.eqb s "+" || String.eqb s "*" then
        match xs with
        | a :: b :: c :: rest =>
          let fix chain x xs := match xs with
            | [] => x
            | y :: ys => app s [x; chain y ys]
            end in Some (chain a (b :: c :: rest))
        | _ => Some (app s xs)
        end
      else Some (app s xs)
    | _, _ => None
    end
  end.

Lemma term_eqb_spec : forall a b, term_eqb a b = true <-> a = b.
Proof.
  induction a as [s|f IHf a IHa]; destruct b; simpl;
    try (split; [discriminate | congruence]).
  - rewrite String.eqb_eq.
    split; [intro H; subst; reflexivity | intro H; inversion H; auto].
  - rewrite andb_true_iff, IHf, IHa.
    split; [intros [-> ->]; reflexivity | intro H; inversion H; auto].
Qed.

Definition numeral (z : Z) : string :=
  NilZero.string_of_int (Z.to_int z).

(* Only canonical signed decimal literals. No lexical normalization on input. *)
Definition is_numeral (s : string) : bool :=
  match NilZero.int_of_string s with
  | Some n => String.eqb s (numeral (Z.of_int n))
  | None => false
  end.

Definition reserved : list string :=
  ["Bool"; "Int"; "Type"; "->"; "true"; "false"; "not"; "and";
   "or"; "=>"; "xor"; "ite"; "="; "+"; "-"; "*"; "<"; "<="; ">"; ">=";
   "Real"; "@List"; "@list"; "@list.nil";
   "eo::List"; "eo::List::cons"; "eo::List::nil"].

Definition is_literal_name (s : string) : bool :=
  match EoArithmetic.parse s with Some _ => true | None => false end.

(* Shared by sort names and function names: no collision with CPC primitives,
   duplicate names, duplicate indices, or array defaults. Names are already
   resolved identifiers, not quoted tokens or CPC define aliases. *)
Record naming := Naming {
  sort_names : list (int * string);
  function_names : list (int * string)
}.

Fixpoint name_at (i : int) (ns : list (int * string)) : option string :=
  match ns with
  | [] => None
  | (j, s) :: ns => if i =? j then Some s else name_at i ns
  end.

Definition fresh_name (s : string) (ns : list string) : bool :=
  negb (existsb (String.eqb s) ns).

Fixpoint unique_names (ns : list string) : bool :=
  match ns with
  | [] => true
  | s :: ns => fresh_name s ns && unique_names ns
  end.

Fixpoint map_wf (bound : int) (ns : list (int * string)) : bool :=
  match ns with
  | [] => true
  | (i, s) :: ns =>
    (i <? bound) && negb (existsb (fun p => i =? fst p) ns) &&
    negb (String.eqb s "") && fresh_name s reserved && negb (is_literal_name s) &&
    map_wf bound ns
  end.

Section Tables.
  Variable t_i : array typ_compdec.
  Variable t_func : array (Atom.tval t_i).
  Variable t_atom : array Atom.atom.
  Variable t_form : array Form.form.
  Variable names : naming.

  Definition names_wf : bool :=
    map_wf (PArray.length t_i) (sort_names names) &&
    map_wf (PArray.length t_func) (function_names names) &&
    unique_names (map snd (sort_names names ++ function_names names)).

  Definition encode_sort (ty : Typ.type) : option term :=
    match ty with
    | Typ.Tbool => Some (Symbol "Bool")
    | Typ.TZ => Some (Symbol "Int")
    | Typ.Tindex n =>
      (* Check before of_Z, which otherwise wraps modulo 2^63. *)
      if Z.ltb (Z.of_N n) (Uint63.to_Z (PArray.length t_i)) then
        option_map Symbol (name_at (Uint63.of_Z (Z.of_N n)) (sort_names names))
      else None
    | _ => None
    end.

  Definition get_type := Atom.get_type t_i t_func t_atom.

  (* SMTCoq's internal positive numeral DAG is not a CPC function symbol. *)
  Fixpoint positive_at (fuel : nat) (i : int) : option positive :=
    match fuel with
    | O => None
    | S k =>
      if (i <? PArray.length t_atom) && Atom.lt_atom i (t_atom.[i]) then
        match t_atom.[i] with
        | Atom.Acop Atom.CO_xH => Some xH
        | Atom.Auop Atom.UO_xO j => option_map xO (positive_at k j)
        | Atom.Auop Atom.UO_xI j => option_map xI (positive_at k j)
        | _ => None
        end
      else None
    end.

  Definition binop_name (op : Atom.binop) : option string :=
    match op with
    | Atom.BO_Zplus => Some "+" | Atom.BO_Zminus => Some "-"
    | Atom.BO_Zmult => Some "*" | Atom.BO_Zlt => Some "<"
    | Atom.BO_Zle => Some "<=" | Atom.BO_Zge => Some ">="
    | Atom.BO_Zgt => Some ">"
    | Atom.BO_eq ty => match encode_sort ty with Some _ => Some "=" | _ => None end
    | _ => None
    end.

  (* Existing Atom typechecking is authoritative; no certificate type oracle.
     Every recursive read is bounded and strictly below its parent. *)
  Fixpoint encode_atom_reference (fuel : nat) (i : int) : option term :=
    match fuel with
    | O => None
    | S k =>
      if (i <? PArray.length t_atom) && Atom.lt_atom i (t_atom.[i]) &&
         Atom.check_aux t_i t_func get_type (t_atom.[i]) (get_type i) then
        match encode_sort (get_type i) with
        | None => None
        | Some _ =>
          match t_atom.[i] with
          | Atom.Acop Atom.CO_Z0 => Some (Symbol "0")
          | Atom.Auop Atom.UO_Zpos j =>
            option_map (fun p => Symbol (numeral (Zpos p))) (positive_at k j)
          | Atom.Auop Atom.UO_Zneg j =>
            option_map (fun p => Symbol (numeral (Zneg p))) (positive_at k j)
          | Atom.Auop Atom.UO_Zopp j =>
            option_map (fun a => app "-" [a]) (encode_atom_reference k j)
          | Atom.Abop op a b =>
            match binop_name op, encode_atom_reference k a, encode_atom_reference k b with
            | Some s, Some x, Some y => Some (app s [x; y])
            | _, _, _ => None
            end
          | Atom.Aapp f args =>
            if f <? PArray.length t_func then
              match name_at f (function_names names), traverse (encode_atom_reference k) args,
                    traverse encode_sort (fst (Atom.v_type _ _ (t_func.[f]))),
                    encode_sort (snd (Atom.v_type _ _ (t_func.[f]))) with
              | Some s, Some xs, Some _, Some _ => Some (app s xs)
              | _, _, _, _ => None
              end
            else None
          | _ => None
          end
        end
      else None
    end.

  Definition encode_atom_with_type (type_of : int -> Typ.type)
      : nat -> int -> option term :=
    fix visit (fuel : nat) (i : int) : option term :=
    match fuel with
    | O => None
    | S k =>
      if (i <? PArray.length t_atom) && Atom.lt_atom i (t_atom.[i]) &&
         Atom.check_aux t_i t_func type_of (t_atom.[i]) (type_of i) then
        match encode_sort (type_of i) with
        | None => None
        | Some _ =>
          match t_atom.[i] with
          | Atom.Acop Atom.CO_Z0 => Some (Symbol "0")
          | Atom.Auop Atom.UO_Zpos j =>
            option_map (fun p => Symbol (numeral (Zpos p))) (positive_at k j)
          | Atom.Auop Atom.UO_Zneg j =>
            option_map (fun p => Symbol (numeral (Zneg p))) (positive_at k j)
          | Atom.Auop Atom.UO_Zopp j =>
            option_map (fun a => app "-" [a]) (visit k j)
          | Atom.Abop op a b =>
            match binop_name op, visit k a, visit k b with
            | Some s, Some x, Some y => Some (app s [x; y])
            | _, _, _ => None
            end
          | Atom.Aapp f args =>
            if f <? PArray.length t_func then
              match name_at f (function_names names), traverse (visit k) args,
                    traverse encode_sort (fst (Atom.v_type _ _ (t_func.[f]))),
                    encode_sort (snd (Atom.v_type _ _ (t_func.[f]))) with
              | Some s, Some xs, Some _, Some _ => Some (app s xs)
              | _, _, _, _ => None
              end
            else None
          | _ => None
          end
        end
      else None
    end.

  Definition encode_atom (fuel : nat) (i : int) : option term :=
    let interpreted := @Atom.t_interp t_i t_func t_atom in
    encode_atom_with_type (@Atom.get_type' t_i interpreted) fuel i.
  Lemma encode_atom_refinement : forall fuel i,
    encode_atom fuel i = encode_atom_reference fuel i.
  Proof. reflexivity. Qed.

  Fixpoint double_nots (fuel : nat) (n : int) (t : term) : option term :=
    if n =? 0 then Some t else
    match fuel with
    | O => None
    | S k => double_nots k (n - 1) (app "not" [app "not" [t]])
    end.

  (* No associative flattening, identity elimination, or Boolean simplification.
     Degenerate n-ary nodes lack an unambiguous surface encoding here. *)
  Definition nary (s : string) (xs : list term) : option term :=
    match xs with _ :: _ :: _ => Some (app s xs) | _ => None end.

  Fixpoint encode_literal_reference (fuel : nat) (l : _lit) : option term :=
    match fuel with
    | O => None
    | S k =>
      let i := Lit.blit l in
      if (i <? PArray.length t_form) && Form.lt_form i (t_form.[i]) then
        let base :=
          match t_form.[i] with
          | Form.Ftrue => Some (Symbol "true")
          | Form.Ffalse => Some (Symbol "false")
          | Form.Fatom a =>
            if (a <? PArray.length t_atom) && Typ.eqb (get_type a) Typ.Tbool
            then encode_atom_reference k a else None
          | Form.Fnot2 n a =>
            match encode_literal_reference k a with
            | Some t => double_nots k n t
            | None => None
            end
          | Form.Fand args | Form.For args | Form.Fimp args =>
            match traverse (encode_literal_reference k) (to_list args) with
            | Some xs => nary
                (match t_form.[i] with Form.Fand _ => "and" | Form.For _ => "or"
                 | _ => "=>" end) xs
            | None => None
            end
          | Form.Fxor a b | Form.Fiff a b =>
            match encode_literal_reference k a, encode_literal_reference k b with
            | Some x, Some y => Some (app
                (match t_form.[i] with Form.Fxor _ _ => "xor" | _ => "=" end) [x; y])
            | _, _ => None
            end
          | Form.Fite a b c =>
            match encode_literal_reference k a, encode_literal_reference k b, encode_literal_reference k c with
            | Some x, Some y, Some z => Some (app "ite" [x; y; z])
            | _, _, _ => None
            end
          | _ => None
          end in
        option_map (fun t => if Lit.is_pos l then t else app "not" [t]) base
      else None
    end.

  Definition encode_literal_with_type (type_of : int -> Typ.type)
      : nat -> _lit -> option term :=
    let atom_encoder := encode_atom_with_type type_of in
    fix visit (fuel : nat) (l : _lit) : option term :=
    match fuel with
    | O => None
    | S k =>
      let i := Lit.blit l in
      if (i <? PArray.length t_form) && Form.lt_form i (t_form.[i]) then
        let base :=
          match t_form.[i] with
          | Form.Ftrue => Some (Symbol "true")
          | Form.Ffalse => Some (Symbol "false")
          | Form.Fatom a =>
            if (a <? PArray.length t_atom) && Typ.eqb (type_of a) Typ.Tbool
            then atom_encoder k a else None
          | Form.Fnot2 n a =>
            match visit k a with
            | Some t => double_nots k n t
            | None => None
            end
          | Form.Fand args | Form.For args | Form.Fimp args =>
            match traverse (visit k) (to_list args) with
            | Some xs => nary
                (match t_form.[i] with Form.Fand _ => "and" | Form.For _ => "or"
                 | _ => "=>" end) xs
            | None => None
            end
          | Form.Fxor a b | Form.Fiff a b =>
            match visit k a, visit k b with
            | Some x, Some y => Some (app
                (match t_form.[i] with Form.Fxor _ _ => "xor" | _ => "=" end) [x; y])
            | _, _ => None
            end
          | Form.Fite a b c =>
            match visit k a, visit k b, visit k c with
            | Some x, Some y, Some z => Some (app "ite" [x; y; z])
            | _, _, _ => None
            end
          | _ => None
          end in
        option_map (fun t => if Lit.is_pos l then t else app "not" [t]) base
      else None
    end.

  Definition encode_literal (fuel : nat) (l : _lit) : option term :=
    let interpreted := @Atom.t_interp t_i t_func t_atom in
    encode_literal_with_type (@Atom.get_type' t_i interpreted) fuel l.
  Lemma encode_literal_refinement : forall fuel l,
    encode_literal fuel l = encode_literal_reference fuel l.
  Proof. reflexivity. Qed.

  (* These are views of a precise clause, never a decoder guessing its indices.
     [false] denotes [] explicitly; a singleton Ffalse remains that singleton. *)
  Definition encode_clause (fuel : nat) (c : C.t) : option term :=
    let interpreted := @Atom.t_interp t_i t_func t_atom in
    let encode := encode_literal_with_type (@Atom.get_type' t_i interpreted) fuel in
    match c with
    | [] => Some (Symbol "false")
    | [l] => encode l
    | _ => option_map (app "or") (traverse encode c)
    end.

  (* A computed cache, never supplied by the proof producer. Misses use the
     original encoder; a pointwise theorem preserves arbitrary fuel/tables. *)
  Fixpoint lookup_encoding (entries : list (_lit * option term)) (l : _lit)
      : option (option term) :=
    match entries with
    | [] => None
    | (key, value) :: rest =>
      if l =? key then Some value else lookup_encoding rest l
    end.

  Lemma lookup_encoding_sound : forall (f : _lit -> option term) keys l value,
    lookup_encoding (map (fun key => (key, f key)) keys) l = Some value ->
    value = f l.
  Proof.
    intros f keys; induction keys as [ | index rest IH]; intros l value H; simpl in H.
    - discriminate.
    - destruct (l =? index) eqn:He.
      + apply Uint63.eqb_spec in He; subst index. inversion H; reflexivity.
      + now apply (IH l value).
  Qed.

  Definition encoding_entries (fuel : nat) (literals : list _lit)
      : list (_lit * option term) :=
    let unique := fold_right (fun l acc =>
      if existsb (fun key => l =? key) acc then acc else l :: acc)
      [] (firstn 1024 literals) in
    let interpreted := @Atom.t_interp t_i t_func t_atom in
    let encode := encode_literal_with_type (@Atom.get_type' t_i interpreted) fuel in
    map (fun l => (l, encode l)) (firstn 512 unique).

  Definition memo_encoding entries (fuel : nat) (l : _lit) :=
    match lookup_encoding entries l with
      | Some value => value | None => encode_literal fuel l end.

  Lemma memo_encoding_refinement : forall fuel keys l,
    memo_encoding (encoding_entries fuel keys) fuel l = encode_literal fuel l.
  Proof.
    intros fuel keys l; unfold memo_encoding, encoding_entries.
    destruct (lookup_encoding _ l) as [value | ] eqn:H; [ | reflexivity].
    now apply lookup_encoding_sound in H.
  Qed.

  Definition cached_clause entries (fuel : nat) : C.t -> option term :=
    let encode := memo_encoding entries fuel in
    fun c => match c with
    | [] => Some (Symbol "false")
    | [l] => encode l
    | _ => option_map (app "or") (traverse encode c)
    end.

  Lemma cached_clause_refinement : forall fuel keys c,
    cached_clause (encoding_entries fuel keys) fuel c = encode_clause fuel c.
  Proof.
    intros fuel keys c.
    assert (forall xs, traverse (memo_encoding (encoding_entries fuel keys) fuel) xs =
      traverse (encode_literal fuel) xs) as H.
    { induction xs as [ | x xs IH]; simpl; [reflexivity | ].
      rewrite memo_encoding_refinement, IH; reflexivity. }
    destruct c as [ | x [ | y xs]]; unfold cached_clause, encode_clause;
      [reflexivity | apply memo_encoding_refinement | now rewrite H].
  Qed.

  Definition binds (fuel : nat) (c : C.t) (t : term) : bool :=
    EunoiaChecker.clause_wf (PArray.length t_form) c &&
    match encode_clause fuel c, lower_arithmetic fuel t with
    | Some u, Some v => term_eqb u v
    | _, _ => false
    end.

  Definition cached_binds entries fuel c t :=
    EunoiaChecker.clause_wf (PArray.length t_form) c &&
    match cached_clause entries fuel c, lower_arithmetic fuel t with
    | Some u, Some v => term_eqb u v | _, _ => false end.
  Lemma cached_binds_refinement : forall fuel keys c t,
    cached_binds (encoding_entries fuel keys) fuel c t = binds fuel c t.
  Proof.
    intros; unfold cached_binds, binds; rewrite cached_clause_refinement; reflexivity.
  Qed.

  Lemma binds_spec : forall fuel c t, binds fuel c t = true <->
    EunoiaChecker.clause_wf (PArray.length t_form) c = true /\
    exists u, encode_clause fuel c = Some u /\ lower_arithmetic fuel t = Some u.
  Proof.
    intros fuel c t; unfold binds; rewrite andb_true_iff.
    destruct (encode_clause fuel c) as [u | ] eqn:Hu;
      destruct (lower_arithmetic fuel t) as [v | ] eqn:Hv.
    - rewrite term_eqb_spec; split.
      + intros [H ->]; split; [exact H| eauto].
      + intros [H [w [H1 H2]]]; inversion H1; inversion H2; subst; auto.
    - split; [intros [_ H]; discriminate| intros [_ [w [_ H]]]; discriminate].
    - split; [intros [_ H]; discriminate| intros [_ [w [H _]]]; discriminate].
    - split; [intros [_ H]; discriminate| intros [_ [w [H _]]]; discriminate].
  Qed.

  Fixpoint bind_terms (fuel : nat) (cs : list C.t) (ts : list term) : bool :=
    match cs, ts with
    | [], [] => true
    | c :: cs, t :: ts => binds fuel c t && bind_terms fuel cs ts
    | _, _ => false
    end.

  Fixpoint cached_bind_terms entries fuel cs ts :=
    match cs,ts with
    | [],[] => true
    | c::cs,t::ts => cached_binds entries fuel c t && cached_bind_terms entries fuel cs ts
    | _,_ => false end.
  Lemma cached_bind_terms_refinement : forall fuel keys cs ts,
    cached_bind_terms (encoding_entries fuel keys) fuel cs ts = bind_terms fuel cs ts.
  Proof.
    intros fuel keys cs; induction cs as [ | c cs IH]; intros [ | t ts]; simpl;
      try reflexivity. rewrite cached_binds_refinement, IH; reflexivity.
  Qed.

  Lemma bind_terms_spec : forall fuel cs ts, bind_terms fuel cs ts = true <->
    Forall2 (fun c t =>
      EunoiaChecker.clause_wf (PArray.length t_form) c = true /\
      (exists u, encode_clause fuel c = Some u /\ lower_arithmetic fuel t = Some u)) cs ts.
  Proof.
    intros fuel cs; induction cs as [ | c cs IH]; destruct ts as [ | t ts]; simpl.
    - split; constructor.
    - split; [discriminate | intro H; inversion H].
    - split; [discriminate | intro H; inversion H].
    - rewrite andb_true_iff, binds_spec, IH.
      split; [intros [H1 H2]; constructor; assumption | intro H; inversion H; auto].
  Qed.

  (* A partial syntactic type query, derived from the same function signatures
     as Atom.check_aux. It neither interprets SMT-LIB nor reads a term map. *)
  Fixpoint function_named (s : string) (ns : list (int * string))
      : option Typ.ftype :=
    match ns with
    | [] => None
    | (i, n) :: ns =>
      if String.eqb s n then
        if i <? PArray.length t_func then Some (Atom.v_type _ _ (t_func.[i]))
        else None
      else function_named s ns
    end.

  Definition same_types (xs : list Typ.type) (ty : Typ.type) : bool :=
    forallb (fun t => Typ.eqb t ty) xs.

  Fixpoint consume_types (expected actual : list Typ.type) : option (list Typ.type) :=
    match expected, actual with
    | _, [] => Some expected
    | x :: xs, y :: ys => if Typ.eqb x y then consume_types xs ys else None
    | _, _ => None
    end.

  Definition builtin_type (s : string) (xs : list Typ.type) : option Typ.type :=
    if String.eqb s "@purify" then
      match xs with [ty] => Some ty | _ => None end
    else if String.eqb s "true" || String.eqb s "false" then
      match xs with [] => Some Typ.Tbool | _ => None end
    else if String.eqb s "not" then
      match xs with [Typ.Tbool] => Some Typ.Tbool | _ => None end
    (* Generated :premise-list arguments can contain one entry. Their internal
       nil-terminated list has Boolean type even though object-level singleton
       connectives are not serialized by encode_literal. *)
    else if String.eqb s "and" || String.eqb s "or" then
      match xs with _ :: _ =>
        if same_types xs Typ.Tbool then Some Typ.Tbool else None
      | _ => None end
    else if String.eqb s "=>" || String.eqb s "xor" then
      match xs with _ :: _ :: _ =>
        if same_types xs Typ.Tbool then Some Typ.Tbool else None
      | _ => None end
    else if String.eqb s "=" then
      match xs with [a; b] => if Typ.eqb a b then Some Typ.Tbool else None
      | _ => None end
    else if String.eqb s "ite" then
      match xs with [Typ.Tbool; a; b] => if Typ.eqb a b then Some a else None
      | _ => None end
    else if existsb (String.eqb s) ["+"; "*"; "-"] then
      match xs with
      | [_] => if String.eqb s "-" && same_types xs Typ.TZ then Some Typ.TZ else None
      | _ :: _ :: _ => if same_types xs Typ.TZ then Some Typ.TZ else None
      | _ => None end
    else if existsb (String.eqb s) ["<"; "<="; ">"; ">="] then
      match xs with [Typ.TZ; Typ.TZ] => Some Typ.Tbool | _ => None end
    else if is_numeral s then
      match xs with [] => Some Typ.TZ | _ => None end
    else None.

  Fixpoint infer (fuel : nat) (t : term) : option Typ.ftype :=
    match fuel with
    | O => None
    | S k =>
      let '(head, args) := spine t [] in
      match head with
      | Apply _ _ => None
      | Symbol s =>
        match traverse (fun a =>
          match infer k a with Some ([], ty) => Some ty | _ => None end) args with
        | None => None
        | Some actual =>
          match function_named s (function_names names) with
          | Some (expected, result) =>
            match consume_types expected actual with
            | Some remaining => Some (remaining, result)
            | None => None
            end
          | None => option_map (fun ty => ([], ty)) (builtin_type s actual)
          end
        end
      end
    end.

  Definition is_sort_name (s : string) : bool :=
    String.eqb s "Bool" || String.eqb s "Int" ||
    existsb (fun p => (fst p <? PArray.length t_i) && String.eqb s (snd p))
      (sort_names names).

  Definition type_term (ft : Typ.ftype) : option term :=
    match traverse encode_sort (fst ft), encode_sort (snd ft) with
    | Some [], Some t => Some t
    | Some args, Some t => Some (app "->" (args ++ [t]))
    | _, _ => None
    end.

  Definition is_function_type (t : term) : bool :=
    match spine t [] with
    | (Symbol s, (_ :: _ :: _) as args) => String.eqb s "->" &&
      forallb (fun a => match a with Symbol n => is_sort_name n | _ => false end) args
    | _ => false
    end.

  Definition object_typeof (fuel : nat) (t : term) : option term :=
      match t with
      | Symbol s =>
        if is_sort_name s then Some (Symbol "Type")
        else match infer fuel t with Some ft => type_term ft | None => None end
      | _ => if is_function_type t then Some (Symbol "Type")
        else match infer fuel t with Some ft => type_term ft | None => None end
      end.

  (* CPC proof arguments can contain heterogeneous lists and rational
     coefficients. These are signature syntax, not new Atom/Form sorts or
     interpretations. The existing object query remains authoritative for
     every term it supports; unsupported object Real expressions stay absent.
     List aliases are from programs/Utils.eo; literal sorts are declared by
     theories/Arith.eo in the pinned signature. *)
  Fixpoint syntax_typeof (fuel : nat) (t : term) : option term :=
    match fuel with
    | O => None
    | S k =>
      match object_typeof fuel t with
      | Some ty => Some ty
      | None =>
        match t with
        | Symbol "Real" | Symbol "@List" | Symbol "eo::List" => Some (Symbol "Type")
        | Symbol "@list.nil" | Symbol "eo::List::nil" => Some (Symbol "@List")
        | Symbol s =>
          match EoArithmetic.parse s with
          | Some (EoArithmetic.LRational _) | Some (EoArithmetic.LDecimal _ _) =>
            Some (Symbol "Real")
          | _ => None
          end
        | _ =>
          let '(head, args) := spine t [] in
          match head, args with
          | Symbol "@list", _ :: _ | Symbol "eo::List::cons", _ :: _ =>
            if forallb (fun a =>
              match syntax_typeof k a with Some _ => true | None => false end) args
            then Some (Symbol "@List") else None
          | _, _ => None
          end
        end
      end
    end.

  Definition typeof (fuel : nat) : term -> option term :=
    let ready := names_wf in
    fun t => if ready then syntax_typeof fuel t else None.

  Definition tables_wf : bool :=
    names_wf && Form.check_form t_form && Atom.check_atom t_atom &&
    Atom.wt t_i t_func t_atom.

  Record rule_payload := MakePayload {
    rule_name : string;
    arguments : list term;
    premise_terms : list term;
    result_term : term;
    result_clause : C.t;
    source_assumption : option term
  }.

  Definition Payload name args premises result clause :=
    MakePayload name args premises result clause None.
  Definition ScopedPayload name args premises result clause assumption :=
    MakePayload name args premises result clause (Some assumption).

  (* Polymorphic only to expose the binding theorem independently of generator
     correctness. The public evaluator below always uses CpcGenerated.derive. *)
  Definition eval_with
      (derive : nat -> (term -> option term) -> string -> list term -> list term -> option term)
      (fuel : nat) : rule_payload -> list C.t -> option C.t :=
    let ready := tables_wf in
    let query := typeof fuel in
    fun p cs =>
    match source_assumption p with
    | Some _ => None
    | None =>
    if ready && bind_terms fuel cs (premise_terms p) then
      match derive fuel query (rule_name p) (arguments p) (premise_terms p) with
      | Some t =>
        if term_eqb t (result_term p) && binds fuel (result_clause p) t
        then Some (result_clause p) else None
      | None => None
      end
    else None
    end.

  Definition cached_eval_with entries
      (derive : nat -> (term -> option term) -> string -> list term -> list term -> option term)
      (fuel : nat) (p : rule_payload) (cs : list C.t) : option C.t :=
    match source_assumption p with
    | Some _ => None
    | None =>
      if tables_wf && cached_bind_terms entries fuel cs (premise_terms p) then
        match derive fuel (typeof fuel) (rule_name p) (arguments p) (premise_terms p) with
        | Some t =>
          if term_eqb t (result_term p) && cached_binds entries fuel (result_clause p) t
          then Some (result_clause p) else None
        | None => None end
      else None end.
  Lemma cached_eval_with_refinement : forall derive fuel keys p cs,
    cached_eval_with (encoding_entries fuel keys) derive fuel p cs = eval_with derive fuel p cs.
  Proof.
    intros; unfold cached_eval_with, eval_with.
    destruct (source_assumption p); [reflexivity | ].
    rewrite cached_bind_terms_refinement.
    destruct (tables_wf && bind_terms fuel cs (premise_terms p)); [ | reflexivity].
    destruct (derive fuel (typeof fuel) (rule_name p) (arguments p) (premise_terms p));
      [now rewrite cached_binds_refinement | reflexivity].
  Qed.

  Definition eval := eval_with CpcGenerated.derive.

  Lemma eval_with_binding : forall derive fuel p cs c,
    eval_with derive fuel p cs = Some c ->
    tables_wf = true /\ bind_terms fuel cs (premise_terms p) = true /\
    derive fuel (typeof fuel) (rule_name p) (arguments p) (premise_terms p) =
      Some (result_term p) /\
    binds fuel c (result_term p) = true /\ c = result_clause p.
  Proof.
    intros derive fuel p cs c H; unfold eval_with in H.
    destruct (source_assumption p); try discriminate.
    destruct (tables_wf && bind_terms fuel cs (premise_terms p)) eqn:Hg;
      try discriminate.
    destruct (derive fuel (typeof fuel) (rule_name p) (arguments p) (premise_terms p))
      as [t | ] eqn:Hd; try discriminate.
    destruct (term_eqb t (result_term p) && binds fuel (result_clause p) t) eqn:Hb;
      try discriminate.
    inversion H; subst c; clear H.
    apply andb_true_iff in Hg; apply andb_true_iff in Hb.
    destruct Hg as [Hw Hp]; destruct Hb as [He Hb].
    apply term_eqb_spec in He; subst t; auto.
  Qed.

  Lemma check_step_binding : forall witness gate fuel m
      (st : @EunoiaChecker.step rule_payload witness) m',
    EunoiaChecker.check_step (eval fuel) gate (PArray.length t_form) m st = Some m' ->
    exists cs,
      EunoiaChecker.fetch m (EunoiaChecker.premises st) = Some cs /\
      bind_terms fuel cs (premise_terms (EunoiaChecker.payload st)) = true /\
      binds fuel (EunoiaChecker.conclusion st)
        (result_term (EunoiaChecker.payload st)) = true /\
      gate cs (EunoiaChecker.conclusion st) (EunoiaChecker.evidence st) = true /\
      S.get (EunoiaChecker.clauses m') (EunoiaChecker.destination st) =
        EunoiaChecker.conclusion st.
  Proof.
    intros witness gate fuel m st m' H.
    apply EunoiaChecker.check_step_binding in H.
    destruct H as [cs [Hf [He [Hg [Hs Hl]]]]].
    apply eval_with_binding in He.
    destruct He as [_ [Hp [_ [Hb _]]]]; exists cs; auto.
  Qed.

  (* The caller's roots are the authoritative negated-goal clauses. The extra
     surface terms cannot replace, reorder, or enlarge them. The semantic gate
     is still mandatory, including when the type query or generator is buggy. *)
  Definition checker {witness : Type}
      (gate : list C.t -> C.t -> witness -> bool)
      (fuel : nat) (capacity : int) (roots : list C.t) (root_terms : list term)
      (claims : list (clause_id * C.t))
      (trace : list (@EunoiaChecker.step rule_payload witness)) (goal : clause_id) : bool :=
    let entries := encoding_entries fuel
      (List.concat roots ++ flat_map EunoiaChecker.conclusion trace)%list in
    tables_wf && bind_terms fuel roots root_terms &&
    EunoiaChecker.checker (cached_eval_with entries CpcGenerated.derive fuel) gate (PArray.length t_form) capacity
      roots claims trace goal.

  Theorem checker_correct : forall witness gate fuel capacity roots root_terms claims
      (trace : list (@EunoiaChecker.step rule_payload witness)) goal rho,
    Valuation.wf rho -> EunoiaChecker.gate_sound gate rho ->
    checker gate fuel capacity roots root_terms claims trace goal = true ->
    ~ Forall (C.valid rho) roots.
  Proof.
    intros witness gate fuel capacity roots root_terms claims trace goal rho Hw Hg H.
    unfold checker in H; apply andb_true_iff in H; destruct H as [_ H].
    eapply EunoiaChecker.checker_correct; eauto.
  Qed.

  Lemma checker_root_binding : forall witness gate fuel capacity roots root_terms claims
      (trace : list (@EunoiaChecker.step rule_payload witness)) goal,
    checker gate fuel capacity roots root_terms claims trace goal = true ->
    bind_terms fuel roots root_terms = true.
  Proof.
    intros witness gate fuel capacity roots root_terms claims trace goal H.
    unfold checker in H; rewrite !andb_true_iff in H; tauto.
  Qed.

  (* Concrete entry point: the same authoritative tables feed both the syntax
     adapter and the existing verified SMTCoq small-checker gate. *)
  Definition checked_checker fuel capacity roots root_terms claims
      (trace : list (@EunoiaChecker.step rule_payload EunoiaBridge.witness)) goal : bool :=
    checker (@EunoiaBridge.gate t_i t_func t_atom t_form)
      fuel capacity roots root_terms claims trace goal.

  Theorem checked_checker_correct : forall fuel capacity roots root_terms claims trace goal,
    checked_checker fuel capacity roots root_terms claims trace goal = true ->
    ~ Forall (C.valid (@EunoiaBridge.valuation t_i t_func t_atom t_form)) roots.
  Proof.
    intros fuel capacity roots root_terms claims trace goal H.
    unfold checked_checker in H.
    assert (tables_wf = true) as Htables.
    { unfold checker in H; rewrite !andb_true_iff in H; tauto. }
    unfold tables_wf in Htables; rewrite !andb_true_iff in Htables.
    destruct Htables as [[[Hnames Hform] Hatom] Hwt].
    eapply checker_correct; [ | | exact H].
    - unfold EunoiaBridge.valuation.
      apply (proj2 (Form.check_form_correct _ _ _ Hform)).
    - now apply EunoiaBridge.gate_correct.
  Qed.

End Tables.

(* Kernel-checked regression examples exercise the public bindings, not an
   alternative CPC evaluator. They are deliberately small and table-backed. *)
Module Examples.
  Definition sorts : array typ_compdec := PArray.make 1 unit_typ_compdec.
  Definition u := Typ.Tindex 0%N.
  Definition funcs : array (Atom.tval sorts) :=
    let fs := PArray.make 6 (@Atom.Tval sorts ([], Typ.Tbool) true) in
    let fs := fs.[0 <- @Atom.Tval sorts ([], u) tt] in
    let fs := fs.[1 <- @Atom.Tval sorts ([], u) tt] in
    let fs := fs.[2 <- @Atom.Tval sorts ([u], u) (fun x => x)] in
    let fs := fs.[3 <- @Atom.Tval sorts ([], Typ.TZ) 0%Z] in
    let fs := fs.[4 <- @Atom.Tval sorts ([], Typ.Tbool) true] in
    fs.[5 <- @Atom.Tval sorts ([], Typ.Tbool) false].

  Definition atoms : array Atom.atom :=
    let a := PArray.make 19 (Atom.Acop Atom.CO_xH) in
    let a := a.[1 <- Atom.Acop Atom.CO_Z0] in
    let a := a.[2 <- Atom.Aapp 0 []] in
    let a := a.[3 <- Atom.Aapp 1 []] in
    let a := a.[4 <- Atom.Aapp 2 [2]] in
    let a := a.[5 <- Atom.Aapp 2 [3]] in
    let a := a.[6 <- Atom.Abop (Atom.BO_eq u) 2 3] in
    let a := a.[7 <- Atom.Abop (Atom.BO_eq u) 4 5] in
    let a := a.[8 <- Atom.Aapp 3 []] in
    let a := a.[9 <- Atom.Auop Atom.UO_Zpos 0] in
    let a := a.[10 <- Atom.Abop Atom.BO_Zplus 8 9] in
    let a := a.[11 <- Atom.Abop Atom.BO_Zle 10 1] in
    let a := a.[12 <- Atom.Aapp 4 []] in
    let a := a.[13 <- Atom.Aapp 5 []] in
    let a := a.[14 <- Atom.Auop Atom.UO_xI 0] in
    let a := a.[15 <- Atom.Auop Atom.UO_Zneg 14] in
    let a := a.[16 <- Atom.Auop Atom.UO_Zopp 9] in
    let a := a.[17 <- Atom.Abop Atom.BO_Zmult 9 8] in
    a.[18 <- Atom.Abop (Atom.BO_eq u) 2 2].

  Definition forms : array Form.form :=
    let f := PArray.make 15 Form.Ftrue in
    let f := f.[1 <- Form.Ffalse] in
    let f := f.[2 <- Form.Fatom 6] in
    let f := f.[3 <- Form.Fatom 7] in
    let f := f.[4 <- Form.Fatom 11] in
    let f := f.[5 <- Form.Fatom 12] in
    let f := f.[6 <- Form.Fatom 13] in
    let args := (PArray.make 2 (Lit.lit 5)).[1 <- Lit.lit 6] in
    let f := f.[7 <- Form.For args] in
    let f := f.[8 <- Form.Fand args] in
    let f := f.[9 <- Form.Fiff (Lit.lit 5) (Lit.lit 6)] in
    let f := f.[10 <- Form.Fnot2 1 (Lit.lit 5)] in
    let f := f.[11 <- Form.Fite (Lit.lit 5) (Lit.lit 6) (Lit.lit 0)] in
    let f := f.[12 <- Form.Fimp args] in
    let f := f.[13 <- Form.Fxor (Lit.lit 5) (Lit.lit 6)] in
    f.[14 <- Form.Fatom 18].

  Definition names := Naming [(0, "U")]
    [(0, "x"); (1, "y"); (2, "f"); (3, "n"); (4, "p"); (5, "q")].
  Definition enc_atom := encode_atom sorts funcs atoms names 40.
  Definition enc_lit := encode_literal sorts funcs atoms forms names 40.
  Definition bound := binds sorts funcs atoms forms names 40.
  Definition bound_terms := bind_terms sorts funcs atoms forms names 40.
  Definition query := typeof sorts funcs names 40.
  Definition run := eval sorts funcs atoms forms names 40.
  Definition x := Symbol "x".
  Definition y := Symbol "y".
  Definition p := Symbol "p".
  Definition q := Symbol "q".

  Example lower_nary_add_order :
    lower_arithmetic 20 (app "+" [x; y; x]) =
      Some (app "+" [x; app "+" [y; x]]).
  Proof. vm_compute; reflexivity. Qed.
  Example preserve_binary_add_tree :
    lower_arithmetic 20 (app "+" [app "+" [x; y]; x]) =
      Some (app "+" [app "+" [x; y]; x]).
  Proof. vm_compute; reflexivity. Qed.
  Example lower_nary_multiply_duplicates :
    lower_arithmetic 20 (app "*" [x; y; y]) =
      Some (app "*" [x; app "*" [y; y]]).
  Proof. vm_compute; reflexivity. Qed.
  Example lower_exhaustion_rejected : lower_arithmetic 0 x = None.
  Proof. reflexivity. Qed.

  Example valid_tables : tables_wf sorts funcs atoms forms names = true.
  Proof. vm_compute; reflexivity. Qed.
  Example uf_application : enc_atom 4 = Some (app "f" [x]).
  Proof. vm_compute; reflexivity. Qed.
  Example integer_linear_term : enc_atom 10 = Some (app "+" [Symbol "n"; Symbol "1"]).
  Proof. vm_compute; reflexivity. Qed.
  Example integer_comparison : enc_lit (Lit.lit 4) =
    Some (app "<=" [app "+" [Symbol "n"; Symbol "1"]; Symbol "0"]).
  Proof. vm_compute; reflexivity. Qed.
  Example negative_literal : enc_atom 15 = Some (Symbol "-3").
  Proof. vm_compute; reflexivity. Qed.
  Example unary_minus_preserved : enc_atom 16 = Some (app "-" [Symbol "1"]).
  Proof. vm_compute; reflexivity. Qed.
  Example coefficient_product : enc_atom 17 = Some (app "*" [Symbol "1"; Symbol "n"]).
  Proof. vm_compute; reflexivity. Qed.
  Example polarity : bound [Lit.nlit 2] (app "not" [app "=" [x; y]]) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example changed_equality : bound [Lit.lit 2] (app "=" [y; x]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example changed_polarity : bound [Lit.lit 2] (app "not" [app "=" [x; y]]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example unit_disjunction : bound [Lit.lit 7] (app "or" [p; q]) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example clause_disjunction : bound [Lit.lit 5; Lit.lit 6] (app "or" [p; q]) = true.
  Proof. vm_compute; reflexivity. Qed.
  Example noncanonical_clause : bound [Lit.lit 6; Lit.lit 5] (app "or" [q; p]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example no_nil_normalization : bound [Lit.lit 7]
    (app "or" [p; app "or" [q; Symbol "false"]]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example false_empty : bound [] (Symbol "false") = true.
  Proof. vm_compute; reflexivity. Qed.
  Example false_unit : bound [Lit.lit 1] (Symbol "false") = true.
  Proof. vm_compute; reflexivity. Qed.
  Example false_no_simplification : bound [] (app "not" [Symbol "true"]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example double_negation_preserved : enc_lit (Lit.lit 10) =
    Some (app "not" [app "not" [p]]).
  Proof. vm_compute; reflexivity. Qed.
  Example all_bool_operations : map enc_lit
      [Lit.lit 8; Lit.lit 9; Lit.lit 11; Lit.lit 12; Lit.lit 13] =
    map (@Some term) [app "and" [p; q]; app "=" [p; q];
      app "ite" [p; q; Symbol "true"]; app "=>" [p; q]; app "xor" [p; q]].
  Proof. vm_compute; reflexivity. Qed.
  Example changed_premise_order : bound_terms [[Lit.lit 5]; [Lit.lit 6]] [q; p] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example missing_premise : bound_terms [[Lit.lit 5]] [] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example extra_root : bound_terms [[Lit.lit 5]] [p; q] = false.
  Proof. vm_compute; reflexivity. Qed.
  Example bounds_not_defaults : enc_lit (Lit.lit 99) = None /\ enc_atom 99 = None.
  Proof. vm_compute; split; reflexivity. Qed.
  Example query_uf : query (app "f" [x]) = Some (Symbol "U").
  Proof. vm_compute; reflexivity. Qed.
  Example query_ill_typed : query (app "f" [Symbol "0"]) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example query_unknown : query (app "mystery" [p]) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_sort : query (Symbol "@List") = Some (Symbol "Type").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_empty : query (Symbol "@list.nil") = Some (Symbol "@List").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_canonical_sort :
    query (Symbol "eo::List") = Some (Symbol "Type").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_canonical_empty :
    query (Symbol "eo::List::nil") = Some (Symbol "@List").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_canonical_list :
    query (app "eo::List::cons" [p; Symbol "1"]) = Some (Symbol "@List").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_heterogeneous :
    query (app "@list" [p; Symbol "1"; x; Symbol "1/2"]) = Some (Symbol "@List").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_nested :
    query (app "@list" [app "@list" [p]; Symbol "@list.nil"]) = Some (Symbol "@List").
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_unknown : query (app "@list" [Symbol "unknown"]) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example query_metadata_unknown_application :
    query (app "@list" [app "mystery" [p]]) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example query_rational_kind : query (Symbol "1/1") = Some (Symbol "Real").
  Proof. vm_compute; reflexivity. Qed.
  Example query_decimal_kind : query (Symbol "1.0") = Some (Symbol "Real").
  Proof. vm_compute; reflexivity. Qed.
  Example query_malformed_rational : query (Symbol "1/0") = None.
  Proof. vm_compute; reflexivity. Qed.
  Example query_real_object_unsupported :
    query (app "+" [Symbol "1/1"; Symbol "2/1"]) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example metadata_name_collision :
    names_wf sorts funcs (Naming [(0, "@List")] []) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example literal_name_collision :
    names_wf sorts funcs (Naming [] [(0, "1/1")]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example query_function : query (Symbol "f") = Some (app "->" [Symbol "U"; Symbol "U"]).
  Proof. vm_compute; reflexivity. Qed.
  Example query_sort : query (Symbol "U") = Some (Symbol "Type").
  Proof. vm_compute; reflexivity. Qed.
  Example query_function_type : query (app "->" [Symbol "U"; Symbol "U"]) =
    Some (Symbol "Type").
  Proof. vm_compute; reflexivity. Qed.
  Example reserved_name_rejected :
    names_wf sorts funcs (Naming [(0, "U")] [(0, "true")]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example duplicate_name_rejected :
    names_wf sorts funcs (Naming [(0, "U")] [(0, "U")]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example duplicate_index_rejected :
    names_wf sorts funcs (Naming [] [(0, "x"); (0, "y")]) = false.
  Proof. vm_compute; reflexivity. Qed.
  Example sort_index_wrap_rejected :
    encode_sort sorts names (Typ.Tindex 9223372036854775808%N) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example malformed_atom_rejected :
    encode_atom sorts funcs (atoms.[10 <- Atom.Abop Atom.BO_Zplus 2 1]) names 40 10 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example function_bounds_rejected :
    encode_atom sorts funcs (atoms.[4 <- Atom.Aapp 99 []]) names 40 4 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example function_arity_rejected :
    encode_atom sorts funcs (atoms.[4 <- Atom.Aapp 2 []]) names 40 4 = None.
  Proof. vm_compute; reflexivity. Qed.
  Example cyclic_form_rejected :
    encode_literal sorts funcs atoms (forms.[9 <- Form.Fiff (Lit.lit 9) (Lit.lit 5)])
      names 40 (Lit.lit 9) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example non_boolean_atom_rejected :
    encode_literal sorts funcs atoms (forms.[9 <- Form.Fatom 8]) names 40 (Lit.lit 9) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example unknown_form_rejected :
    encode_literal sorts funcs atoms (forms.[9 <- Form.FbbT 8 []]) names 40 (Lit.lit 9) = None.
  Proof. vm_compute; reflexivity. Qed.
  Example low_fuel_rejected : encode_literal sorts funcs atoms forms names 0 (Lit.lit 2) = None.
  Proof. vm_compute; reflexivity. Qed.

  Definition contra := Payload "contra" [] [p; app "not" [p]] (Symbol "false") [].
  Example generated_contra : run contra [[Lit.lit 5]; [Lit.nlit 5]] = Some [].
  Proof. vm_compute; reflexivity. Qed.
  Example generated_premise_change : run contra [[Lit.lit 6]; [Lit.nlit 5]] = None.
  Proof. vm_compute; reflexivity. Qed.
  Example generated_premise_order : run contra [[Lit.nlit 5]; [Lit.lit 5]] = None.
  Proof. vm_compute; reflexivity. Qed.
  Example generated_unknown_rule : run (Payload "not_a_rule" [] [] p [Lit.lit 5]) [] = None.
  Proof. vm_compute; reflexivity. Qed.
  Example generated_result_change : run
    (Payload "contra" [] [p; app "not" [p]] (Symbol "false") [Lit.lit 5])
    [[Lit.lit 5]; [Lit.nlit 5]] = None.
  Proof. vm_compute; reflexivity. Qed.
  Example generated_refl : run (Payload "refl" [x] [] (app "=" [x; x]) [Lit.lit 14]) [] =
    Some [Lit.lit 14].
  Proof. vm_compute; reflexivity. Qed.
  Example mandatory_semantic_gate :
    EunoiaChecker.check_step run (fun _ _ (_ : unit) => false) (PArray.length forms)
      (EunoiaChecker.initial 1)
      (@EunoiaChecker.Step rule_payload unit 0 []
        (Payload "refl" [x] [] (app "=" [x; x]) [Lit.lit 14]) [Lit.lit 14] tt) = None.
  Proof. vm_compute; reflexivity. Qed.

  Definition resolve_p := EunoiaBridge.Witness 3
    (Checker_Ext.Res 2 ((PArray.make 2 0).[1 <- 1])).
  Definition contra_trace :=
    [@EunoiaChecker.Step rule_payload EunoiaBridge.witness
      2 [0; 1] contra [] resolve_p].
  Example checked_contra : checked_checker sorts funcs atoms forms names 40 3
    [[Lit.lit 5]; [Lit.nlit 5]] [p; app "not" [p]]
    [(0, [Lit.lit 5]); (1, [Lit.nlit 5])] contra_trace 2 = true.
  Proof. vm_compute; reflexivity. Qed.
  Example checked_changed_root : checked_checker sorts funcs atoms forms names 40 3
    [[Lit.lit 5]; [Lit.nlit 5]] [q; app "not" [p]]
    [(0, [Lit.lit 5]); (1, [Lit.nlit 5])] contra_trace 2 = false.
  Proof. vm_compute; reflexivity. Qed.

  Example singleton_premise_list_type :
    query (app "and" [app "=" [x; x]]) = Some (Symbol "Bool").
  Proof. vm_compute; reflexivity. Qed.

  Example generated_single_premise_congruence :
    CpcGenerated.derive 500 query "cong"
      [app "not" [app "=" [x; x]]]
      [app "=" [app "=" [x; x]; Symbol "true"]] =
    Some (app "=" [app "not" [app "=" [x; x]]; app "not" [Symbol "true"]]).
  Proof. vm_compute; reflexivity. Qed.
End Examples.

Print Assumptions term_eqb_spec.
Print Assumptions binds_spec.
Print Assumptions bind_terms_spec.
Print Assumptions eval_with_binding.
Print Assumptions check_step_binding.
Print Assumptions checker_correct.
Print Assumptions checker_root_binding.
Print Assumptions checked_checker_correct.

End EunoiaAdapter.
