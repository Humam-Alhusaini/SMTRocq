(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)
From Stdlib Require Import String Ascii List Bool ZArith QArith Qround DecimalString Lia Zpow_alt.
From SMTCoq.checker.eunoia Require Import EoSyntax.
Import ListNotations.
Local Open Scope string_scope.

(** Eunoia meta-language literal computations, pinned to Ethos
    f97393ea55f03653689e104d0e9c9010ee17780c. This module gives no interpretation
    to object formulas and establishes no CPC rule soundness. *)
Module EoArithmetic.

Inductive literal :=
| LInteger : Z -> literal
| LRational : Q -> literal
(* Unscaled decimal numerator and number of fractional digits. Keeping this
   category matters: Ethos is_q rejects DECIMAL, even when it is integral. *)
| LDecimal : Z -> nat -> literal.

Definition unsigned (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => option_map Z.of_uint (NilEmpty.uint_of_string s)
  end.

(* Split only once; the parsers of each component consume their entire input. *)
Fixpoint split_at (c : ascii) (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String a tl =>
      if Ascii.eqb c a then Some ("", tl)
      else option_map (fun p => (String a (fst p), snd p)) (split_at c tl)
  end.

Definition pow10 (n : nat) : Z := Zpower_alt 10 (Z.of_nat n).
Definition signed (negative : bool) (n : Z) := if negative then Z.opp n else n.
Definition fraction (n d : Z) : option Q :=
  match d with
  | Zpos p => Some (Qred (n # p))
  | _ => None
  end.

Definition parse_unsigned (negative : bool) (s : string) : option literal :=
  match split_at "/" s with
  | Some (a, b) =>
      match unsigned a, unsigned b with
      | Some n, Some d => option_map LRational (fraction (signed negative n) d)
      | _, _ => None
      end
  | None =>
      match split_at "." s with
      | Some (a, b) =>
          (* Ethos also lexes -.digits as a negative decimal. *)
          let whole := if negative && String.eqb a "" then Some 0%Z else unsigned a in
          match whole, unsigned b with
          | Some n, Some m => Some (LDecimal
              (signed negative (n * pow10 (String.length b) + m)%Z) (String.length b))
          | _, _ => None
          end
      | None => option_map (fun n => LInteger (signed negative n)) (unsigned s)
      end
  end.

Definition parse (s : string) : option literal :=
  match s with
  | String "-" tl => parse_unsigned true tl
  | _ => parse_unsigned false s
  end.

Definition parse_term (t : term) : option literal :=
  match t with Symbol s => parse s | _ => None end.
Definition integer_string (n : Z) : string :=
  NilZero.string_of_int (Z.to_int n).
Definition rational_string (q : Q) : string :=
  let r := Qred q in
  integer_string (Qnum r) ++ "/" ++ integer_string (Zpos (Qden r)).

Fixpoint zeroes (n : nat) : string :=
  match n with O => "" | S k => String "0" (zeroes k) end.
Fixpoint reduce_decimal (n : Z) (scale : nat) : Z * nat :=
  match scale with
  | O => (n, O)
  | S k => if Z.eqb (Z.modulo n 10) 0 then reduce_decimal (Z.div n 10) k
           else (n, S k)
  end.
Definition decimal_string (unscaled : Z) (digits : nat) : string :=
  let '(n, scale) := reduce_decimal unscaled digits in
  let places := Nat.max 1 scale in
  let magnitude := (Z.abs n * pow10 (places - scale))%Z in
  let divisor := pow10 places in
  let whole := integer_string (Z.div magnitude divisor) in
  let part := integer_string (Z.modulo magnitude divisor) in
  (if Z.ltb n 0 then "-" else "") ++ whole ++ "." ++
    zeroes (places - String.length part) ++ part.
Definition render (v : literal) : term := Symbol (
  match v with
  | LInteger n => integer_string n
  | LRational q => rational_string q
  | LDecimal n k => decimal_string n k
  end).
Definition normalize (t : term) : option term := option_map render (parse_term t).
Definition value (v : literal) : Q :=
  match v with
  | LInteger n => inject_Z n
  | LRational q => q
  | LDecimal n k => n # (Z.to_pos (pow10 k))
  end.
Definition boolean (b : bool) : term := Symbol (if b then "true" else "false").

Definition negate (x : literal) : literal :=
  match x with
  | LInteger n => LInteger (-n)
  | LRational q => LRational (Qred (-q))
  | LDecimal n k => LDecimal (-n) k
  end.
Definition add (x y : literal) : option literal :=
  match x, y with
  | LInteger a, LInteger b => Some (LInteger (a + b))
  | LRational a, LRational b => Some (LRational (Qred (a + b)))
  | LDecimal a k, LDecimal b l =>
      let m := Nat.max k l in
      Some (LDecimal (a * pow10 (m-k) + b * pow10 (m-l)) m)
  | _, _ => None
  end.
Definition multiply (x y : literal) : option literal :=
  match x, y with
  | LInteger a, LInteger b => Some (LInteger (a * b))
  | LRational a, LRational b => Some (LRational (Qred (a * b)))
  | LDecimal a k, LDecimal b l => Some (LDecimal (a * b) (k+l))
  | _, _ => None
  end.
Definition same_kind (x y : literal) : bool :=
  match x, y with
  | LInteger _, LInteger _ | LRational _, LRational _ | LDecimal _ _, LDecimal _ _ => true
  | _, _ => false
  end.

(* Z.div itself has the wrong remainder convention for a negative divisor. *)
Definition euclidean_quotient (a b : Z) : Z :=
  if Z.ltb b 0 then (- (Z.div a (-b)))%Z else Z.div a b.
Definition euclidean_remainder (a b : Z) : Z := Z.modulo a (Z.abs b).
Definition integer_division (remainder : bool) (x y : literal) : option literal :=
  match x, y with
  | LInteger a, LInteger b =>
      if Z.eqb b 0 then None else Some (LInteger
        (if remainder then euclidean_remainder a b else euclidean_quotient a b))
  | _, _ => None
  end.
Definition rational_division (x y : literal) : option literal :=
  if same_kind x y then
    if Qeq_bool (value y) 0 then None
    else Some (LRational (Qred (value x / value y)))
  else None.
Definition greater (x y : literal) : option term :=
  if same_kind x y then
    Some (boolean (match Qcompare (value x) (value y) with Gt => true | _ => false end))
  else None.

(* Native pow accepts a NUMERAL exponent fitting uint32_t, including zero. *)
Definition power (x y : literal) : option literal :=
  match y with
  | LInteger e =>
      if (Z.leb 0 e && Z.leb e 4294967295)%bool then
        match x with
        | LInteger a => Some (LInteger (Zpower_alt a e))
        | LRational a => Some (LRational (Qred (Qpower a e)))
        | LDecimal a k =>
            let '(a, k) := reduce_decimal a k in
            match k with
            | O => Some (LDecimal (Zpower_alt a e) O)
            | S _ => Some (LDecimal (Zpower_alt a e) (k * Z.to_nat e))
            end
        end
      else None
  | _ => None
  end.

(* Each iteration divides by a base >= 2. Bit length bounds the iteration
   count without converting the potentially huge operand into a unary nat. *)
Fixpoint floor_log_loop (fuel : nat) (base remaining count : Z) : option Z :=
  if Z.ltb remaining base then Some count else
  match fuel with
  | O => None
  | S k => floor_log_loop k base (Z.div remaining base) (count+1)
  end.
Definition floor_log (x y : literal) : option literal :=
  match x with
  | LInteger base =>
      let n := Qfloor (value y) in
      if (Z.leb base 1 || Z.leb n 0)%bool then Some (LInteger 0) else
      option_map LInteger (floor_log_loop (Z.to_nat (Z.log2 n + 1)) base n 0)
  | _ => None
  end.

Definition unary (f : literal -> option term) (xs : list term) : option term :=
  match xs with
  | [x] => match parse_term x with Some a => f a | None => None end
  | _ => None
  end.
Definition binary (f : literal -> literal -> option term) (xs : list term) : option term :=
  match xs with
  | [x;y] => match parse_term x, parse_term y with
             | Some a, Some b => f a b | _, _ => None end
  | _ => None
  end.
Definition lift (f : literal -> literal -> option literal) :=
  fun x y => option_map render (f x y).
Fixpoint fold_literals (f : literal -> literal -> option literal)
    (acc : literal) (xs : list term) : option literal :=
  match xs with
  | [] => Some acc
  | x :: tl =>
      match parse_term x with
      | Some a => match f acc a with Some b => fold_literals f b tl | None => None end
      | None => None
      end
  end.
Definition nary (f : literal -> literal -> option literal) (xs : list term) : option term :=
  match xs with
  | x :: y :: tl =>
      match parse_term x with
      | Some a => option_map render (fold_literals f a (y::tl))
      | None => None
      end
  | _ => None
  end.

Definition digit (c : ascii) : bool :=
  (Nat.leb 48 (nat_of_ascii c) && Nat.leb (nat_of_ascii c) 57)%bool.
Definition numeric_candidate (s : string) : bool :=
  match s with
  | String "-" (String c _) => digit c || Ascii.eqb c "."
  | String c _ => digit c
  | _ => false
  end.
(* Valid non-literals answer false to kind predicates. A malformed numeric
   token must not become a successful false side condition. *)
Definition kind_predicate (rational : bool) (xs : list term) : option term :=
  match xs with
  | [Symbol s] =>
      match parse s with
      | Some (LInteger _) => Some (boolean (negb rational))
      | Some (LRational _) => Some (boolean rational)
      | Some (LDecimal _ _) => Some (boolean false)
      | None => if numeric_candidate s then None else Some (boolean false)
      end
  | [Apply _ _] => Some (boolean false)
  | _ => None
  end.

Definition names : list string :=
  ["eo::is_z"; "eo::is_q"; "eo::add"; "eo::mul"; "eo::neg";
   "eo::is_neg"; "eo::gt"; "eo::zdiv"; "eo::zmod"; "eo::qdiv";
   "eo::to_z"; "eo::to_q"; "eo::pow"; "eo::log"].
Definition supports (name : string) : bool := existsb (String.eqb name) names.
Definition eval (name : string) (xs : list term) : option term :=
  match name with
  | "eo::is_z" => kind_predicate false xs
  | "eo::is_q" => kind_predicate true xs
  | "eo::add" => nary add xs
  | "eo::mul" => nary multiply xs
  | "eo::neg" => unary (fun a => Some (render (negate a))) xs
  | "eo::is_neg" => unary (fun a => Some (boolean (Z.ltb (Qnum (value a)) 0))) xs
  | "eo::gt" => binary greater xs
  | "eo::zdiv" => binary (lift (integer_division false)) xs
  | "eo::zmod" => binary (lift (integer_division true)) xs
  | "eo::qdiv" => binary (lift rational_division) xs
  | "eo::to_z" => unary (fun a => Some (render (LInteger (Qfloor (value a))))) xs
  | "eo::to_q" => unary (fun a => Some (render (LRational (Qred (value a))))) xs
  | "eo::pow" => binary (lift power) xs
  | "eo::log" => binary (lift floor_log) xs
  | _ => None
  end.

(* Use dispatch or test supports BEFORE eval. Failed recognized calls must
   never fall back to symbolic application, an identity, or a boolean false. *)
Inductive result := Unsupported | Failed | Value : term -> result.
Definition dispatch (name : string) (xs : list term) : result :=
  if supports name then match eval name xs with
    | Some t => Value t | None => Failed end
  else Unsupported.

Lemma unsupported_dispatch name xs :
  supports name = false -> dispatch name xs = Unsupported.
Proof. intros H. unfold dispatch. now rewrite H. Qed.
Lemma failed_dispatch name xs :
  supports name = true -> eval name xs = None -> dispatch name xs = Failed.
Proof. intros H E. unfold dispatch. now rewrite H, E. Qed.

Lemma euclidean_equation a b :
  b <> 0%Z ->
  a = (b * euclidean_quotient a b + euclidean_remainder a b)%Z.
Proof.
  intros H. unfold euclidean_quotient, euclidean_remainder.
  destruct (Z.ltb_spec b 0) as [Hneg|Hpos].
  - rewrite Z.abs_neq by lia.
    pose proof (Z.div_mod a (-b) ltac:(lia)). nia.
  - rewrite Z.abs_eq by lia.
    apply Z.div_mod. exact H.
Qed.

Lemma euclidean_remainder_bounds a b :
  b <> 0%Z -> (0 <= euclidean_remainder a b < Z.abs b)%Z.
Proof.
  intros H. unfold euclidean_remainder.
  apply Z.mod_pos_bound. now apply Z.abs_pos.
Qed.

Lemma zero_division_fails a :
  integer_division false (LInteger a) (LInteger 0) = None /\
  integer_division true (LInteger a) (LInteger 0) = None.
Proof. split; reflexivity. Qed.

End EoArithmetic.
