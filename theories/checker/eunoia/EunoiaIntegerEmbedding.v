(* Restricted rational intermediates in an otherwise integer proof. *)
From Stdlib Require Import List String Bool ZArith QArith Qround Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoArithmetic.
Import ListNotations.
Local Open Scope string_scope.
Module EunoiaIntegerEmbedding.
Definition app name xs := fold_left Apply xs (Symbol name).
Definition integer z := Symbol (EoArithmetic.integer_string z).
Fixpoint spine (t : term) (acc : list term) : term * list term :=
  match t with Symbol _ => (t,acc) | Apply f a => spine f (a::acc) end.
Fixpoint traverse {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x::rest => match f x, traverse f rest with
    | Some y,Some ys => Some (y::ys) | _,_ => None end
  end.
Fixpoint requires_embedding (t : term) : bool :=
  match t with
  | Symbol name =>
    String.eqb name "to_real" || String.eqb name "to_int" ||
    match EoArithmetic.parse name with
    | Some (EoArithmetic.LRational _) | Some (EoArithmetic.LDecimal _ _) => true
    | _ => false end
  | Apply f a => requires_embedding f || requires_embedding a
  end.
Fixpoint fold_literal (op : EoArithmetic.literal -> EoArithmetic.literal -> option EoArithmetic.literal)
    (value : EoArithmetic.literal) (rest : list EoArithmetic.literal) :=
  match rest with [] => Some value | x::xs =>
    match op value x with Some y => fold_literal op y xs | None => None end end.
Fixpoint ground (fuel : nat) (t : term) : option EoArithmetic.literal :=
  match fuel with
  | O => None
  | S k =>
    let '(head,args) := spine t [] in
    match head, traverse (ground k) args with
    | Symbol name,Some values =>
      if String.eqb name "to_real" then
        match values with [EoArithmetic.LInteger z] =>
          Some (EoArithmetic.LRational (inject_Z z)) | _ => None end
      else if String.eqb name "to_int" then
        match values with
        | [EoArithmetic.LRational q] => Some (EoArithmetic.LInteger (Qfloor q))
        | [EoArithmetic.LDecimal n d] =>
          Some (EoArithmetic.LInteger (Qfloor (EoArithmetic.value (EoArithmetic.LDecimal n d))))
        | _ => None end
      else if String.eqb name "+" || String.eqb name "*" then
        match values with
        | a::b::rest => fold_literal
            (if String.eqb name "+" then EoArithmetic.add else EoArithmetic.multiply) a (b::rest)
        | _ => None end
      else if String.eqb name "-" then
        match values with
        | [a] => Some (EoArithmetic.negate a)
        | [a;b] => EoArithmetic.add a (EoArithmetic.negate b)
        | _ => None end
      else if String.eqb name "/" then
        match values with [a;b] => EoArithmetic.rational_division a b | _ => None end
      else match args with [] => EoArithmetic.parse name | _ => None end
    | _,_ => None end
  end.
Inductive view := Plain (t : term) | Fraction (numerator : term) (denominator : positive).
Definition fraction_of_literal v :=
  let q := Qred (EoArithmetic.value v) in Fraction (integer (Qnum q)) (Qden q).
Definition scale (denominator : positive) (numerator : term) :=
  if Pos.eqb denominator 1%positive then numerator
  else app "*" [integer (Zpos denominator);numerator].
Definition add_fraction a b :=
  match a,b with
  | Fraction x d,Fraction y e =>
    if Pos.eqb d e then Some (Fraction (app "+" [x;y]) d)
    else Some (Fraction (app "+" [scale e x;scale d y]) (Pos.mul d e))
  | _,_ => None end.
Definition mul_fraction a b :=
  match a,b with
  | Fraction x d,Fraction y e => Some (Fraction (app "*" [x;y]) (Pos.mul d e))
  | _,_ => None end.
Definition negate_fraction a := match a with
  | Fraction n d => Some (Fraction (app "-" [n]) d) | _ => None end.
Fixpoint fold_view (op : view -> view -> option view) value rest :=
  match rest with [] => Some value | x::xs =>
    match op value x with Some y => fold_view op y xs | None => None end end.
Definition plain_terms xs := traverse (fun v => match v with Plain t => Some t | _ => None end) xs.
Definition ordinary_app name xs :=
  if String.eqb name "@purify" then match xs with [x] => Some (Plain x) | _ => None end
  else if String.eqb name "+" || String.eqb name "*" then
    match xs with
    | a::b::c::rest =>
      let fix chain x xs := match xs with [] => x | y::ys => app name [x;chain y ys] end in
      Some (Plain (chain a (b::c::rest)))
    | _ => Some (Plain (app name xs)) end
  else Some (Plain (app name xs)).
Definition compare_fraction name a b :=
  match a,b with
  | Fraction x d,Fraction y e =>
    if Pos.eqb d e then Some (Plain (app name [x;y]))
    else Some (Plain (app name [scale e x;scale d y]))
  | _,_ => None end.
Definition divide_fraction (a : view) (divisor : EoArithmetic.literal) :=
  let q := Qred (EoArithmetic.value divisor) in
  match a,Qnum q with
  | Fraction n d,Zpos p => Some (Fraction (scale (Qden q) n) (Pos.mul d p))
  | Fraction n d,Zneg p => Some (Fraction (app "-" [scale (Qden q) n]) (Pos.mul d p))
  | _,_ => None end.
Fixpoint reduce (query : term -> option term) (fuel : nat) (t : term) : option view :=
  match fuel with
  | O => None
  | S k =>
    let '(head,args) := spine t [] in
    match head,traverse (reduce query k) args with
    | Symbol name,Some values =>
      if String.eqb name "@purify" then
        match values with [v] => Some v | _ => None end
      else if String.eqb name "to_real" then
        match args,values with
        | [raw],[Plain n] =>
          match query raw with Some (Symbol "Int") => Some (Fraction n 1%positive) | _ => None end
        | _,_ => None end
      else if String.eqb name "to_int" then
        match args,values with
        | [raw],[Fraction n d] =>
          match query raw with
          | Some (Symbol "Real") =>
            if Pos.eqb d 1%positive then Some (Plain n) else
              match ground k raw with
              | Some v => Some (Plain (integer (Qfloor (EoArithmetic.value v))))
              | None => None end
          | _ => None end
        | _,_ => None end
      else match plain_terms values with
      | Some xs =>
        match args,EoArithmetic.parse name with
        | [],Some (EoArithmetic.LRational q) => Some (fraction_of_literal (EoArithmetic.LRational q))
        | [],Some (EoArithmetic.LDecimal n d) => Some (fraction_of_literal (EoArithmetic.LDecimal n d))
        | _,_ => ordinary_app name xs end
      | None =>
        if String.eqb name "+" || String.eqb name "*" then
          match values with a::b::rest =>
            fold_view (if String.eqb name "+" then add_fraction else mul_fraction) a (b::rest)
          | _ => None end
        else if String.eqb name "-" then
          match values with
          | [a] => negate_fraction a
          | [a;b] => match negate_fraction b with Some nb => add_fraction a nb | None => None end
          | _ => None end
        else if String.eqb name "/" then
          match args,values with
          | [_;raw],[a;Fraction _ _] =>
            match ground k raw with Some divisor => divide_fraction a divisor | None => None end
          | _,_ => None end
        else if existsb (String.eqb name) ["=";"<";"<=";">";">="] then
          match values with [a;b] => compare_fraction name a b | _ => None end
        else None
      end
    | _,_ => None end
  end.
Definition normalize (ordinary : nat -> term -> option term) query fuel t :=
  if requires_embedding t then
    match reduce query fuel t with Some (Plain u) => Some u | _ => None end
  else ordinary fuel t.
Lemma normalize_ordinary : forall ordinary query fuel t,
  requires_embedding t = false -> normalize ordinary query fuel t = ordinary fuel t.
Proof. intros ordinary query fuel t H; unfold normalize; now rewrite H. Qed.
Lemma positive_denominator : forall d : positive, (0 < Zpos d)%Z.
Proof. intros; lia. Qed.
Lemma fraction_eq_cross : forall n m d e,
  (n # d == m # e)%Q <-> (n * Zpos e = m * Zpos d)%Z.
Proof. reflexivity. Qed.
Lemma fraction_le_cross : forall n m d e,
  (n # d <= m # e)%Q <-> (n * Zpos e <= m * Zpos d)%Z.
Proof. reflexivity. Qed.
Lemma fraction_lt_cross : forall n m d e,
  (n # d < m # e)%Q <-> (n * Zpos e < m * Zpos d)%Z.
Proof. reflexivity. Qed.
Lemma fraction_eq_same : forall n m d,
  (n # d == m # d)%Q <-> n = m.
Proof. intros; unfold Qeq; simpl; assert (0 < Zpos d)%Z by lia; nia. Qed.
Lemma fraction_le_same : forall n m d,
  (n # d <= m # d)%Q <-> (n <= m)%Z.
Proof. intros; unfold Qle; simpl; assert (0 < Zpos d)%Z by lia; nia. Qed.
Lemma fraction_lt_same : forall n m d,
  (n # d < m # d)%Q <-> (n < m)%Z.
Proof. intros; unfold Qlt; simpl; assert (0 < Zpos d)%Z by lia; nia. Qed.
Lemma floor_integer : forall n : Z, Qfloor (n # 1) = n.
Proof. intro n; cbn [Qfloor]; apply Z.div_1_r. Qed.
Lemma fraction_add : forall n m d e,
  ((n # d) + (m # e) == ((Zpos e * n + Zpos d * m) # (Pos.mul d e)))%Q.
Proof.
  intros n m d e.
  change (((n * Zpos e + m * Zpos d) * Zpos (Pos.mul d e) =
    (Zpos e * n + Zpos d * m) * Zpos (Pos.mul d e))%Z).
  ring.
Qed.
Lemma fraction_mul : forall n m d e,
  ((n # d) * (m # e) == ((n * m) # (Pos.mul d e)))%Q.
Proof. reflexivity. Qed.
Lemma fraction_neg : forall n d,
  (- (n # d) == ((-n) # d))%Q.
Proof. reflexivity. Qed.
End EunoiaIntegerEmbedding.
