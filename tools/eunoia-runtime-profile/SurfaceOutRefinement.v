From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
Import ListNotations.
Open Scope string_scope.

(* Frozen pre-sharing definition from c79eeba, to establish pointwise
   preservation for arbitrary nil/type queries, operators, fuel and terms. *)
Fixpoint surface_out_reference (nilof : nil_query) (typeof : term -> option term) (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_out_reference nilof typeof k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd with
      | Symbol name =>
          match (match xs with [] => named name ops | x :: _ =>
            match surface_out_reference nilof typeof k ops x with
            | Some y => nilof name (typeof y) | None => None end end), xs with
          | Some terminator, _ :: _ =>
              match list_elements hd terminator t with
              | Some ys => option_map (apply_many hd) (visit ys)
              | None => None
              end
          | None, _ :: _ => if nil_known nilof name then None else option_map (apply_many hd) (visit xs)
          | _, _ => option_map (apply_many hd) (visit xs)
          end
      | _ => None
      end
  end.

Definition visit_terms (f : term -> option term) : list term -> option (list term) :=
  fix visit (xs : list term) := match xs with
  | [] => Some []
  | x :: tl => match f x, visit tl with
    | Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.
Lemma visit_terms_pointwise f g :
  (forall t, f t = g t) -> forall xs, visit_terms f xs = visit_terms g xs.
Proof.
  intros H xs. induction xs as [|x xs IH]; cbn; [reflexivity|].
  rewrite H, IH. reflexivity.
Qed.

Theorem surface_out_with_refinement nilof typeof fuel ops :
  forall t, surface_out_with nilof typeof fuel ops t =
            surface_out_reference nilof typeof fuel ops t.
Proof.
  induction fuel as [|k IH]; intro t; [reflexivity|].
  cbn [surface_out_with surface_out_reference].
  fold (visit_terms (surface_out_with nilof typeof k ops)).
  fold (visit_terms (surface_out_reference nilof typeof k ops)).
  destruct (unapply t []) as [hd xs]. destruct hd as [name | f a]; [|reflexivity].
  destruct xs as [|x tl].
  - cbn. destruct (named name ops); reflexivity.
  - rewrite IH. destruct (surface_out_reference nilof typeof k ops x) as [y|] eqn:Hx.
    + destruct (nilof name (typeof y)) as [z|].
      * destruct (list_elements (Symbol name) z t) as [ys|]; [|reflexivity].
        rewrite (visit_terms_pointwise _ _ IH). reflexivity.
      * destruct (nil_known nilof name); [reflexivity|].
        cbn [visit_terms]. rewrite Hx, (visit_terms_pointwise _ _ IH).
        destruct (visit_terms (surface_out_reference nilof typeof k ops) tl); reflexivity.
    + destruct (nil_known nilof name); [reflexivity|].
      cbn [visit_terms]. rewrite Hx. reflexivity.
Qed.
Print Assumptions visit_terms_pointwise.
Print Assumptions surface_out_with_refinement.
