From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
Import ListNotations.
Open Scope string_scope.
(* Frozen strict-query definitions; the optimized variants are definitionally equal. *)

Definition native_with_nils_reference (nilof : nil_query) (typeof : term -> option term) (extra : primitive_hook) (ops : list (string * term))
    (name : string) (args : list term) : option term :=
  let list_of op t :=
    match op with Symbol s => match nil_list_value nilof s (typeof t) with Some terminator => list_elements op terminator t | _ => None end | _ => None end in
  let rebuild op xs :=
    match op with Symbol s => option_map (fun terminator => make_list op terminator xs) (match xs with
      | x :: _ => nilof s (typeof x)
      | [] => match args with
          | _ :: witness :: _ =>
              if String.eqb name "eo::list_repeat" then nilof s (typeof witness)
              else nil_list_value nilof s (typeof witness)
          | _ => None end end) | _ => None end in
  match name, args with
  | "eo::not", [a] => option_map (fun b => bool_term (negb b)) (as_bool a)
  | "eo::and", [a; b] | "eo::or", [a; b] | "eo::xor", [a; b] =>
      match as_bool a, as_bool b with
      | Some x, Some y => Some (bool_term (if String.eqb name "eo::and" then x && y else if String.eqb name "eo::or" then x || y else xorb x y))
      | _, _ => extra name args
      end
  | "eo::is_bool", [a] => Some (bool_term (match as_bool a with Some _ => true | _ => false end))
  | "eo::is_z", [a] => match extra "eo::supports" [Symbol name] with
      | Some (Symbol "true") => extra name args | _ => Some (bool_term (is_integer a)) end
  | "eo::is_q", [a] => match extra "eo::supports" [Symbol name] with
      | Some (Symbol "true") => extra name args | _ => Some (bool_term (is_rational a)) end
  | "eo::is_bin", [Symbol s] => Some (bool_term (prefix "#b" s || prefix "#x" s))
  | "eo::is_str", [Symbol s] => Some (bool_term (prefix """" s))
  | "eo::is_bin", [_] | "eo::is_str", [_] => Some (bool_term false)
  | "eo::list_rev", [op; a] => match list_of op a with Some xs => rebuild op (rev xs) | _ => None end
  | "eo::list_len", [op; a] => option_map (fun xs => nat_term (List.length xs)) (list_of op a)
  | "eo::list_nth", [op; a; i] =>
      match list_of op a, as_nat i with Some xs, Some n => nth_error xs n | _, _ => None end
  | "eo::list_find", [op; a; x] => option_map (fun xs => find_index x xs 0) (list_of op a)
  | "eo::list_erase", [op; a; x] =>
      match list_of op a with Some xs => rebuild op (match erase_first x xs with Some ys => ys | _ => xs end) | _ => None end
  | "eo::list_erase_all", [op; a; x] =>
      match list_of op a with Some xs => rebuild op (filter (fun y => negb (term_eqb x y)) xs) | _ => None end
  | "eo::list_setof", [op; a] => match list_of op a with Some xs => rebuild op (setof xs) | _ => None end
  | "eo::list_concat", [op; a; b] | "eo::list_diff", [op; a; b] | "eo::list_inter", [op; a; b] =>
      match list_of op a, list_of op b with
      | Some xs, Some ys => rebuild op (if String.eqb name "eo::list_concat" then (xs ++ ys)%list else multiset_filter (String.eqb name "eo::list_inter") xs ys)
      | _, _ => None
      end
  | "eo::list_minclude", [op; a; b] | "eo::list_meq", [op; a; b] =>
      match list_of op a, list_of op b with
      | Some xs, Some ys => Some (bool_term (multiset_include xs ys && (if String.eqb name "eo::list_meq" then multiset_include ys xs else true)))
      | _, _ => None
      end
  | "eo::list_singleton_elim", [op; a] =>
      match list_of op a with Some [x] => Some x | Some _ => Some a | _ => None end
  | "eo::list_singleton_intro", [op; a] => match list_of op a with Some _ => Some a | _ => rebuild op [a] end
  | "eo::list_repeat", [op; a; n] => match as_nat n with Some k => rebuild op (repeat a k) | _ => None end
  | "eo::cons", [op; a; tl] => match list_of op tl with Some xs => rebuild op (a :: xs) | _ => None end
  | "eo::nil", [Symbol op; ty] => nil_list_value nilof op (Some ty)
  | _, _ => extra name args
  end.

Lemma native_with_nils_refinement : forall nilof typeof extra ops name args,
 native_with_nils nilof typeof extra ops name args =
 native_with_nils_reference nilof typeof extra ops name args.
Proof. reflexivity. Qed.
Print Assumptions native_with_nils_refinement.


Fixpoint surface_in_reference (nilof : nil_query) (typeof : term -> option term) (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_in_reference nilof typeof k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd, visit xs with
      | Symbol name, Some ys =>
          match ys, (match xs with [] => named name ops | x :: _ => nilof name (typeof x) end) with
          | [], _ => Some hd
          | _, Some terminator => Some (make_list hd terminator ys)
          | _, None => if nil_known nilof name then None else Some (apply_many hd ys)
          end
      | _, _ => None
      end
  end.


Lemma surface_in_with_refinement : forall nilof typeof fuel ops t,
 surface_in_with nilof typeof fuel ops t = surface_in_reference nilof typeof fuel ops t.
Proof. reflexivity. Qed.
Print Assumptions surface_in_with_refinement.

Fixpoint match_pattern_with_reference (nilof : nil_query) (typeof : term -> option term) (p : pattern) (t : term) (env : bindings)
    : option bindings :=
  match p with
  | PNil op => match nil_list_value nilof op (typeof t) with
      | Some z => if term_eqb z t then Some env else None | None => None end
  | PVar n =>
      match lookup n env with
      | None => Some ((n, t) :: env)
      | Some u => if term_eqb t u then Some env else None
      end
  | PSymbol s =>
      match t with
      | Symbol r => if String.eqb s r then Some env else None
      | _ => None
      end
  | PApply f a =>
      match t with
      | Apply g b =>
          match match_pattern_with_reference nilof typeof f g env with
          | Some env' => match_pattern_with_reference nilof typeof a b env'
          | None => None
          end
      | _ => None
      end
  end.

Lemma match_pattern_with_refinement : forall nilof typeof p t env,
 match_pattern_with nilof typeof p t env = match_pattern_with_reference nilof typeof p t env.
Proof. reflexivity. Qed.
Print Assumptions match_pattern_with_refinement.
