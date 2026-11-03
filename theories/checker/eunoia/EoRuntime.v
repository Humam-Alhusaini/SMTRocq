From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax.
Import ListNotations.
Open Scope string_scope.

Fixpoint lookup {A : Type} (n : nat) (xs : list (nat * A)) : option A :=
  match xs with
  | [] => None
  | (m, v) :: tl => if Nat.eqb n m then Some v else lookup n tl
  end.

Fixpoint named {A : Type} (s : string) (xs : list (string * A)) : option A :=
  match xs with
  | [] => None
  | (t, v) :: tl => if String.eqb s t then Some v else named s tl
  end.

Fixpoint match_pattern (p : pattern) (t : term) (env : bindings)
    : option bindings :=
  match p with
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
          match match_pattern f g env with
          | Some env' => match_pattern a b env'
          | None => None
          end
      | _ => None
      end
  end.

Fixpoint match_patterns (ps : list pattern) (ts : list term) (env : bindings)
    : option bindings :=
  match ps, ts with
  | [], [] => Some env
  | p :: pr, t :: tr =>
      match match_pattern p t env with
      | Some env' => match_patterns pr tr env'
      | None => None
      end
  | _, _ => None
  end.

Fixpoint instantiate (p : pattern) (env : bindings) : option term :=
  match p with
  | PVar n => lookup n env
  | PSymbol s => Some (Symbol s)
  | PApply f a =>
      match instantiate f env, instantiate a env with
      | Some g, Some b => Some (Apply g b)
      | _, _ => None
      end
  end.

(** Infer type binders from already matched value binders. Unbound binders
    are checked in a separate final pass, never treated as unconstrained. *)
Fixpoint infer_types (typeof : term -> option term) (bs : binder_types)
    (env : bindings) : option bindings :=
  match bs with
  | [] => Some env
  | (n, ty) :: tl =>
      match lookup n env with
      | None => infer_types typeof tl env
      | Some t =>
          match typeof t with
          | None => None
          | Some actual =>
              match match_pattern ty actual env with
              | None => None
              | Some env' => infer_types typeof tl env'
              end
          end
      end
  end.

Definition has_type (typeof : term -> option term) (t ty : term) : bool :=
  match typeof t with
  | Some actual => term_eqb actual ty
  | None => false
  end.

Definition check_binders (typeof : term -> option term) (bs : binder_types)
    (env : bindings) : bool :=
  forallb (fun b =>
    match lookup (fst b) env, instantiate (snd b) env with
    | Some t, Some ty => has_type typeof t ty
    | _, _ => false
    end) bs.

Definition typed_bindings (typeof : term -> option term) (bs : binder_types)
    (env : bindings) : option bindings :=
  match infer_types typeof bs env with
  | Some env' => if check_binders typeof bs env' then Some env' else None
  | None => None
  end.

Fixpoint match_types (typeof : term -> option term) (ps : list pattern)
    (ts : list term) (env : bindings) : option bindings :=
  match ps, ts with
  | [], [] => Some env
  | p :: pr, t :: tr =>
      match typeof t with
      | Some ty =>
          match match_pattern p ty env with
          | Some env' => match_types typeof pr tr env'
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Fixpoint select_case (cs : list program_case) (args : list term)
    (env : bindings) : option (bindings * expression) :=
  match cs with
  | [] => None
  | c :: tl =>
      match match_patterns (case_patterns c) args env with
      | Some env' => Some (env', case_body c)
      | None => select_case tl args env
      end
  end.

(** Fuel bounds all expression traversal and recursive helper calls.
    Once a case matches, a failed body does not fall through to later cases. *)
Fixpoint evaluate (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (env : bindings) (e : expression)
    : option term :=
  match fuel with
  | O => None
  | S k =>
    let ev := evaluate k typeof programs env in
    match e with
    | EVar n => lookup n env
    | ESymbol s => Some (Symbol s)
    | EApply f a =>
        match ev f, ev a with
        | Some g, Some b => Some (Apply g b)
        | _, _ => None
        end
    | EEq a b =>
        match ev a, ev b with
        | Some x, Some y => Some (Symbol (if term_eqb x y then "true" else "false"))
        | _, _ => None
        end
    | EIf c a b =>
        match ev c with
        | Some (Symbol s) =>
            if String.eqb s "true" then ev a
            else if String.eqb s "false" then ev b else None
        | _ => None
        end
    | ERequires a b body =>
        match ev a, ev b with
        | Some x, Some y => if term_eqb x y then ev body else None
        | _, _ => None
        end
    | ETypeof a => match ev a with Some t => typeof t | None => None end
    | ELet n value body =>
        match ev value with
        | Some t => evaluate k typeof programs ((n, t) :: env) body
        | None => None
        end
    | ECall name args =>
        let fix eval_args (xs : list expression) : option (list term) :=
          match xs with
          | [] => Some []
          | a :: tl =>
              match ev a, eval_args tl with
              | Some t, Some ts => Some (t :: ts)
              | _, _ => None
              end
          end in
        match named name programs, eval_args args with
        | Some p, Some ts =>
            match match_types typeof (program_inputs p) ts [] with
            | Some tenv =>
              match select_case (program_cases p) ts tenv with
              | Some (env', body) =>
                match typed_bindings typeof (program_binders p) env' with
                | Some checked =>
                  match evaluate k typeof programs checked body,
                        instantiate (program_output p) checked with
                  | Some t, Some ty => if has_type typeof t ty then Some t else None
                  | _, _ => None
                  end
                | None => None
                end
              | None => None
              end
            | None => None
            end
        | _, _ => None
        end
    end
  end.

Definition run_rule (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (args premises : list term) : option term :=
  match named name rules with
  | None => None
  | Some r =>
    match match_patterns (rule_arguments r ++ rule_premises r)
                         (args ++ premises) [] with
    | None => None
    | Some env =>
      (* Check lengths separately: arguments cannot consume premise slots. *)
      if Nat.eqb (List.length args) (List.length (rule_arguments r)) &&
         Nat.eqb (List.length premises) (List.length (rule_premises r)) &&
         forallb (fun t => has_type typeof t (Symbol "Bool")) premises then
        match typed_bindings typeof (rule_binders r) env with
        | None => None
        | Some checked =>
          let ev := evaluate fuel typeof programs checked in
          if forallb (fun req =>
              match ev (fst req), ev (snd req) with
              | Some x, Some y => term_eqb x y
              | _, _ => false
              end) (rule_requires r) then
            match ev (rule_conclusion r) with
            | Some t => if has_type typeof t (Symbol "Bool") then Some t else None
            | None => None
            end
          else None
        end
      else None
    end
  end.
