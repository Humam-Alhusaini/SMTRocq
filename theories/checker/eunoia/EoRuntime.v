From Stdlib Require Import String Ascii List Bool Arith DecimalString.
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

Fixpoint rename_symbols (aliases : list (string * term)) (t : term) : term :=
  match t with
  | Symbol s => match named s aliases with Some u => u | None => t end
  | Apply f a => Apply (rename_symbols aliases f) (rename_symbols aliases a)
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

(** Surface syntax stays curried. Internally an attributed variadic operator
    is a binary cons spine with its signature-declared terminator. No associativity or
    duplicate elimination of object formulas is performed. *)
Fixpoint unapply (t : term) (args : list term) : term * list term :=
  match t with
  | Apply f a => unapply f (a :: args)
  | _ => (t, args)
  end.
(** Unsupported operator elaboration rejects before helper case selection;
    otherwise a malformed known operator might accidentally select a fallback.
    Right/left associative and chainable syntax currently admits binary surface
    applications only; nil operators use the generated closed nil table. *)
Fixpoint surface_supported (blocked binary : list string) (t : term) : bool :=
  match t with
  | Symbol _ => true
  | Apply f a =>
      let '(hd, xs) := unapply t [] in
      let root_ok := match hd with
        | Symbol name => negb (existsb (String.eqb name) blocked) &&
            (if existsb (String.eqb name) binary then Nat.eqb (List.length xs) 2 else true)
        | _ => false end in
      (* Check the head spine without rechecking its partial arities. *)
      let fix children u := match u with
        | Symbol _ => true
        | Apply g b => children g && surface_supported blocked binary b
        end in
      root_ok && children t
  end.

Definition apply_many (f : term) (args : list term) := fold_left Apply args f.
Definition make_list (op terminator : term) (xs : list term) :=
  fold_right (fun x tl => Apply (Apply op x) tl) terminator xs.

Fixpoint list_elements (op terminator t : term) : option (list term) :=
  if term_eqb t terminator then Some [] else
  match t with
  | Apply (Apply f x) tl =>
      if term_eqb f op then
        option_map (cons x) (list_elements op terminator tl)
      else None
  | _ => None
  end.

Fixpoint surface_in (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_in k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd, visit xs with
      | Symbol name, Some ys =>
          match ys, named name ops with
          | [], _ => Some hd
          | _, Some terminator => Some (make_list hd terminator ys)
          | _, None => Some (apply_many hd ys)
          end
      | _, _ => None
      end
  end.

Fixpoint surface_out (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_out k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd with
      | Symbol name =>
          match named name ops, xs with
          | Some terminator, _ :: _ =>
              match list_elements hd terminator t with
              | Some ys => option_map (apply_many hd) (visit ys)
              | None => None
              end
          | _, _ => option_map (apply_many hd) (visit xs)
          end
      | _ => None
      end
  end.

Definition bool_term (b : bool) := Symbol (if b then "true" else "false").
Definition as_bool (t : term) : option bool :=
  match t with Symbol "true" => Some true | Symbol "false" => Some false | _ => None end.
Definition as_nat (t : term) : option nat :=
  match t with
  | Symbol EmptyString => None
  | Symbol s => option_map Nat.of_uint (NilEmpty.uint_of_string s)
  | _ => None
  end.
Definition nat_term (n : nat) := Symbol (NilZero.string_of_uint (Nat.to_uint n)).
Definition is_integer (t : term) : bool :=
  match t with
  | Symbol (String "-"%char s) => match as_nat (Symbol s) with Some _ => true | _ => false end
  | _ => match as_nat t with Some _ => true | _ => false end
  end.
Fixpoint split_slash (s acc : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c tl => if Ascii.eqb c "/"%char then Some (acc, tl) else split_slash tl (acc ++ String c EmptyString)
  end.
Definition is_rational (t : term) : bool :=
  match t with
  | Symbol s => match split_slash s EmptyString with
    | Some (n, d) => is_integer (Symbol n) && match as_nat (Symbol d) with Some (S _) => true | _ => false end
    | _ => false end
  | _ => false
  end.

Fixpoint erase_first (x : term) (xs : list term) : option (list term) :=
  match xs with
  | [] => None
  | y :: tl => if term_eqb x y then Some tl else option_map (cons y) (erase_first x tl)
  end.
Fixpoint multiset_include (xs ys : list term) : bool :=
  match ys with
  | [] => true
  | y :: tl => match erase_first y xs with Some rest => multiset_include rest tl | _ => false end
  end.
Fixpoint setof (xs : list term) : list term :=
  match xs with [] => [] | x :: tl => x :: filter (fun y => negb (term_eqb x y)) (setof tl) end.
Fixpoint multiset_filter (intersection : bool) (xs ys : list term) : list term :=
  match xs with
  | [] => []
  | x :: tl =>
      match erase_first x ys with
      | Some rest => if intersection then x :: multiset_filter intersection tl rest else multiset_filter intersection tl rest
      | None => if intersection then multiset_filter intersection tl ys else x :: multiset_filter intersection tl ys
      end
  end.
Fixpoint find_index (x : term) (xs : list term) (n : nat) : term :=
  match xs with [] => Symbol "-1" | y :: tl => if term_eqb x y then nat_term n else find_index x tl (S n) end.

(** The extension hook is syntax computation only. A later literal/arithmetic
    implementation can supply exact operations here; None propagates and never
    turns a failed selected case into the program's fallback case. *)
Definition primitive_hook := string -> list term -> option term.
Definition no_extension : primitive_hook := fun _ _ => None.
Definition native (extra : primitive_hook) (ops : list (string * term))
    (name : string) (args : list term) : option term :=
  let list_of op t :=
    match op with Symbol s => match named s ops with Some terminator => list_elements op terminator t | _ => None end | _ => None end in
  let rebuild op xs :=
    match op with Symbol s => option_map (fun terminator => make_list op terminator xs) (named s ops) | _ => None end in
  match name, args with
  | "eo::not", [a] => option_map (fun b => bool_term (negb b)) (as_bool a)
  | "eo::and", [a; b] | "eo::or", [a; b] | "eo::xor", [a; b] =>
      match as_bool a, as_bool b with
      | Some x, Some y => Some (bool_term (if String.eqb name "eo::and" then x && y else if String.eqb name "eo::or" then x || y else xorb x y))
      | _, _ => extra name args
      end
  | "eo::is_bool", [a] => Some (bool_term (match as_bool a with Some _ => true | _ => false end))
  | "eo::is_z", [a] => Some (bool_term (is_integer a))
  | "eo::is_q", [a] => Some (bool_term (is_rational a))
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
  | "eo::nil", [Symbol op; _] => named op ops
  | _, _ => extra name args
  end.

(** Fuel bounds expression traversal and recursive helper calls. Matching is
    purely syntactic as in Ethos evaluateProgramInternal (f97393e), not a second
    interpretation of program variable type annotations. Signatures remain
    metadata: inserting dynamic type checks here would reject legal traversals
    of polymorphic partial applications (e.g. congruence reaches bare =).
    Rule binders and explicit eo::typeof queries still use the supplied query. *)
Fixpoint evaluate_with (extra : primitive_hook) (ops : list (string * term))
    (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (env : bindings) (e : expression)
    : option term :=
  match fuel with
  | O => None
  | S k =>
    let ev := evaluate_with extra ops k typeof programs env in
    let fix eval_args (xs : list expression) : option (list term) :=
      match xs with
      | [] => Some []
      | a :: tl => match ev a, eval_args tl with Some t, Some ts => Some (t :: ts) | _, _ => None end
      end in
    match e with
    | EVar n => lookup n env
    | ESymbol s => Some (Symbol s)
    | EApply f a => match ev f, ev a with Some g, Some b => Some (Apply g b) | _, _ => None end
    | EIsOk a => Some (bool_term (match ev a with Some _ => true | None => false end))
    | EIsEq a b => Some (bool_term (match ev a, ev b with Some x, Some y => term_eqb x y | _, _ => false end))
    | EEq a b => match ev a, ev b with Some x, Some y => Some (bool_term (term_eqb x y)) | _, _ => None end
    | EIf c a b => match ev c with Some (Symbol "true") => ev a | Some (Symbol "false") => ev b | _ => None end
    | ERequires a b body => match ev a, ev b with Some x, Some y => if term_eqb x y then ev body else None | _, _ => None end
    | ETypeof a => match ev a with Some t => typeof t | None => None end
    | ELet n value body => match ev value with Some t => evaluate_with extra ops k typeof programs ((n, t) :: env) body | None => None end
    | ENative name args => match eval_args args with Some ts => native extra ops name ts | _ => None end
    | ECall name args =>
        match named name programs, eval_args args with
        | Some p, Some ts =>
            match select_case (program_cases p) ts [] with
            | Some (env', body) => evaluate_with extra ops k typeof programs env' body
            | None => None
            end
        | _, _ => None
        end
    end
  end.
Definition evaluate := evaluate_with no_extension [].

Definition run_rule_with (extra : primitive_hook) (ops : list (string * term))
    (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (args premises : list term) : option term :=
  match named name rules with
  | None => None
  | Some r =>
    let gathered :=
      match rule_premise_list r with
      | None => Some premises
      | Some op => option_map (fun terminator => [make_list (Symbol op) terminator premises]) (named op ops)
      end in
    match gathered with
    | None => None
    | Some ps =>
    match match_patterns (rule_arguments r ++ rule_premises r) (args ++ ps) [] with
    | None => None
    | Some env =>
      if Nat.eqb (List.length args) (List.length (rule_arguments r)) &&
         Nat.eqb (List.length ps) (List.length (rule_premises r)) &&
         forallb (fun t => has_type typeof t (Symbol "Bool")) premises then
        match typed_bindings typeof (rule_binders r) env with
        | None => None
        | Some checked =>
          let ev := evaluate_with extra ops fuel typeof programs checked in
          if forallb (fun req => match ev (fst req), ev (snd req) with Some x, Some y => term_eqb x y | _, _ => false end) (rule_requires r) then
            match ev (rule_conclusion r) with
            | Some t => if has_type typeof t (Symbol "Bool") then Some t else None
            | None => None
            end
          else None
        end
      else None
    end
    end
  end.
Definition run_rule := run_rule_with no_extension [].

Definition run_surface_rule_with (extra : primitive_hook) (fuel : nat)
    (typeof : term -> option term) (ops : list (string * term))
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (args premises : list term) : option term :=
  let fix visit xs :=
    match xs with
    | [] => Some []
    | x :: tl => match surface_in fuel ops x, visit tl with Some y, Some ys => Some (y :: ys) | _, _ => None end
    end in
  let internal_type t :=
    match surface_out fuel ops t with
    | Some s => typeof s
    | _ => None
    end in
  match visit args, visit premises with
  | Some xs, Some ps =>
    match run_rule_with extra ops fuel internal_type programs rules name xs ps with
    | Some t => surface_out fuel ops t
    | _ => None
    end
  | _, _ => None
  end.
Definition run_surface_rule := run_surface_rule_with no_extension.
