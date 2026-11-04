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

(* Delay type queries until the selected signature nil declaration uses them.
   The strict interface remains available for reference computations. *)
Record nil_query := {
  nil_known : string -> bool;
  nil_value_lazy : string -> (unit -> option term) -> option term;
  nil_list_value_lazy : string -> (unit -> option term) -> option term
}.
Definition nil_value (nilof : nil_query) op ty := nil_value_lazy nilof op (fun _ => ty).
Definition nil_list_value (nilof : nil_query) op ty := nil_list_value_lazy nilof op (fun _ => ty).
Coercion nil_value : nil_query >-> Funclass.
Definition nil_apply (nilof : nil_query) (typeof : term -> option term) op t :=
  nil_value_lazy nilof op (fun _ => typeof t).
Definition nil_list_apply (nilof : nil_query) (typeof : term -> option term) op t :=
  nil_list_value_lazy nilof op (fun _ => typeof t).
Lemma nil_apply_refinement : forall nilof typeof op t,
  nil_apply nilof typeof op t = nil_value nilof op (typeof t).
Proof. reflexivity. Qed.
Lemma nil_list_apply_refinement : forall nilof typeof op t,
  nil_list_apply nilof typeof op t = nil_list_value nilof op (typeof t).
Proof. reflexivity. Qed.
Definition closed_nil (ops : list (string * term)) : nil_query :=
  {| nil_known := fun op => match named op ops with Some _ => true | None => false end;
     nil_value_lazy := fun op _ => named op ops;
     nil_list_value_lazy := fun op _ => named op ops |}.

Fixpoint match_pattern_with (nilof : nil_query) (typeof : term -> option term) (p : pattern) (t : term) (env : bindings)
    : option bindings :=
  match p with
  | PNil op => match nil_list_apply nilof typeof op t with
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
          match match_pattern_with nilof typeof f g env with
          | Some env' => match_pattern_with nilof typeof a b env'
          | None => None
          end
      | _ => None
      end
  end.

Definition match_pattern := match_pattern_with (closed_nil []) (fun _ => None).

Fixpoint match_patterns_with (nilof : nil_query) (typeof : term -> option term) (ps : list pattern) (ts : list term) (env : bindings)
    : option bindings :=
  match ps, ts with
  | [], [] => Some env
  | p :: pr, t :: tr =>
      match match_pattern_with nilof typeof p t env with
      | Some env' => match_patterns_with nilof typeof pr tr env'
      | None => None
      end
  | _, _ => None
  end.

Definition match_patterns := match_patterns_with (closed_nil []) (fun _ => None).

Fixpoint instantiate (p : pattern) (env : bindings) : option term :=
  match p with
  | PNil _ => None
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

(** Infer a matched function variable's type from its *application context*.
    No standalone monomorphic type is invented for an overloaded symbol.
    Hints are indexed by source binder, not by symbol spelling (outer Boolean
    equality and an inner integer equality can share the same symbol).

    A source-declared polymorphic constant has one syntax identity but may
    have different type instances at separate applications. Retain the first
    concrete hint to check the source binder, while checking each surrounding
    application through [typeof]. Ordinary variables still require agreement.
    This is syntax computation, not evidence that the query is trustworthy. *)
Definition polymorphic_head (polymorphic : list string) (t ty : term) : bool :=
  match t, ty with
  | Symbol name, Apply (Apply (Symbol "->") _) _ =>
      existsb (String.eqb name) polymorphic
  | _, _ => false
  end.
Fixpoint application_hints_with_polymorphic (polymorphic : list string) (typeof : term -> option term) (p : pattern)
    (t : term) (expected : option term) (hints : bindings) : option bindings :=
  let actual := match expected with Some ty => Some ty | None => typeof t end in
  match p with
  | PVar id => match actual, lookup id hints with
      | Some ty, Some prior =>
          if term_eqb ty prior ||
             (polymorphic_head polymorphic t ty && polymorphic_head polymorphic t prior)
          then Some hints else None
      | Some ty, None => Some ((id, ty) :: hints)
      | None, _ => Some hints end
  | PApply f a => match t with
      | Apply g b =>
          let dom := typeof b in
          let function_type := match dom, actual with
            | Some d, Some c => Some (Apply (Apply (Symbol "->") d) c)
            | _, _ => None end in
          match application_hints_with_polymorphic polymorphic typeof f g function_type hints with
          | Some hs => application_hints_with_polymorphic polymorphic typeof a b dom hs
          | None => None end
      | _ => None end
  | _ => Some hints
  end.
Definition application_hints := application_hints_with_polymorphic [].
Fixpoint collect_application_hints_with_polymorphic polymorphic typeof ps ts hints : option bindings :=
  match ps, ts with
  | [], [] => Some hints
  | p :: pr, t :: tr =>
      match application_hints_with_polymorphic polymorphic typeof p t None hints with
      | Some hs => collect_application_hints_with_polymorphic polymorphic typeof pr tr hs | None => None end
  | _, _ => None end.
Definition collect_application_hints := collect_application_hints_with_polymorphic [].
Definition binder_type_query (typeof : term -> option term) hints id t :=
  match typeof t, lookup id hints with
  | Some ty, Some inferred => if term_eqb ty inferred then Some ty else None
  | Some ty, None => Some ty
  | None, inferred => inferred end.
Fixpoint infer_types_with_hints typeof hints (bs : binder_types) (env : bindings) : option bindings :=
  match bs with
  | [] => Some env
  | (id, ty) :: tl => match lookup id env with
      | None => infer_types_with_hints typeof hints tl env
      | Some t => match binder_type_query typeof hints id t with
          | Some actual => match match_pattern ty actual env with
              | Some next => infer_types_with_hints typeof hints tl next | None => None end
          | None => None end
      end
  end.
Definition typed_bindings_with_hints typeof hints (bs : binder_types) env :=
  match infer_types_with_hints typeof hints bs env with
  | None => None
  | Some inferred => if forallb (fun entry =>
      match lookup (fst entry) inferred, instantiate (snd entry) inferred with
      | Some t, Some ty => match binder_type_query typeof hints (fst entry) t with
          | Some actual => term_eqb actual ty | None => false end
      | _, _ => false end) bs then Some inferred else None
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

Fixpoint select_case_with (nilof : nil_query) (typeof : term -> option term) (cs : list program_case) (args : list term)
    (env : bindings) : option (bindings * expression) :=
  match cs with
  | [] => None
  | c :: tl =>
      match match_patterns_with nilof typeof (case_patterns c) args env with
      | Some env' => Some (env', case_body c)
      | None => select_case_with nilof typeof tl args env
      end
  end.

Definition select_case := select_case_with (closed_nil []) (fun _ => None).

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
    applications (plus source-declared unary overloads) only; nil operators use generated closed or type-dependent nil bodies. *)
Fixpoint surface_supported_with_arities (unary blocked binary : list string) (t : term) : bool :=
  match t with
  | Symbol _ => true
  | Apply f a =>
      let '(hd, xs) := unapply t [] in
      let root_ok := match hd with
        | Symbol name => negb (existsb (String.eqb name) blocked) &&
            (if existsb (String.eqb name) binary then Nat.eqb (List.length xs) 2 ||
              (existsb (String.eqb name) unary && Nat.eqb (List.length xs) 1) else true)
        | _ => false end in
      (* Check the head spine without rechecking its partial arities. *)
      let fix children u := match u with
        | Symbol _ => true
        | Apply g b => children g && surface_supported_with_arities unary blocked binary b
        end in
      root_ok && children t
  end.

Definition surface_supported := surface_supported_with_arities [].

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

Fixpoint surface_in_with (nilof : nil_query) (typeof : term -> option term) (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_in_with nilof typeof k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd, visit xs with
      | Symbol name, Some ys =>
          match ys, (match xs with [] => named name ops | x :: _ => nil_apply nilof typeof name x end) with
          | [], _ => Some hd
          | _, Some terminator => Some (make_list hd terminator ys)
          | _, None => if nil_known nilof name then None else Some (apply_many hd ys)
          end
      | _, _ => None
      end
  end.

Fixpoint surface_out_with (nilof : nil_query) (typeof : term -> option term) (fuel : nat) (ops : list (string * term)) (t : term)
    : option term :=
  match fuel with
  | 0 => None
  | S k =>
      let '(hd, xs) := unapply t [] in
      let fix visit (xs : list term) : option (list term) :=
        match xs with
        | [] => Some []
        | x :: tl =>
          match surface_out_with nilof typeof k ops x, visit tl with
          | Some y, Some ys => Some (y :: ys)
          | _, _ => None
          end
        end in
      match hd, xs with
      | Symbol name, [] => Some hd
      | Symbol name, x :: tl =>
          match surface_out_with nilof typeof k ops x with
          | None => None
          | Some y =>
              match nil_apply nilof typeof name y with
              | Some terminator =>
                  match list_elements hd terminator t with
                  | Some ys => option_map (apply_many hd) (visit ys)
                  | None => None
                  end
              | None => if nil_known nilof name then None else
                  option_map (fun ys => apply_many hd (y :: ys)) (visit tl)
              end
          end
      | _, _ => None
      end
  end.

Definition surface_in fuel ops := surface_in_with (closed_nil ops) (fun _ => None) fuel ops.
Definition surface_out fuel ops := surface_out_with (closed_nil ops) (fun _ => None) fuel ops.

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
Definition native_with_nils (nilof : nil_query) (typeof : term -> option term) (extra : primitive_hook) (ops : list (string * term))
    (name : string) (args : list term) : option term :=
  let list_of op t :=
    match op with Symbol s => match nil_list_apply nilof typeof s t with Some terminator => list_elements op terminator t | _ => None end | _ => None end in
  let rebuild op xs :=
    match op with Symbol s => option_map (fun terminator => make_list op terminator xs) (match xs with
      | x :: _ => nil_apply nilof typeof s x
      | [] => match args with
          | _ :: witness :: _ =>
              if String.eqb name "eo::list_repeat" then nil_apply nilof typeof s witness
              else nil_list_apply nilof typeof s witness
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

Definition native extra ops := native_with_nils (closed_nil ops) (fun _ => None) extra ops.

(** Fuel bounds expression traversal and recursive helper calls. Matching is
    purely syntactic as in Ethos evaluateProgramInternal (f97393e), not a second
    interpretation of program variable type annotations. Signatures remain
    metadata: inserting dynamic type checks here would reject legal traversals
    of polymorphic partial applications (e.g. congruence reaches bare =).
    Rule binders and explicit eo::typeof queries still use the supplied query. *)
(** A stuck *available* operation differs from a missing implementation. EO
    kind/is_ok predicates can observe the former. Missing primitives and fuel
    exhaustion propagate through those predicates and cannot manufacture false. *)
Inductive computation (A : Type) := Done : A -> computation A | Stuck | Missing : string -> computation A.
Arguments Done {A} _.
Arguments Stuck {A}.
Arguments Missing {A} _.
Definition from_option {A} (x : option A) : computation A :=
  match x with Some v => Done v | None => Stuck end.
Definition computed {A} (x : computation A) : option A :=
  match x with Done v => Some v | _ => None end.
Definition bind_computation {A B} (x : computation A) (f : A -> computation B) : computation B :=
  match x with Done v => f v | Stuck => Stuck | Missing reason => Missing reason end.

Fixpoint evaluate_computation (nilof : nil_query) (extra : primitive_hook)
    (ops : list (string * term)) (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (env : bindings) (e : expression)
    : computation term :=
  match fuel with
  | O => Missing "fuel exhausted"
  | S k =>
    let ev := evaluate_computation nilof extra ops k typeof programs env in
    let fix eval_args (xs : list expression) : computation (list term) :=
      match xs with
      | [] => Done []
      | a :: tl =>
          match ev a, eval_args tl with
          | Done t, Done ts => Done (t :: ts)
          | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
          | _, _ => Stuck end
      end in
    let binary a b f := match ev a, ev b with
      | Done x, Done y => f x y
      | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
      | _, _ => Stuck end in
    match e with
    | ENil op ty => bind_computation (ev ty) (fun t => match nilof op (Some t) with Some z => Done z | None => Missing ("nil " ++ op) end)
    | EVar n => match lookup n env with Some t => Done t | None => Missing "unbound variable" end
    | ESymbol s => Done (Symbol s)
    | EApply f a => binary f a (fun g b => Done (Apply g b))
    | EIsOk a => match ev a with
        | Done _ => Done (bool_term true) | Stuck => Done (bool_term false) | Missing reason => Missing reason end
    | EIsEq a b => match ev a, ev b with
        | Done x, Done y => Done (bool_term (term_eqb x y))
        | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason | _, _ => Done (bool_term false) end
    | EEq a b => binary a b (fun x y => Done (bool_term (term_eqb x y)))
    | EIf c a b => match ev c with
        | Done (Symbol "true") => ev a | Done (Symbol "false") => ev b
        | Missing reason => Missing reason | _ => Stuck end
    | ERequires a b body => binary a b (fun x y => if term_eqb x y then ev body else Stuck)
    | ETypeof a => bind_computation (ev a) (fun t => match typeof t with Some ty => Done ty | None => Missing "eo::typeof" end)
    | ELet n value body => bind_computation (ev value) (fun t =>
        evaluate_computation nilof extra ops k typeof programs ((n, t) :: env) body)
    | ENative name args =>
        match eval_args args with
        | Missing reason => Missing reason
        | Stuck =>
            if existsb (String.eqb name) ["eo::is_z"; "eo::is_q"; "eo::is_bin"; "eo::is_str"; "eo::is_bool"]
            then Done (bool_term false) else Stuck
        | Done ts => match native_with_nils nilof typeof extra ops name ts with
            | Some t => Done t
            | None =>
                if existsb (String.eqb name)
                    ["eo::not"; "eo::and"; "eo::or"; "eo::xor";
                     "eo::list_rev"; "eo::list_len"; "eo::list_nth"; "eo::list_find";
                     "eo::list_erase"; "eo::list_erase_all"; "eo::list_setof"; "eo::list_concat";
                     "eo::list_diff"; "eo::list_inter"; "eo::list_minclude"; "eo::list_meq";
                     "eo::list_singleton_elim"; "eo::list_singleton_intro"; "eo::list_repeat";
                     "eo::cons"; "eo::nil"] then Stuck
                else match extra "eo::supports" [Symbol name] with
                | Some (Symbol "true") => Stuck | _ => Missing name end
            end
        end
    | ECall name args =>
        match named name programs, eval_args args with
        | Some p, Done ts =>
            match select_case_with nilof typeof (program_cases p) ts [] with
            | Some (bs, body) => evaluate_computation nilof extra ops k typeof programs bs body
            | None => Stuck end
        | None, _ => Missing ("program " ++ name)
        | _, Missing reason => Missing reason
        | _, _ => Stuck
        end
    end
  end.
Definition evaluate_with_nils nilof extra ops fuel typeof programs env e :=
  computed (evaluate_computation nilof extra ops fuel typeof programs env e).

Definition evaluate_with extra ops := evaluate_with_nils (closed_nil ops) extra ops.
Definition evaluate := evaluate_with no_extension [].

Definition nil_spec := (option (pattern * pattern) * expression)%type.
Definition resolve_nil_mode extra ops fuel typeof programs (specs : list (string * nil_spec))
    (list_argument : bool) op ty : option term :=
  match named op specs with
  | None => named op ops
  | Some (domains, body) =>
      let env := match domains, ty with
        | None, _ => Some []
        | Some (element, tail), Some t =>
            match_pattern (if list_argument then tail else element) t []
        | _, _ => None end in
      match env with Some bs => evaluate_with extra ops fuel typeof programs bs body | None => None end
  end.
Definition resolve_nil_lazy_mode extra ops fuel typeof programs (specs : list (string * nil_spec))
    (list_argument : bool) op (ty : unit -> option term) : option term :=
  match named op specs with
  | None => named op ops
  | Some (domains, body) =>
      let env := match domains with
        | None => Some []
        | Some (element, tail) => match ty tt with
          | Some t => match_pattern (if list_argument then tail else element) t []
          | None => None end end in
      match env with Some bs => evaluate_with extra ops fuel typeof programs bs body | None => None end
  end.
Lemma resolve_nil_lazy_mode_refinement : forall extra ops fuel typeof programs specs mode op ty,
  resolve_nil_lazy_mode extra ops fuel typeof programs specs mode op (fun _ => ty) =
  resolve_nil_mode extra ops fuel typeof programs specs mode op ty.
Proof.
  intros. unfold resolve_nil_lazy_mode, resolve_nil_mode.
  destruct (named op specs) as [[domains body]|]; [|reflexivity].
  destruct domains as [[element tail]|]; destruct ty; reflexivity.
Qed.
Definition resolve_nil extra ops fuel typeof programs (specs : list (string * nil_spec)) : nil_query :=
  {| nil_known := fun op => match named op specs, named op ops with None, None => false | _, _ => true end;
     nil_value_lazy := resolve_nil_lazy_mode extra ops fuel typeof programs specs false;
     nil_list_value_lazy := resolve_nil_lazy_mode extra ops fuel typeof programs specs true |}.

Definition run_rule_assuming_with_nils_polymorphic (polymorphic : list string) (nilof : nil_query) (extra : primitive_hook) (ops : list (string * term))
    (fuel : nat) (typeof : term -> option term)
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  match named name rules with
  | None => None
  | Some r =>
    let gathered :=
      match rule_premise_list r with
      | None => Some premises
      | Some op => option_map (fun terminator => [make_list (Symbol op) terminator premises]) (named op ops)
      end in
    let assumed := match rule_assumption r, assumption with
      | None, None => Some []
      | Some pat, Some t =>
          if has_type typeof t (Symbol "Bool") then match_pattern_with nilof typeof pat t [] else None
      | _, _ => None
      end in
    match gathered, assumed with
    | Some ps, Some initial =>
    match match_patterns_with nilof typeof (rule_arguments r ++ rule_premises r) (args ++ ps) initial with
    | None => None
    | Some env =>
      if Nat.eqb (List.length args) (List.length (rule_arguments r)) &&
         Nat.eqb (List.length ps) (List.length (rule_premises r)) &&
         forallb (fun t => has_type typeof t (Symbol "Bool")) premises then
        let patterns := (rule_arguments r ++ rule_premises r)%list in
        let values := (args ++ ps)%list in
        let hints := match collect_application_hints_with_polymorphic polymorphic typeof patterns values [] with
          | Some hs => match rule_assumption r, assumption with
              | Some pat, Some t => application_hints_with_polymorphic polymorphic typeof pat t None hs
              | _, _ => Some hs end
          | None => None end in
        match (match hints with Some hs => typed_bindings_with_hints typeof hs (rule_binders r) env | None => None end) with
        | None => None
        | Some checked =>
          let ev := evaluate_with_nils nilof extra ops fuel typeof programs checked in
          if forallb (fun req => match ev (fst req), ev (snd req) with Some x, Some y => term_eqb x y | _, _ => false end) (rule_requires r) then
            match ev (rule_conclusion r) with
            | Some t => if has_type typeof t (Symbol "Bool") then Some t else None
            | None => None
            end
          else None
        end
      else None
    end
    | _, _ => None
    end
  end.
Definition run_rule_assuming_with_nils := run_rule_assuming_with_nils_polymorphic [].
Definition run_rule_assuming_with extra ops := run_rule_assuming_with_nils (closed_nil ops) extra ops.

Definition run_rule_with extra ops fuel typeof programs rules name args premises :=
  run_rule_assuming_with extra ops fuel typeof programs rules name None args premises.
Definition run_rule := run_rule_with no_extension [].

Definition run_surface_rule_assuming_with_nils_polymorphic (polymorphic : list string) (nilof : nil_query) (extra : primitive_hook) (fuel : nat)
    (typeof : term -> option term) (ops : list (string * term))
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (assumption : option term) (args premises : list term) : option term :=
  let fix visit xs :=
    match xs with
    | [] => Some []
    | x :: tl => match surface_in_with nilof typeof fuel ops x, visit tl with Some y, Some ys => Some (y :: ys) | _, _ => None end
    end in
  let internal_type t :=
    match surface_out_with nilof typeof fuel ops t with
    | Some s => typeof s
    | _ => None
    end in
  let assumed := match assumption with
    | None => Some None
    | Some t => option_map (@Some term) (surface_in_with nilof typeof fuel ops t)
    end in
  match visit args, visit premises, assumed with
  | Some xs, Some ps, Some a =>
    match run_rule_assuming_with_nils_polymorphic polymorphic nilof extra ops fuel internal_type programs rules name a xs ps with
    | Some t => surface_out_with nilof typeof fuel ops t
    | _ => None
    end
  | _, _, _ => None
  end.
Definition run_surface_rule_assuming_with_nils := run_surface_rule_assuming_with_nils_polymorphic [].
Definition run_surface_rule_assuming_with extra fuel typeof ops :=
  run_surface_rule_assuming_with_nils (closed_nil ops) extra fuel typeof ops.

Definition run_surface_rule_with extra fuel typeof ops programs rules name args premises :=
  run_surface_rule_assuming_with extra fuel typeof ops programs rules name None args premises.
Definition run_surface_rule := run_surface_rule_with no_extension.
