From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoArithmetic CpcGenerated TraceReplay.
Import ListNotations.
Open Scope string_scope.
(** Deterministic syntax type metadata for tests. Casts check their input
    sorts; arithmetic accepts homogeneous Int or Real operands only. No
    equation, arithmetic fact, rule name or desired result influences typing. *)
Definition arithmetic_sort ty := term_eqb ty (Symbol "Int") || term_eqb ty (Symbol "Real").
Fixpoint lia_query_fuel (fuel : nat) (decls : list (string * term)) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S k =>
    let query := lia_query_fuel k decls in
    let same ty a := match query a with Some actual => term_eqb ty actual | _ => false end in
    match t with
    | Symbol "Real" => Some (Symbol "Type")
    | Symbol _ => match EoArithmetic.parse_term t with
        | Some (EoArithmetic.LRational _) | Some (EoArithmetic.LDecimal _ _) => Some (Symbol "Real")
        | _ => uf_query decls t end
    | Apply (Symbol "=") x => option_map (fun ty => arrow ty (Symbol "Bool")) (query x)
    | Apply _ _ =>
      let '(hd, args) := unapply t [] in
      if term_eqb hd (Symbol "@list") then Some (Symbol "@List") else
      if existsb (fun s => term_eqb hd (Symbol s)) ["to_real"; "to_int"; "is_int"] then
        match args with
        | [x] =>
            let input := if term_eqb hd (Symbol "to_real") then Symbol "Int" else Symbol "Real" in
            if same input x then Some (if term_eqb hd (Symbol "to_real") then Symbol "Real"
              else if term_eqb hd (Symbol "to_int") then Symbol "Int" else Symbol "Bool") else None
        | _ => None end
      else if existsb (fun s => term_eqb hd (Symbol s)) ["+"; "*"; "-"; "/"] then
        match args with
        | x :: tl => match query x with
          | Some ty => if arithmetic_sort ty && forallb (same ty) tl &&
              (if term_eqb hd (Symbol "/") then term_eqb ty (Symbol "Real") && Nat.eqb (List.length args) 2
               else if term_eqb hd (Symbol "-") then Nat.leb (List.length args) 2
               else Nat.leb 2 (List.length args))
            then Some ty else None
          | _ => None end
        | _ => None end
      else if existsb (fun s => term_eqb hd (Symbol s)) ["<"; "<="; ">"; ">="; "="] then
        match args with
        | [x; y] => match query x with
          | Some ty => if same ty y && (term_eqb hd (Symbol "=") || arithmetic_sort ty)
            then Some (Symbol "Bool") else None
          | _ => None end
        | _ => None end
      else if existsb (fun s => term_eqb hd (Symbol s)) ["not"; "and"; "or"; "=>"; "xor"] then
        if forallb (same (Symbol "Bool")) args &&
            (if term_eqb hd (Symbol "not") then Nat.eqb (List.length args) 1 else true)
        then Some (Symbol "Bool") else None
      else if term_eqb hd (Symbol "ite") then
        match args with
        | [c; x; y] => match query x with
          | Some ty => if same (Symbol "Bool") c && same ty y then Some ty else None
          | _ => None end
        | _ => None end
      else match t with
      | Apply f a => match query f, query a with
        | Some (Apply (Apply (Symbol "->") dom) cod), Some actual => if term_eqb dom actual then Some cod else None
        | _, _ => None end
      | _ => None end
    end
  end.
Definition lia_query := lia_query_fuel 200.

(** Fixture computation harness only. Every local step is computed before a
    pop restores the saved environment. This is not the semantic scoped core. *)
Inductive trace_command :=
| TraceStep : decoded_step -> trace_command
| TracePush : nat -> term -> trace_command
| TracePop : decoded_step -> trace_command.
Definition trace_frame := (term * bindings)%type.
Definition insert_computed (env : bindings) (s : decoded_step) (t : term) : option bindings :=
  match lookup (step_id s) env with
  | Some _ => None
  | None => if match step_declared s with Some d => term_eqb d t | None => true end
            then Some ((step_id s, t) :: env) else None end.
Definition trace_tick_with compute compute_assuming (query : term -> option term) (env : bindings)
    (stack : list trace_frame) (command : trace_command)
    : option (bindings * list trace_frame) :=
  match command with
  | TraceStep s => option_map (fun next => (next, stack)) (replay_step_with compute query env s)
  | TracePush id assumption =>
      match lookup id env with
      | Some _ => None
      | None => if has_type query assumption (Symbol "Bool")
        then Some ((id, assumption) :: env, (assumption, env) :: stack) else None end
  | TracePop s =>
      match stack, fetch (step_premises s) env with
      | (assumption, saved) :: tl, Some ps =>
        match compute_assuming 500 query (step_rule s) assumption (step_args s) ps with
        | Some t => option_map (fun next => (next, tl)) (insert_computed saved s t)
        | _ => None end
      | _, _ => None end
  end.
Definition trace_tick := trace_tick_with derive derive_assuming.
Fixpoint trace_replay_with compute compute_assuming query env stack commands : option bindings :=
  match commands with
  | [] => match stack with [] => Some env | _ => None end
  | c :: tl => match trace_tick_with compute compute_assuming query env stack c with
      | Some (next, frames) => trace_replay_with compute compute_assuming query next frames tl | _ => None end
  end.
Definition trace_replay := trace_replay_with derive derive_assuming.
Definition trace_final_with compute compute_assuming query roots commands goal :=
  match trace_replay_with compute compute_assuming query roots [] commands with Some env => lookup goal env | _ => None end.
Definition trace_final := trace_final_with derive derive_assuming.
Definition command_id (c : trace_command) :=
  match c with TraceStep s | TracePop s => step_id s | TracePush id _ => id end.
Fixpoint trace_diagnostic query env stack commands : option nat :=
  match commands with
  | [] => match stack with [] => None | _ => Some 0 end
  | c :: tl => match trace_tick query env stack c with
      | Some (next, frames) => trace_diagnostic query next frames tl
      | _ => Some (command_id c) end
  end.
