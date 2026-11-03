From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoArithmetic CpcGenerated TraceReplay.
Import ListNotations.
Open Scope string_scope.
Fixpoint lia_query_fuel (fuel : nat) (decls : list (string * term)) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S k =>
    let query := lia_query_fuel k decls in
    match t with
    | Symbol "Real" => Some (Symbol "Type")
    | Symbol _ => if is_rational t then Some (Symbol "Real") else uf_query decls t
    | Apply (Symbol "=") x => option_map (fun ty => arrow ty (Symbol "Bool")) (query x)
    | Apply (Symbol op) x =>
        if existsb (String.eqb op) ["not"; "and"; "or"; "=>"; "xor"] then
          match query x with Some (Symbol "Bool") => Some (Symbol "Bool") | _ => None end
        else if existsb (String.eqb op) ["<"; "<="; ">"; ">="] then
          option_map (fun ty => arrow ty (Symbol "Bool")) (query x)
        else if String.eqb op "-" then query x
        else if String.eqb op "to_real" then Some (Symbol "Real")
        else if String.eqb op "to_int" then Some (Symbol "Int")
        else match uf_query decls t with Some ty => Some ty | _ => None end
    | Apply _ _ =>
      let '(hd, args) := unapply t [] in
      if term_eqb hd (Symbol "@list") then Some (Symbol "@List") else
      if existsb (fun s => term_eqb hd (Symbol s)) ["+"; "*"; "-"] then
        match args with
        | x :: tl => match query x with
          | Some ty => if forallb (fun a => match query a with Some actual => term_eqb ty actual | _ => false end) tl then Some ty else None
          | _ => None end
        | _ => None end
      else if existsb (fun s => term_eqb hd (Symbol s)) ["<"; "<="; ">"; ">="; "="] then
        match args with
        | [x; y] => match query x, query y with Some a, Some b => if term_eqb a b then Some (Symbol "Bool") else None | _, _ => None end
        | _ => None end
      else if existsb (fun s => term_eqb hd (Symbol s)) ["and"; "or"; "=>"; "xor"] then
        if forallb (fun a => match query a with Some (Symbol "Bool") => true | _ => false end) args then Some (Symbol "Bool") else None
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
Definition trace_tick (query : term -> option term) (env : bindings)
    (stack : list trace_frame) (command : trace_command)
    : option (bindings * list trace_frame) :=
  match command with
  | TraceStep s => option_map (fun next => (next, stack)) (replay_step_with derive query env s)
  | TracePush id assumption =>
      match lookup id env with
      | Some _ => None
      | None => if has_type query assumption (Symbol "Bool")
        then Some ((id, assumption) :: env, (assumption, env) :: stack) else None end
  | TracePop s =>
      match stack, fetch (step_premises s) env with
      | (assumption, saved) :: tl, Some ps =>
        match derive_assuming 500 query (step_rule s) assumption (step_args s) ps with
        | Some t => option_map (fun next => (next, tl)) (insert_computed saved s t)
        | _ => None end
      | _, _ => None end
  end.
Fixpoint trace_replay query env stack commands : option bindings :=
  match commands with
  | [] => match stack with [] => Some env | _ => None end
  | c :: tl => match trace_tick query env stack c with
      | Some (next, frames) => trace_replay query next frames tl | _ => None end
  end.
Definition trace_final query roots commands goal :=
  match trace_replay query roots [] commands with Some env => lookup goal env | _ => None end.
Definition command_id (c : trace_command) :=
  match c with TraceStep s | TracePop s => step_id s | TracePush id _ => id end.
Fixpoint trace_diagnostic query env stack commands : option nat :=
  match commands with
  | [] => match stack with [] => None | _ => Some 0 end
  | c :: tl => match trace_tick query env stack c with
      | Some (next, frames) => trace_diagnostic query next frames tl
      | _ => Some (command_id c) end
  end.
