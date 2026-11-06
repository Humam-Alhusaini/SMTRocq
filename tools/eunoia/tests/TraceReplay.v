From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated.
Import ListNotations.
Open Scope string_scope.
Definition arrow (a b : term) := Apply (Apply (Symbol "->") a) b.

(** A partial, structural type query for the decoded UF fixture declarations.
    This is computation test input; no interpretation or acceptance theorem. *)
Fixpoint uf_query_fuel (fuel : nat) (decls : list (string * term)) (t : term) : option term :=
  match fuel with
  | 0 => None
  | S k =>
  match t with
  | Symbol "Bool" | Symbol "Int" | Symbol "U" | Symbol "@List" => Some (Symbol "Type")
  | Symbol "true" | Symbol "false" => Some (Symbol "Bool")
  | Symbol "not" => Some (arrow (Symbol "Bool") (Symbol "Bool"))
  | Symbol "@list.nil" => Some (Symbol "@List")
  | Symbol s => if is_integer t then Some (Symbol "Int") else named s decls
  | Apply (Symbol "=") x => option_map (fun ty => arrow ty (Symbol "Bool")) (uf_query_fuel k decls x)
  | Apply (Apply (Apply (Symbol "ite") c) x) y =>
      match uf_query_fuel k decls c, uf_query_fuel k decls x, uf_query_fuel k decls y with
      | Some (Symbol "Bool"), Some tx, Some ty => if term_eqb tx ty then Some tx else None
      | _, _, _ => None
      end
  | Apply _ _ =>
      let '(hd, args) := unapply t [] in
      if term_eqb hd (Symbol "and") || term_eqb hd (Symbol "or") ||
         term_eqb hd (Symbol "=>") || term_eqb hd (Symbol "xor") then
        let fix check xs := match xs with
          | [] => true
          | a :: tl => match uf_query_fuel k decls a with Some (Symbol "Bool") => check tl | _ => false end
          end in
        if check args then Some (Symbol "Bool") else None
      else if term_eqb hd (Symbol "@list") then Some (Symbol "@List") else
      match t with
      | Apply f a =>
        match uf_query_fuel k decls f, uf_query_fuel k decls a with
        | Some (Apply (Apply (Symbol "->") domain) codomain), Some actual =>
            if term_eqb domain actual then Some codomain else None
        | _, _ => None
        end
      | _ => None
      end
  end
  end.
Definition uf_query := uf_query_fuel 100.

Record decoded_step := {
  step_id : nat;
  step_rule : string;
  step_args : list term;
  step_premises : list nat;
  step_declared : option term
}.
Fixpoint fetch (ids : list nat) (env : bindings) : option (list term) :=
  match ids with
  | [] => Some []
  | i :: tl => match lookup i env, fetch tl env with Some t, Some ts => Some (t :: ts) | _, _ => None end
  end.
Definition replay_step_with (compute : nat -> (term -> option term) -> string -> list term -> list term -> option term) (query : term -> option term) (env : bindings) (s : decoded_step) : option bindings :=
  match lookup (step_id s) env with
  | Some _ => None
  | None =>
    match fetch (step_premises s) env with
    | None => None
    | Some ps =>
      match compute 500 query (step_rule s) (step_args s) ps with
      | None => None
      | Some t =>
          if match step_declared s with None => true | Some d => term_eqb d t end
          then Some ((step_id s, t) :: env) else None
      end
    end
  end.
Fixpoint replay_with (compute : nat -> (term -> option term) -> string -> list term -> list term -> option term) (query : term -> option term) (env : bindings) (steps : list decoded_step) : option bindings :=
  match steps with
  | [] => Some env
  | s :: tl => match replay_step_with compute query env s with Some next => replay_with compute query next tl | None => None end
  end.
Definition replay := replay_with derive.
Definition final_term query roots steps goal :=
  match replay query roots steps with Some env => lookup goal env | _ => None end.
