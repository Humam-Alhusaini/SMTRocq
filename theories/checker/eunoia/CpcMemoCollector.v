(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime CpcGenerated.
From SMTCoq.checker.eunoia Require Import EoCheckedMemo EoRuleMemo EoMemoCollector CpcMemo.
Import ListNotations EoCheckedMemo.EoCheckedMemo.
Local Open Scope string_scope.
Definition prepare_surface (polymorphic : list string) (nilof : nil_query) (extra : primitive_hook) (fuel : nat)
    (typeof : term -> option term) (ops : list (string * term))
    (programs : list (string * program)) (rules : list (string * rule))
    (name : string) (assumption : option term) (args premises : list term) : option (rule * bindings) :=
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
    EoRuleMemo.with_prepared_rule (fun r env=>Some (r,env)) polymorphic nilof extra ops fuel internal_type programs rules name a xs ps
  | _, _, _ => None
  end.

Definition collect_context extra fuel typeof name assumption args premises :=
 let canon:=rename_symbols cpc_aliases in
 let query:=surface_query typeof in
 let nilof:=context_nilof extra fuel typeof in
 match prepare_surface cpc_polymorphic_operators nilof extra fuel query cpc_operators cpc_programs cpc_rules
   name (option_map canon assumption) (map canon args) (map canon premises) with
 | None=>[]
 | Some (r,env)=>
   let expressions:=rule_conclusion r :: flat_map (fun p=>[fst p;snd p]) (rule_requires r) in
   firstn 256 (flat_map (fun e=>snd(evaluate_logged nilof extra cpc_operators fuel 0
     (context_query extra fuel typeof) cpc_programs env e)) expressions)
 end.

(* Producer-only combined evaluation: return the candidate and its helper
   observations in one pass. The actual checker still validates both. *)
Definition execute_logged nilof extra fuel query r env :=
 let ev:=evaluate_logged nilof extra cpc_operators fuel 0 query cpc_programs env in
 let fix requirements reqs :=
   match reqs with
   | []=>(true,[])
   | (a,b)::rest=>
     let '(va,la):=ev a in let '(vb,lb):=ev b in
     let equal:=match va,vb with Done x,Done y=>term_eqb x y|_,_=>false end in
     if equal then let '(ok,ls):=requirements rest in (ok,(la++lb++ls)%list)
     else (false,(la++lb)%list)
   end in
 let '(ok,entries):=requirements (rule_requires r) in
 if ok then let '(value,logs):=ev (rule_conclusion r) in
   ((match value with Done t=>if has_type query t (Symbol "Bool") then Some t else None|_=>None end),
    firstn 256 (logs++entries)%list)
 else (None,firstn 256 entries).
Definition derive_context_logged extra fuel typeof name assumption args premises :=
 let canon:=rename_symbols cpc_aliases in
 let surface:=rename_symbols cpc_surface_names in
 let query:=surface_query typeof in
 let nilof:=context_nilof extra fuel typeof in
 let all_inputs:=((match assumption with Some a=>[a]|None=>[] end)++args++premises)%list in
 if forallb (surface_supported_with_arities cpc_unary_operators cpc_blocked_operators cpc_binary_operators)
   (map canon all_inputs) then
 match prepare_surface cpc_polymorphic_operators nilof extra fuel query cpc_operators cpc_programs cpc_rules
   name (option_map canon assumption) (map canon args) (map canon premises) with
 | None=>(None,[])
 | Some (r,env)=>
   let '(value,entries):=execute_logged nilof extra fuel (context_query extra fuel typeof) r env in
   let result:=match value with
     | Some t=>option_map surface (surface_out_with nilof query fuel cpc_operators t)
     | None=>None end in
   (result,entries)
 end else (None,[]).
