(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
(* Specialize expression structure ahead of evaluation. *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoCheckedMemo EoMemoCollector.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module EoDirect.
Definition handler := nat -> string -> list term -> computation term.
Section Context.
 Variable nilof:nil_query.
 Variable extra:primitive_hook.
 Variable ops:list(string*term).
 Variable typeof:term->option term.
 Variable programs:list(string*program).
 Fixpoint compile (e:expression) (calls:handler) (fuel:nat) (env:bindings)
   {struct e} : computation term :=
 match fuel with
 | 0=>Missing "fuel exhausted"
 | S k=>
 match e with
 | EVar n=>match lookup n env with Some t=>Done t|None=>Missing "unbound variable" end
 | ESymbol s=>Done(Symbol s)
 | ENil op ty=>bind_computation (compile ty calls k env)
    (fun t=>match nilof op (Some t) with Some z=>Done z|None=>Missing("nil "++op) end)
 | EApply a b=>
   match compile a calls k env,compile b calls k env with
   | Done x,Done y=>Done(Apply x y)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | EIsOk a=>match compile a calls k env with
   |Done _=>Done(bool_term true)|Stuck=>Done(bool_term false)|Missing r=>Missing r end
 | EIsEq a b=>match compile a calls k env,compile b calls k env with
   |Done x,Done y=>Done(bool_term(term_eqb x y))|Missing r,_=>Missing r|_,Missing r=>Missing r
   |_,_=>Done(bool_term false) end
 | EEq a b=>match compile a calls k env,compile b calls k env with
   |Done x,Done y=>Done(bool_term(term_eqb x y))|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | EIf c a b=>match compile c calls k env with
   |Done(Symbol "true")=>compile a calls k env
   |Done(Symbol "false")=>compile b calls k env
   |Missing r=>Missing r|_=>Stuck end
 | ERequires a b body=>match compile a calls k env,compile b calls k env with
   |Done x,Done y=>if term_eqb x y then compile body calls k env else Stuck
   |Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | ETypeof a=>bind_computation (compile a calls k env)
   (fun t=>match typeof t with Some ty=>Done ty|None=>Missing "eo::typeof" end)
 | ELet n value body=>bind_computation (compile value calls k env)
   (fun t=>compile body calls k ((n,t)::env))
 | ENative name args=>
   let fix go xs :=match xs with
   |[]=>Done []
   |a::rest=>match compile a calls k env,go rest with
      |Done x,Done xs=>Done(x::xs)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end end in
   native_result nilof typeof extra ops name (go args)
 | ECall name args=>
   let fix go xs :=match xs with
   |[]=>Done []
   |a::rest=>match compile a calls k env,go rest with
      |Done x,Done xs=>Done(x::xs)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end end in
   match named name programs,go args with
   |None,_=>Missing("program "++name)
   |Some _,Done xs=>calls k name xs
   |_,Missing r=>Missing r|_,_=>Stuck end
 end end.
End Context.

Theorem compile_refinement : forall nilof extra ops typeof programs fuel calls,
 (forall remaining name args, remaining<fuel ->
  calls remaining name args=call_reference nilof extra ops remaining typeof programs name args) ->
 forall env e,
 compile nilof extra ops typeof programs e calls fuel env=
 evaluate_computation nilof extra ops fuel typeof programs env e.
Proof.
 intros nilof extra ops typeof programs fuel;induction fuel as [|fuel IH];intros calls Hcalls env e.
 - destruct e;reflexivity.
 - assert(Hrec:forall env e,
     compile nilof extra ops typeof programs e calls fuel env=
     evaluate_computation nilof extra ops fuel typeof programs env e).
   { intros;apply IH;intros;apply Hcalls;lia. }
   destruct e;cbn[compile evaluate_computation].
   all:fold compile evaluate_computation.
   all:try(repeat rewrite Hrec;reflexivity).
   all:try(unfold bind_computation;rewrite Hrec;
      destruct(evaluate_computation nilof extra ops fuel typeof programs env e1);try reflexivity;apply Hrec).
   all:try reflexivity.
   all:fold(arguments(fun e=>compile nilof extra ops typeof programs e calls fuel env)).
   all:fold(arguments(evaluate_computation nilof extra ops fuel typeof programs env)).
   all:rewrite(arguments_ext _ _ (Hrec env)).
   all:try(unfold native_result;reflexivity).
   destruct(named s programs)as[p|]eqn:Hnamed;[|reflexivity].
   destruct(arguments(evaluate_computation nilof extra ops fuel typeof programs env)l)
     as[ts| |reason];try reflexivity.
   rewrite Hcalls by lia. unfold call_reference;rewrite Hnamed;reflexivity.
Qed.
Definition run_program nilof extra ops typeof programs calls fuel p args :=
 match select_case_with nilof typeof (program_cases p) args [] with
 |None=>Stuck|Some(env,body)=>compile nilof extra ops typeof programs body calls fuel env end.
Theorem run_program_correct:forall nilof extra ops typeof programs fuel calls,
 (forall remaining name args,remaining<fuel -> calls remaining name args=
 call_reference nilof extra ops remaining typeof programs name args) ->
 forall p args,run_program nilof extra ops typeof programs calls fuel p args=
 match select_case_with nilof typeof(program_cases p)args[]with
 |None=>Stuck|Some(env,body)=>evaluate_computation nilof extra ops fuel typeof programs env body end.
Proof.
 intros;unfold run_program.
 destruct(select_case_with nilof typeof(program_cases p)args[])as[[env body]|];[|reflexivity].
 apply compile_refinement;assumption.
Qed.
Definition call_compiled nilof extra ops typeof programs calls fuel name args :=
 match named name programs with
 |None=>Missing("program "++name)
 |Some p=>run_program nilof extra ops typeof programs calls fuel p args end.
Theorem call_compiled_correct : forall nilof extra ops typeof programs fuel calls,
 (forall remaining name args,remaining<fuel -> calls remaining name args=
   call_reference nilof extra ops remaining typeof programs name args) ->
 forall name args,call_compiled nilof extra ops typeof programs calls fuel name args=
 call_reference nilof extra ops fuel typeof programs name args.
Proof.
 intros;unfold call_compiled,run_program,call_reference.
 destruct(named name programs)as[p|];[|reflexivity].
 destruct(select_case_with nilof typeof(program_cases p)args[])as[[env body]|];[|reflexivity].
 apply compile_refinement;assumption.
Qed.
Print Assumptions call_compiled_correct.
Print Assumptions compile_refinement.
End EoDirect.
