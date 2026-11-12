(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
(* Specialize expression structure ahead of evaluation. *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoCheckedMemo EoMemoCollector.
Import ListNotations EoCheckedMemo.
Open Scope string_scope.
Module EoStaged.
Definition handler := nat -> string -> list term -> computation term.
Section Context.
 Variable nilof:nil_query.
 Variable extra:primitive_hook.
 Variable ops:list(string*term).
 Variable typeof:term->option term.
 Variable programs:list(string*program).
 Fixpoint compile (e:expression) (depth:nat) (calls:handler) (fuel:nat) (env:bindings)
   {struct e} : computation term :=
 match fuel with
 | 0=>Missing "fuel exhausted"
 | S k=>
 match e with
 | EVar n=>match lookup n env with Some t=>Done t|None=>Missing "unbound variable" end
 | ESymbol s=>Done(Symbol s)
 | ENil op ty=>bind_computation (compile ty (S depth) calls k env)
    (fun t=>match nilof op (Some t) with Some z=>Done z|None=>Missing("nil "++op) end)
 | EApply a b=>
   match compile a (S depth) calls k env,compile b (S depth) calls k env with
   | Done x,Done y=>Done(Apply x y)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | EIsOk a=>match compile a (S depth) calls k env with
   |Done _=>Done(bool_term true)|Stuck=>Done(bool_term false)|Missing r=>Missing r end
 | EIsEq a b=>match compile a (S depth) calls k env,compile b (S depth) calls k env with
   |Done x,Done y=>Done(bool_term(term_eqb x y))|Missing r,_=>Missing r|_,Missing r=>Missing r
   |_,_=>Done(bool_term false) end
 | EEq a b=>match compile a (S depth) calls k env,compile b (S depth) calls k env with
   |Done x,Done y=>Done(bool_term(term_eqb x y))|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | EIf c a b=>match compile c (S depth) calls k env with
   |Done(Symbol "true")=>compile a (S depth) calls k env
   |Done(Symbol "false")=>compile b (S depth) calls k env
   |Missing r=>Missing r|_=>Stuck end
 | ERequires a b body=>match compile a (S depth) calls k env,compile b (S depth) calls k env with
   |Done x,Done y=>if term_eqb x y then compile body (S depth) calls k env else Stuck
   |Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end
 | ETypeof a=>bind_computation (compile a (S depth) calls k env)
   (fun t=>match typeof t with Some ty=>Done ty|None=>Missing "eo::typeof" end)
 | ELet n value body=>bind_computation (compile value (S depth) calls k env)
   (fun t=>compile body (S depth) calls k ((n,t)::env))
 | ENative name args=>
   let fix go xs :=match xs with
   |[]=>Done []
   |a::rest=>match compile a (S depth) calls k env,go rest with
      |Done x,Done xs=>Done(x::xs)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end end in
   native_result nilof typeof extra ops name (go args)
 | ECall name args=>
   let fix go xs :=match xs with
   |[]=>Done []
   |a::rest=>match compile a (S depth) calls k env,go rest with
      |Done x,Done xs=>Done(x::xs)|Missing r,_=>Missing r|_,Missing r=>Missing r|_,_=>Stuck end end in
   match named name programs,go args with
   |None,_=>Missing("program "++name)
   |Some _,Done xs=>calls (S depth) name xs
   |_,Missing r=>Missing r|_,_=>Stuck end
 end end.
End Context.


Theorem compile_refinement : forall nilof extra ops typeof programs budget calls,
 (forall depth name args, 0<depth<=budget ->
  calls depth name args=call_reference nilof extra ops (budget-depth) typeof programs name args) ->
 forall fuel depth env e, fuel+depth=budget ->
 compile nilof extra ops typeof programs e depth calls fuel env=
 evaluate_computation nilof extra ops fuel typeof programs env e.
Proof.
 intros nilof extra ops typeof programs budget calls Hcalls fuel.
 induction fuel as [|fuel IH]; intros depth env e Hbudget.
 - destruct e; reflexivity.
 - assert (Hrec:forall env e,
     compile nilof extra ops typeof programs e (S depth) calls fuel env=
     evaluate_computation nilof extra ops fuel typeof programs env e).
   { intros;apply IH;lia. }
   destruct e; cbn [compile evaluate_computation].
   all: fold compile evaluate_computation.
   all: try (repeat rewrite Hrec;reflexivity).
   all: try (unfold bind_computation;rewrite Hrec;
      destruct (evaluate_computation nilof extra ops fuel typeof programs env e1);try reflexivity;apply Hrec).
   all: try reflexivity.
   all: fold (arguments (fun e=>compile nilof extra ops typeof programs e (S depth) calls fuel env)).
   all: fold (arguments (evaluate_computation nilof extra ops fuel typeof programs env)).
   all: rewrite (arguments_ext _ _ (Hrec env)).
   all: try (unfold native_result;reflexivity).
   destruct (named s programs) as [p|] eqn:Hnamed;[|reflexivity].
   destruct (arguments (evaluate_computation nilof extra ops fuel typeof programs env) l)
      as [ts| |reason];try reflexivity.
   rewrite Hcalls by lia. unfold call_reference. rewrite Hnamed.
   replace (budget-S depth) with fuel by lia. reflexivity.
Qed.
Print Assumptions compile_refinement.
End EoStaged.
