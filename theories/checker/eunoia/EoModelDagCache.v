(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool Arith Lia Uint63 ZArith.
From SMTCoq.utils Require Import PArray.
From SMTCoq.checker.eunoia Require Import EoSyntax.
Import ListNotations.
Module EoModelDagCache.
(* A computed cache, never producer-supplied evidence. Each entry records the
   minimum recursive fuel at which its result agrees with the reference. *)
Module M:=PArray.Map.
Module F:=PArray.P.F.
Inductive kind:=Atom|Positive|Literal.
Inductive value:=TermValue(v:option term)|PositiveValue(v:option positive).
Record entry:=Entry{result:value;depth:nat}.
Record cache:=Cache{atoms:M.t entry;positives:M.t entry;literals:M.t entry}.
Definition empty:=Cache(M.empty entry)(M.empty entry)(M.empty entry).
Definition table(k:kind)(c:cache):M.t entry:=match k with Atom=>atoms c|Positive=>positives c|Literal=>literals c end.
Definition lookup k id c:=M.find id(table k c).
Definition put k id e c:=match k with
|Atom=>Cache(M.add id e(atoms c))(positives c)(literals c)
|Positive=>Cache(atoms c)(M.add id e(positives c))(literals c)
|Literal=>Cache(atoms c)(positives c)(M.add id e(literals c))end.
Definition valid(reference:nat->kind->int->value)(c:cache):Prop:=
 forall k id e,lookup k id c=Some e->forall fuel,depth e<=fuel->result e=reference fuel k id.
Lemma empty_valid:forall reference,valid reference empty.
Proof. intros reference k id e H;destruct k;unfold lookup,table,empty in H;cbn in H;discriminate. Qed.
Lemma put_valid:forall reference c k id e,valid reference c->
 (forall fuel,depth e<=fuel->result e=reference fuel k id)->valid reference(put k id e c).
Proof.
 intros reference c k id e Hc He k' id' e' Hfind fuel Hfuel.
 destruct k;destruct k';unfold lookup,put,table in Hfind;cbn[atoms positives literals]in Hfind;
 try solve[eapply Hc;[exact Hfind|exact Hfuel]].
 all:destruct(Uint63.eqb id id')eqn:Eq.
 all:try(apply Uint63.eqb_spec in Eq;subst id';rewrite F.add_eq_o in Hfind;
  [inversion Hfind;subst;eapply He;exact Hfuel|apply PArray.IntOrderedType.eq_refl]).
 all:rewrite F.add_neq_o in Hfind;[eapply Hc;[exact Hfind|exact Hfuel]|unfold PArray.IntOrderedType.eq;intro H;congruence].
Qed.
Inductive plan(A:Type):Type:=Done(a:A)|Request(k:kind)(id:int)(next:value->plan A).
(* Plans expose dependencies without recursively expanding their values. A
   single pass can skip a node whose prerequisites have not been cached. *)
Arguments Done{A}_ .
Arguments Request{A}_ _ _ .
Fixpoint bind{A B}(p:plan A)(f:A->plan B):plan B:=match p with
|Done a=>f a|Request k id next=>Request k id(fun v=>bind(next v)f)end.
Definition map{A B}(f:A->B)(p:plan A):plan B:=bind p(fun a=>Done(f a)).
Fixpoint evaluate{A}(query:kind->int->value)(p:plan A):A:=match p with
|Done a=>a|Request k id next=>evaluate query(next(query k id))end.
Fixpoint run{A}(p:plan A)(c:cache):option(A*nat):=match p with
|Done a=>Some(a,0)
|Request k id next=>match lookup k id c with
 |None=>None
 |Some e=>match run(next(result e))c with
  |None=>None|Some(v,d)=>Some(v,Nat.max(depth e)d)end end end.
Lemma evaluate_bind:forall A B query(p:plan A)(f:A->plan B),
 evaluate query(bind p f)=evaluate query(f(evaluate query p)).
Proof. intros A B query p;induction p as[a|k id next IH];intros f;cbn;[reflexivity|apply IH]. Qed.
Lemma evaluate_map:forall A B query(f:A->B)(p:plan A),evaluate query(map f p)=f(evaluate query p).
Proof. intros;unfold map;rewrite evaluate_bind;reflexivity. Qed.
Theorem run_correct:forall A reference c(p:plan A)result bound,
 valid reference c->run p c=Some(result,bound)->
 forall fuel,bound<=fuel->result=evaluate(reference fuel)p.
Proof.
 intros A reference c p;induction p as[a|k id next IH];intros result bound Hc Hrun fuel Hfuel;cbn in Hrun.
 - inversion Hrun;reflexivity.
 - destruct(lookup k id c)as[e|]eqn:E;[|discriminate].
   destruct(run(next(EoModelDagCache.result e))c)as[[v d]|]eqn:Er;[|discriminate].
   inversion Hrun;subst result bound;cbn[evaluate].
   rewrite <- (Hc k id e E fuel ltac:(lia)).
   apply(IH _ v d Hc Er fuel);lia.
Qed.
Definition compile(body:kind->int->option(plan value))(k:kind)id(c:cache):cache:=
 match body k id with
 |None=>c
 |Some p=>match run p c with
  |None=>c
  |Some(v,bound)=>put k id(Entry v(S bound))c end end.
Theorem compile_correct:forall reference body,
 (forall k id p,body k id=Some p->forall fuel,
   reference(S fuel)k id=evaluate(reference fuel)p)->
 forall c,valid reference c->forall k id,valid reference(compile body k id c).
Proof.
 intros reference body Hbody c Hc k id;unfold compile.
 destruct(body k id)as[p|]eqn:E;[|exact Hc].
 destruct(run p c)as[[v d]|]eqn:Er;[|exact Hc].
 apply put_valid;[exact Hc|].
 intros[|fuel]Hfuel;[cbn in Hfuel;lia|].
 cbn[result depth]in *;rewrite(Hbody _ _ _ E fuel).
 apply(run_correct _ reference c p v d Hc Er fuel);lia.
Qed.
Definition term_request k id:plan(option term):=Request k id(fun value=>Done(match value with TermValue t=>t|_=>None end)).
Definition positive_request id:plan(option positive):=Request Positive id(fun value=>Done(match value with PositiveValue p=>p|_=>None end)).
Fixpoint terms(k:kind)(ids:list int):plan(option(list term)):=match ids with
|[]=>Done(Some[])
|id::ids=>bind(term_request k id)(fun v=>map(fun rest=>match v,rest with
 |Some t,Some ts=>Some(t::ts)|_,_=>None end)(terms k ids))end.
Lemma terms_evaluate:forall query k ids,
 evaluate query(terms k ids)=
 (fix traverse(ids:list int):option(list term):=match ids with
 |[]=>Some[]|id::ids=>match query k id,traverse ids with
 |TermValue(Some t),Some ts=>Some(t::ts)|_,_=>None end end)ids.
Proof.
 intros query k ids;induction ids;cbn[terms];[reflexivity|].
 rewrite evaluate_bind,evaluate_map,IHids;cbn[term_request evaluate];destruct(query k a);[destruct v|];reflexivity.
Qed.
Definition cached reference fuel k id c:=match lookup k id c with
|None=>reference fuel k id
|Some e=>if Nat.leb(depth e)fuel then result e else reference fuel k id end.
Lemma cached_correct:forall reference fuel k id c,valid reference c->
 cached reference fuel k id c=reference fuel k id.
Proof.
 intros reference fuel k id c H;unfold cached.
 destruct(lookup k id c)as[e|]eqn:E;[|reflexivity].
 destruct(Nat.leb(depth e)fuel)eqn:Hd;[|reflexivity].
 apply Nat.leb_le in Hd;eapply H;eassumption.
Qed.
Print Assumptions compile_correct.
End EoModelDagCache.
