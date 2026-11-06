(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List Bool String Uint63 ZArith.
From SMTCoq.utils Require Import PArray Misc CompDec.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker.eunoia Require Import EoSyntax EunoiaAdapter.
From SMTCoq.checker.eunoia Require Import EoModelDagCache.
Import ListNotations.
Module EunoiaModelDag.
(* Reuse SMTCoq's typed, indexed atom/formula graph and the adapter's exact
   encoding rules. The pass shares intermediate syntax; it adds no semantics.
   Missing dependencies and insufficient fuel use the original encoder. *)
Module K:=EoModelDagCache.
Section Tables.
Variable t_i:array typ_compdec.
Variable t_func:array(Atom.tval t_i).
Variable t_atom:array Atom.atom.
Variable t_form:array Form.form.
Variable names:EunoiaAdapter.naming.
Variable type_of:int->Typ.type.
Local Open Scope string_scope.
Local Open Scope array_scope.
Local Open Scope uint63_scope.
Local Abbreviation app:=EunoiaAdapter.app.
Local Abbreviation encode_sort:=(@EunoiaAdapter.encode_sort t_i names).
Local Abbreviation binop_name:=(@EunoiaAdapter.binop_name t_i names).
Definition reference fuel k id:=match k with
|K.Atom=>K.TermValue(@EunoiaAdapter.encode_atom_with_type t_i t_func t_atom names type_of fuel id)
|K.Positive=>K.PositiveValue(@EunoiaAdapter.positive_at t_atom fuel id)
|K.Literal=>K.TermValue(@EunoiaAdapter.encode_literal_with_type t_i t_func t_atom t_form names type_of fuel id)end.
Definition atom_plan(id:int):K.plan K.value:=
 if(id <? PArray.length t_atom)&&Atom.lt_atom id(t_atom.[id])&&
 Atom.check_aux t_i t_func type_of(t_atom.[id])(type_of id)then
 match encode_sort(type_of id)with
 |None=>K.Done(K.TermValue None)
 |Some _=>match t_atom.[id]with
  |Atom.Acop Atom.CO_Z0=>K.Done(K.TermValue(Some(Symbol "0")))
  |Atom.Auop Atom.UO_Zpos j=>K.map(fun v=>K.TermValue(option_map(fun p=>Symbol(EunoiaAdapter.numeral(Zpos p)))v))(K.positive_request j)
  |Atom.Auop Atom.UO_Zneg j=>K.map(fun v=>K.TermValue(option_map(fun p=>Symbol(EunoiaAdapter.numeral(Zneg p)))v))(K.positive_request j)
  |Atom.Auop Atom.UO_Zopp j=>K.map(fun v=>K.TermValue(option_map(fun a=>app "-"[a])v))(K.term_request K.Atom j)
  |Atom.Abop op a b=>K.bind(K.term_request K.Atom a)(fun va=>K.map(fun vb=>K.TermValue(match binop_name op,va,vb with
    |Some s,Some x,Some y=>Some(app s[x;y])|_,_,_=>None end))(K.term_request K.Atom b))
  |Atom.Aapp f args=>if f <? PArray.length t_func then
    K.map(fun vs=>K.TermValue(match EunoiaAdapter.name_at f(EunoiaAdapter.function_names names),vs,
     EunoiaAdapter.traverse encode_sort(fst(Atom.v_type _ _(t_func.[f]))),encode_sort(snd(Atom.v_type _ _(t_func.[f])))with
    |Some s,Some xs,Some _,Some _=>Some(app s xs)|_,_,_,_=>None end))(K.terms K.Atom args)
    else K.Done(K.TermValue None)
  |_=>K.Done(K.TermValue None)end
 end else K.Done(K.TermValue None).
Definition positive_plan(id:int):K.plan K.value:=
 if(id <? PArray.length t_atom)&&Atom.lt_atom id(t_atom.[id])then
 match t_atom.[id]with
 |Atom.Acop Atom.CO_xH=>K.Done(K.PositiveValue(Some xH))
 |Atom.Auop Atom.UO_xO j=>K.map(fun v=>K.PositiveValue(option_map xO v))(K.positive_request j)
 |Atom.Auop Atom.UO_xI j=>K.map(fun v=>K.PositiveValue(option_map xI v))(K.positive_request j)
 |_=>K.Done(K.PositiveValue None)end
 else K.Done(K.PositiveValue None).
Definition literal_plan(l:int):option(K.plan K.value):=
 let i:=Lit.blit l in
 if(i <? PArray.length t_form)&&Form.lt_form i(t_form.[i])then
 let base:=match t_form.[i]with
 |Form.Ftrue=>Some(K.Done(Some(Symbol "true")))
 |Form.Ffalse=>Some(K.Done(Some(Symbol "false")))
 |Form.Fatom a=>Some(if(a <? PArray.length t_atom)&&Typ.eqb(type_of a)Typ.Tbool then K.term_request K.Atom a else K.Done None)
 |Form.Fnot2 _ _=>None (* Preserve its fuel-dependent iteration by fallback. *)
 |Form.Fand args|Form.For args|Form.Fimp args=>Some(K.map(fun vs=>match vs with
  |Some xs=>EunoiaAdapter.nary(match t_form.[i]with Form.Fand _=>"and"|Form.For _=>"or"|_=>"=>"end)xs
  |None=>None end)(K.terms K.Literal(to_list args)))
 |Form.Fxor a b|Form.Fiff a b=>Some(K.bind(K.term_request K.Literal a)(fun va=>K.map(fun vb=>match va,vb with
  |Some x,Some y=>Some(app(match t_form.[i]with Form.Fxor _ _=>"xor"|_=>"="end)[x;y])|_,_=>None end)(K.term_request K.Literal b)))
 |Form.Fite a b c=>Some(K.bind(K.term_request K.Literal a)(fun va=>K.bind(K.term_request K.Literal b)(fun vb=>K.map(fun vc=>match va,vb,vc with
  |Some x,Some y,Some z=>Some(app "ite"[x;y;z])|_,_,_=>None end)(K.term_request K.Literal c))))
 |_=>Some(K.Done None)end in
 option_map(fun p=>K.map(fun v=>K.TermValue(option_map(fun t=>if Lit.is_pos l then t else app "not"[t])v))p)base
 else Some(K.Done(K.TermValue None)).
Definition body k id:=match k with
|K.Atom=>Some(atom_plan id)|K.Positive=>Some(positive_plan id)|K.Literal=>literal_plan id end.
Lemma terms_reference:forall fuel k ids,
 K.evaluate(reference fuel)(K.terms k ids)=
 EunoiaAdapter.traverse(fun id=>match reference fuel k id with K.TermValue t=>t|_=>None end)ids.
Proof. intros;rewrite K.terms_evaluate;induction ids;cbn;[reflexivity| ]. rewrite IHids;destruct(reference fuel k a);[destruct v| ];reflexivity. Qed.
Theorem body_reference:forall k id p,body k id=Some p->forall fuel,
 reference(S fuel)k id=K.evaluate(reference fuel)p.
Proof.
 intros[ | | ]id p H fuel;unfold body in H.
 - inversion H;subst p;unfold atom_plan;unfold reference at 1.
   cbn[EunoiaAdapter.encode_atom_with_type].
   destruct((id <? PArray.length t_atom)&&Atom.lt_atom id(t_atom.[id])&&Atom.check_aux t_i t_func type_of(t_atom.[id])(type_of id));[ |reflexivity].
   destruct(encode_sort(type_of id));[ |reflexivity].
   destruct(t_atom.[id])as[c|op a|op a b|op a b c|op args|f args].
   + destruct c;reflexivity.
   + destruct op;repeat rewrite K.evaluate_map;cbn[K.positive_request K.term_request K.evaluate reference];reflexivity.
   + repeat rewrite K.evaluate_bind;repeat rewrite K.evaluate_map;cbn[K.term_request K.evaluate reference].
     destruct(binop_name op),(@EunoiaAdapter.encode_atom_with_type t_i t_func t_atom names type_of fuel a),
      (@EunoiaAdapter.encode_atom_with_type t_i t_func t_atom names type_of fuel b);reflexivity.
   + reflexivity.
   + reflexivity.
   + destruct(f <? PArray.length t_func);[ |reflexivity].
     rewrite K.evaluate_map,terms_reference;reflexivity.

 - inversion H;subst p;unfold positive_plan;unfold reference at 1.
   cbn[EunoiaAdapter.positive_at].
   destruct((id <? PArray.length t_atom)&&Atom.lt_atom id(t_atom.[id]));[ |reflexivity].
   destruct(t_atom.[id])as[c|op j|op a b|op a b c|op args|f args];try reflexivity.
   + destruct c;reflexivity.
   + destruct op;repeat rewrite K.evaluate_map;cbn[K.positive_request K.evaluate reference];reflexivity.
 - unfold literal_plan in H;unfold reference at 1;cbn[EunoiaAdapter.encode_literal_with_type].
   destruct((Lit.blit id <? PArray.length t_form)&&Form.lt_form(Lit.blit id)(t_form.[Lit.blit id]));[ |inversion H;reflexivity].
   destruct(t_form.[Lit.blit id]);try discriminate;inversion H;subst p;cbn[K.evaluate];
    repeat rewrite K.evaluate_bind;repeat rewrite K.evaluate_map;repeat rewrite terms_reference;
    cbn[K.term_request K.evaluate reference];try reflexivity.
destruct((i <? PArray.length t_atom)&&Typ.eqb(type_of i)Typ.Tbool);reflexivity.
Qed.
Definition prepare:K.cache:=
 let atom_cache:=foldi(fun id c=>K.compile body K.Atom id(K.compile body K.Positive id c))0(PArray.length t_atom)K.empty in
 foldi(fun id c=>let l:=Lit.lit id in K.compile body K.Literal(Lit.neg l)(K.compile body K.Literal l c))0(PArray.length t_form)atom_cache.
Lemma compile_valid:forall c,K.valid reference c->forall k id,K.valid reference(K.compile body k id c).
Proof. intros;apply K.compile_correct;[exact body_reference|assumption]. Qed.
Theorem prepare_valid:K.valid reference prepare.
Proof.
 unfold prepare;apply(foldi_ind _ (fun _ c=>K.valid reference c));[apply leb_0| | ].
 - apply(foldi_ind _ (fun _ c=>K.valid reference c));[apply leb_0|apply K.empty_valid| ].
   intros;apply compile_valid;apply compile_valid;assumption.
 - intros;apply compile_valid;apply compile_valid;assumption.
Qed.
Definition encode_literal_cached fuel l cache:=match K.cached reference fuel K.Literal l cache with
|K.TermValue t=>t|_=>None end.
Theorem encode_literal_cached_correct:forall fuel l,
 encode_literal_cached fuel l prepare=
 @EunoiaAdapter.encode_literal_with_type t_i t_func t_atom t_form names type_of fuel l.
Proof. intros;unfold encode_literal_cached;rewrite K.cached_correct by exact prepare_valid;reflexivity. Qed.
End Tables.
Definition encoding_entries(t_i:array typ_compdec)(t_func:array(Atom.tval t_i))
 (t_atom:array Atom.atom)(t_form:array Form.form)(names:EunoiaAdapter.naming)(fuel:nat)(keys:list int):list(int*option term):=
 let unique:=fold_right(fun l acc=>if existsb(fun key=>Uint63.eqb l key)acc then acc else l::acc)[](firstn 1024 keys)in
 let interpreted:=@Atom.t_interp t_i t_func t_atom in
 let type_of:=@Atom.get_type' t_i interpreted in
 let cache:=prepare t_i t_func t_atom t_form names type_of in
 map(fun l=>(l,encode_literal_cached t_i t_func t_atom t_form names type_of fuel l cache))(firstn 512 unique).
Theorem encoding_entries_refinement:forall t_i t_func t_atom t_form names fuel keys,
 encoding_entries t_i t_func t_atom t_form names fuel keys=
 EunoiaAdapter.encoding_entries t_i t_func t_atom t_form names fuel keys.
Proof.
 intros;unfold encoding_entries,EunoiaAdapter.encoding_entries;apply map_ext;intro l;f_equal.
 apply encode_literal_cached_correct.
Qed.
Print Assumptions encode_literal_cached_correct.
End EunoiaModelDag.
