(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Pure verified indexing of signature metadata. *)
From Stdlib Require Import List String Ascii Bool.
From SMTCoq.checker.eunoia Require Import EoRuntime.
Import ListNotations.
Open Scope string_scope.
Module EoNameIndex.
Inductive trie (A:Type) := Node : option A -> list (ascii * trie A) -> trie A.
Arguments Node {A} _ _.
Definition empty {A}:trie A := Node None [].
Fixpoint edge {A} c (edges:list (ascii*trie A)) :=
 match edges with []=>None|(a,t)::rest=>if Ascii.eqb c a then Some t else edge c rest end.
Fixpoint set_edge {A} c (t:trie A) edges :=
 match edges with
 | []=>[(c,t)]
 | (a,old)::rest=>if Ascii.eqb c a then (c,t)::rest else (a,old)::set_edge c t rest
 end.
Fixpoint lookup {A} (key:string) (t:trie A) : option A :=
 match key,t with
 | EmptyString,Node value _=>value
 | String c rest,Node _ edges=>match edge c edges with Some child=>lookup rest child|None=>None end
 end.
Fixpoint insert {A} (key:string) (value:A) (t:trie A) : trie A :=
 match key,t with
 | EmptyString,Node _ edges=>Node (Some value) edges
 | String c rest,Node old edges=>
   let child:=match edge c edges with Some child=>child|None=>empty end in
   Node old (set_edge c (insert rest value child) edges)
 end.
Lemma char_refl : forall c,Ascii.eqb c c=true.
Proof. intro; apply Ascii.eqb_eq; reflexivity. Qed.
Lemma edge_set_same : forall A c (t:trie A) edges,
 edge c (set_edge c t edges)=Some t.
Proof.
 intros A c t edges; induction edges as [|[a old] rest IH]; simpl.
 - now rewrite char_refl.
 - destruct (Ascii.eqb c a) eqn:Hca; simpl; [now rewrite char_refl|].
   rewrite Hca; exact IH.
Qed.
Lemma edge_set_other : forall A a b (t:trie A) edges,
 a<>b -> edge a (set_edge b t edges)=edge a edges.
Proof.
 intros A a b t edges Hneq; induction edges as [|[c old] rest IH]; simpl.
 - destruct (Ascii.eqb a b) eqn:H; [apply Ascii.eqb_eq in H; contradiction|reflexivity].
 - destruct (Ascii.eqb b c) eqn:Hbc; simpl.
   + apply Ascii.eqb_eq in Hbc; subst c.
     destruct (Ascii.eqb a b) eqn:H; [apply Ascii.eqb_eq in H; contradiction|reflexivity].
   + destruct (Ascii.eqb a c); [reflexivity|exact IH].
Qed.
Lemma lookup_empty : forall A key,@lookup A key empty=None.
Proof. intros A [|c key]; reflexivity. Qed.
Theorem lookup_insert : forall A (key:string) value (t:trie A) query,
 lookup query (insert key value t)=if String.eqb query key then Some value else lookup query t.
Proof.
 intros A key; induction key as [|c key IH]; intros value [old edges] [|a query]; simpl.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - destruct (Ascii.eqb a c) eqn:Hac.
   + apply Ascii.eqb_eq in Hac; subst a. repeat rewrite char_refl. rewrite edge_set_same.
     rewrite IH. destruct (edge c edges); [reflexivity|now rewrite lookup_empty].
   + rewrite (edge_set_other A a c) by (intro Heq; subst a; rewrite char_refl in Hac; discriminate).
     reflexivity.
Qed.
Definition from_list {A} (entries:list(string*A)) : trie A :=
 fold_right (fun kv t=>insert (fst kv) (snd kv) t) empty entries.
Theorem lookup_from_list : forall A (entries:list(string*A)) key,
 lookup key (from_list entries)=named key entries.
Proof.
 intros A entries; induction entries as [|[name value] entries IH]; intro key; simpl.
 - apply lookup_empty.
 - rewrite lookup_insert,IH. reflexivity.
Qed.
Print Assumptions lookup_from_list.
End EoNameIndex.
