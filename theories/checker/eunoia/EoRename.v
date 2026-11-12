(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime EoNameIndex.
Module EoRename.
Fixpoint rename (index:EoNameIndex.trie term)(t:term):term:=
 match t with
 |Symbol s=>match EoNameIndex.lookup s index with Some u=>u|None=>t end
 |Apply f a=>Apply(rename index f)(rename index a)
 end.
Theorem refinement:forall aliases t,
 rename(EoNameIndex.from_list aliases)t=rename_symbols aliases t.
Proof.
 intros aliases t;induction t;simpl.
 - now rewrite EoNameIndex.lookup_from_list.
 - now rewrite IHt1,IHt2.
Qed.
Print Assumptions refinement.
End EoRename.
