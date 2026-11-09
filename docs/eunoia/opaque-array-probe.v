(* Component diagnostic described in opaque-array-comparison-2026-11-09.md.
   Compile against each fully rebuilt library variant with a 30-second deadline.
   The raw lookup is a proved diagnostic control, not a checker replacement. *)
From Stdlib Require Import List Bool Uint63 ZArith.
From SMTCoq.utils Require Import PArray.
Import ListNotations.
Module FastMapProbe.
Module M:=PArray.Map.
Local Open Scope uint63_scope.
Fixpoint raw_find {A}(x:int)(t:M.Raw.tree A):option A:=match t with
 |M.Raw.Leaf _=>None
 |M.Raw.Node l key value r _=>if x <? key then raw_find x l
   else if x =? key then Some value else raw_find x r end.
Theorem raw_find_refinement:forall A(x:int)(t:M.Raw.tree A),raw_find x t=M.Raw.find x t.
Proof.
 intros A x t;induction t as[|l IHl k value r IHr h];[reflexivity|].
 cbn[raw_find M.Raw.find].
 destruct(PArray.IntOrderedType.compare x k)as[Hlt|Heq|Hgt].
 - unfold PArray.IntOrderedType.lt in Hlt;rewrite Hlt;exact IHl.
 - unfold PArray.IntOrderedType.eq in Heq;apply Uint63.eqb_spec in Heq;subst k.
   assert(Hlt:(x <? x)=false).
   { apply Bool.not_true_iff_false;intro H;apply Uint63.ltb_spec in H;lia. }
   rewrite Hlt,Uint63.eqb_refl;reflexivity.
 - unfold PArray.IntOrderedType.lt in Hgt.
   assert(Hlt:(x <? k)=false).
   { apply Bool.not_true_iff_false;intro H;apply Uint63.ltb_spec in H,Hgt;lia. }
   assert(Heq:(x =? k)=false).
   { apply Bool.not_true_iff_false;intro H;apply Uint63.eqb_spec in H;subst k.
     apply Uint63.ltb_spec in Hgt;lia. }
   rewrite Hlt,Heq;exact IHr.
Qed.
Definition find{A}(x:int)(m:M.t A):=raw_find x(M.this m).
Theorem find_refinement:forall A x(m:M.t A),find x m=M.find x m.
Proof. intros;apply raw_find_refinement. Qed.
Definition keys:=map(fun n=>Uint63.of_Z(Z.of_nat n))(seq 0 1024).
Definition tree:=Eval vm_compute in fold_left(fun m k=>M.add k(k*7)m)keys(M.empty int).
Definition scan(get:int->M.t int->option int):int:=fold_left(fun acc k=>
 match get k tree with Some value=>acc+value|None=>acc end)keys 0.
Goal scan find=scan (@M.find int).
Proof. Time do 30(let v:=eval vm_compute in(scan (@M.find int))in idtac).
Time do 30(let v:=eval vm_compute in(scan find)in idtac).
Time do 30(let v:=eval vm_compute in(scan (@M.find int))in idtac).
Time do 30(let v:=eval vm_compute in(scan find)in idtac).
vm_compute;reflexivity. Qed.
End FastMapProbe.
