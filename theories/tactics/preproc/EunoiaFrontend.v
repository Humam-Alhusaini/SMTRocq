(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE).
   Proof-producing translation for the quantifier-free UF/LIA front end.
   Unsupported propositions retain the existing Trakt preprocessing path. *)
From Stdlib Require Import Bool ZArith.
From Ltac2 Require Import Ltac2.
From SMTCoq.utils Require Import Misc CompDec.
Require Import ReflectFacts.
Set Default Proof Mode "Classic".
Module EunoiaFrontend.
Lemma and_iff P Q a b : (P <-> a=true)->(Q <-> b=true)->(P/\Q <-> andb a b=true).
Proof. intros HP HQ;rewrite andb_true_iff,<-HP,<-HQ;reflexivity. Qed.
Lemma or_iff P Q a b : (P <-> a=true)->(Q <-> b=true)->(P\/Q <-> orb a b=true).
Proof. intros HP HQ;rewrite orb_true_iff,<-HP,<-HQ;reflexivity. Qed.
Lemma impl_iff P Q a b : (P <-> a=true)->(Q <-> b=true)->((P->Q) <-> implb a b=true).
Proof. intros HP HQ;rewrite HP,HQ;apply reflect_iff,implyP. Qed.
Lemma iff_iff P Q a b : (P <-> a=true)->(Q <-> b=true)->((P<->Q) <-> Bool.eqb a b=true).
Proof. intros HP HQ;rewrite HP,HQ;apply reflect_iff,iffP. Qed.
Lemma not_iff P a : (P <-> a=true)->(~P <-> negb a=true).
Proof. intro HP;rewrite HP;apply reflect_iff,negP. Qed.
Lemma bool_true_iff (a:bool) : (a=true)<->a=true.
Proof. reflexivity. Qed.
Ltac2 unsupported () := Control.zero (Tactic_failure (Some (Message.of_string "EunoiaFrontend: unsupported proposition"))).
Ltac2 rec find_compdec ty hs :=
 match hs with
 | [] => unsupported ()
 | (id,_,t)::rest =>
   lazy_match! t with
   | CompDec.CompDec ?a => if Constr.equal ty a then Control.hyp id else find_compdec ty rest
   | _ => find_compdec ty rest
   end
 end.
Ltac2 rec reflect_prop p :=
 lazy_match! p with
 | True => ('true, '(iff_sym TrueB))
 | False => ('false, '(iff_sym FalseB))
 | ?a /\ ?b =>
   let (x,hx):=reflect_prop a in let(y,hy):=reflect_prop b in
   ('(andb $x $y),'(@and_iff $a $b $x $y $hx $hy))
 | ?a \/ ?b =>
   let(x,hx):=reflect_prop a in let(y,hy):=reflect_prop b in
   ('(orb $x $y),'(@or_iff $a $b $x $y $hx $hy))
 | ?a <-> ?b =>
   let(x,hx):=reflect_prop a in let(y,hy):=reflect_prop b in
   ('(Bool.eqb $x $y),'(@iff_iff $a $b $x $y $hx $hy))
 | ~ ?a => let(x,hx):=reflect_prop a in ('(negb $x),'(@not_iff $a $x $hx))
 | ?a -> ?b =>
   let(x,hx):=reflect_prop a in let(y,hy):=reflect_prop b in
   ('(implb $x $y),'(@impl_iff $a $b $x $y $hx $hy))
 | @eq bool ?a true => (a,'(bool_true_iff $a))
 | @eq bool ?a ?b => ('(Bool.eqb $a $b),'(reflect_iff _ _ (eqP $a $b)))
 | @eq Z ?a ?b => ('(Z.eqb $a $b),'(iff_sym (Z.eqb_eq $a $b)))
 | Z.le ?a ?b => ('(Z.leb $a $b),'(iff_sym (Z.leb_le $a $b)))
 | Z.lt ?a ?b => ('(Z.ltb $a $b),'(iff_sym (Z.ltb_lt $a $b)))
 | Z.ge ?a ?b => ('(Z.leb $b $a),'(iff_sym (Z.leb_le $b $a)))
 | Z.gt ?a ?b => ('(Z.ltb $b $a),'(iff_sym (Z.ltb_lt $b $a)))
 | @eq ?a ?x ?y =>
   let c:=find_compdec a (Control.hyps ()) in
   ('(@CompDec.eqb_of_compdec $a $c $x $y),'(@CompDec.compdec_eq_eqb $a $c $x $y))
 | _ => unsupported ()
 end.
(* Build one equivalence proof per proposition, then convert each actual
   hypothesis once. The backend receives proof terms, not asserted truth values. *)
Ltac2 prepare () :=
 let ps:=List.map(fun(id,_)=>
   let h:=Control.hyp id in let p:=Constr.type h in
   let(_,hb):=reflect_prop p in '(proj1 $hb $h)) (get_hyps_prop ()) in
 let p:=Control.goal () in let(_,hb):=reflect_prop p in
 (tupleify ps, '(proj2 $hb)).
End EunoiaFrontend.
