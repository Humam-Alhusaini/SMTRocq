(* Fixed semantic array certificates: no solver or native search is required. *)
From Stdlib Require Import List Bool Uint63.
From SMTCoq.utils Require Import PArray CompDec.
From SMTCoq.structures Require Import CompDecInstances.
From SMTCoq.checker.fol Require Import State Terms.
From SMTCoq.checker Require Import MainChecker.
From SMTCoq.checker.eunoia Require Import EunoiaLocal.
Import ListNotations EunoiaLocal.
Local Open Scope uint63_scope.
Local Open Scope array_scope.
Module EunoiaArrayTests.
Definition sorts:=make 0 unit_typ_compdec.
Definition arr:=Typ.TFArray Typ.TZ Typ.TZ.
Definition value ty:=@Atom.Tval sorts ([],ty)
  (@default_value _ (@inh_of_compdec _ (Typ.interp_compdec sorts ty))).
Definition funcs:array(Atom.tval sorts):=
  (make 5 (value Typ.Tbool)).[0<-value arr].[1<-value Typ.TZ]
    .[2<-value Typ.TZ].[3<-value Typ.TZ].[4<-value arr].
Definition atoms:array Atom.atom:=
  (make 18 (Atom.Acop Atom.CO_xH))
    .[1<-Atom.Aapp 0 []].[2<-Atom.Aapp 1 []].[3<-Atom.Aapp 2 []]
    .[4<-Atom.Aapp 3 []].[5<-Atom.Atop (Atom.TO_store Typ.TZ Typ.TZ) 1 2 4]
    .[6<-Atom.Abop (Atom.BO_select Typ.TZ Typ.TZ) 5 2]
    .[7<-Atom.Abop (Atom.BO_eq Typ.TZ) 6 4]
    .[8<-Atom.Abop (Atom.BO_select Typ.TZ Typ.TZ) 5 3]
    .[9<-Atom.Abop (Atom.BO_select Typ.TZ Typ.TZ) 1 3]
    .[10<-Atom.Abop (Atom.BO_eq Typ.TZ) 2 3]
    .[11<-Atom.Abop (Atom.BO_eq Typ.TZ) 8 9]
    .[12<-Atom.Aapp 4 []]
    .[13<-Atom.Abop (Atom.BO_diffarray Typ.TZ Typ.TZ) 1 12]
    .[14<-Atom.Abop (Atom.BO_select Typ.TZ Typ.TZ) 1 13]
    .[15<-Atom.Abop (Atom.BO_select Typ.TZ Typ.TZ) 12 13]
    .[16<-Atom.Abop (Atom.BO_eq arr) 1 12]
    .[17<-Atom.Abop (Atom.BO_eq Typ.TZ) 14 15].
Definition forms:array Form.form:=
  (make 8 Form.Ftrue).[1<-Form.Ffalse].[2<-Form.Fatom 7]
    .[3<-Form.Fatom 10].[4<-Form.Fatom 11].[5<-Form.Fatom 16]
    .[6<-Form.Fatom 17].[7<-Form.For ((make 2 10).[1<-13])].
Definition resolve p a b c:=Command (Checker_Ext.Res p ((make 2 a).[1<-b])) c.
Definition same_program:=[ArrayCommand 1 (ArrayReadSame 4) [4];resolve 2 0 1 []].
Definition same:=Witness 3 [(0,[5])] same_program 2.
Definition other:=Witness 5 [(0,[7]);(1,[9])]
  [ArrayCommand 2 (ArrayReadOther [6;8]) [6;8];
   resolve 3 0 2 [8];resolve 4 1 3 []] 4.
Definition ext:=Witness 7 [(0,[11]);(1,[12])]
  [ArrayCommand 2 (ArrayExtensionality 14) [14];
   Command (Checker_Ext.BuildDef 3 15) [10;13;15];
   resolve 4 2 3 [10;13];resolve 5 0 4 [13];resolve 6 1 5 []] 6.
Definition check cs c w:=Atom.wt sorts funcs atoms && @gate sorts funcs atoms forms cs c w.
Example typed_tables:Form.check_form forms && Atom.check_atom atoms && Atom.wt sorts funcs atoms=true.
Proof. vm_compute;reflexivity. Qed.
Example array_same:check [] [4] same=true.
Proof. vm_compute;reflexivity. Qed.
Example array_other:check [[7]] [8] other=true.
Proof. vm_compute;reflexivity. Qed.
Example array_extensionality:check [] [10;13] ext=true.
Proof. vm_compute;reflexivity. Qed.
Example canonicalized_array_output:
 @execute_array atoms forms.[3<-Form.Fatom 11].[4<-Form.Fatom 10]
 (initial 1) 0 (ArrayReadOther [8;6]) [6;8]<>
 None.
Proof. vm_compute;discriminate. Qed.
Example missing_index_disequality:check [] [8] other=false.
Proof. vm_compute;reflexivity. Qed.
Example wrong_array_polarity:check [] [4]
 (Witness 3 [(0,[5])] [ArrayCommand 1 (ArrayReadSame 5) [4];resolve 2 0 1 []] 2)=false.
Proof. vm_compute;reflexivity. Qed.
Example wrong_row_order:check [[7]] [8]
 (Witness 5 [(0,[7]);(1,[9])]
 [ArrayCommand 2 (ArrayReadOther [8;6]) [6;8];resolve 3 0 2 [8];resolve 4 1 3 []] 4)=false.
Proof. vm_compute;reflexivity. Qed.
Example unsupported_array_shape:check [] [4]
 (Witness 3 [(0,[5])] [ArrayCommand 1 (ArrayReadSame 6) [4];resolve 2 0 1 []] 2)=false.
Proof. vm_compute;reflexivity. Qed.
Example array_input_out_of_bounds:check [] [4]
 (Witness 3 [(0,[5])] [ArrayCommand 1 (ArrayReadSame 200) [4];resolve 2 0 1 []] 2)=false.
Proof. vm_compute;reflexivity. Qed.
Example array_destination_reused:check [] [4]
 (Witness 2 [(0,[5])] [ArrayCommand 0 (ArrayReadSame 4) [4];resolve 1 0 0 []] 1)=false.
Proof. vm_compute;reflexivity. Qed.
Example invalid_array_after_conflict:check [] [4]
 (Witness 4 [(0,[5])] (same_program++[ArrayCommand 3 (ArrayReadSame 200) []]) 2)=false.
Proof. vm_compute;reflexivity. Qed.
Example wrong_difference_witness:
 Atom.wt sorts funcs atoms.[13<-Atom.Abop (Atom.BO_diffarray Typ.TZ Typ.TZ) 1 1] &&
 @gate sorts funcs atoms.[13<-Atom.Abop (Atom.BO_diffarray Typ.TZ Typ.TZ) 1 1] forms [] [10;13] ext=false.
Proof. vm_compute;reflexivity. Qed.
End EunoiaArrayTests.
