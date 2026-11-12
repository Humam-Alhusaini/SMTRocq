(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import String List Bool Arith.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
From SMTCoq.checker.eunoia Require Import EoCheckedMemo.
Import ListNotations EoCheckedMemo.EoCheckedMemo.
Open Scope string_scope.
(* Producer only. Every emitted entry must pass validate_entries. *)
Definition native_result nilof typeof extra ops name result :=
 match result with
 | Missing reason => Missing reason
 | Stuck => if existsb (String.eqb name) ["eo::is_z";"eo::is_q";"eo::is_bin";"eo::is_str";"eo::is_bool"]
              then Done (bool_term false) else Stuck
 | Done ts => match native_with_nils nilof typeof extra ops name ts with
   | Some t => Done t
   | None => if existsb (String.eqb name)
       ["eo::not";"eo::and";"eo::or";"eo::xor";"eo::list_rev";"eo::list_len";"eo::list_nth";"eo::list_find";
        "eo::list_erase";"eo::list_erase_all";"eo::list_setof";"eo::list_concat";"eo::list_diff";"eo::list_inter";
        "eo::list_minclude";"eo::list_meq";"eo::list_singleton_elim";"eo::list_singleton_intro";"eo::list_repeat";
        "eo::cons";"eo::nil"] then Stuck else
       match extra "eo::supports" [Symbol name] with Some (Symbol "true")=>Stuck|_=>Missing name end
   end
 end.
Fixpoint evaluate_logged (nilof:nil_query) (extra:primitive_hook) (ops:list (string*term))
 (fuel depth:nat) (typeof:term->option term) (programs:list(string*program)) (env:bindings) (e:expression)
 : computation term * list cache_entry :=
 match fuel with
 | O => (Missing "fuel exhausted",[])
 | S k =>
 let ev := evaluate_logged nilof extra ops k (S depth) typeof programs env in
 let fix args xs : computation (list term) * list cache_entry :=
   match xs with
   | [] => (Done [],[])
   | a::tl => let '(ra,la):=ev a in let '(rs,ls):=args tl in
     ((match ra,rs with Done t,Done ts=>Done(t::ts)|Missing reason,_=>Missing reason
       |_,Missing reason=>Missing reason|_,_=>Stuck end),(la++ls)%list)
   end in
 let binary a b f := let '(ra,la):=ev a in let '(rb,lb):=ev b in
   ((match ra,rb with Done x,Done y=>f x y|Missing reason,_=>Missing reason
     |_,Missing reason=>Missing reason|_,_=>Stuck end),(la++lb)%list) in
 match e with
 | EVar n => (match lookup n env with Some t=>Done t|None=>Missing "unbound variable" end,[])
 | ESymbol s => (Done (Symbol s),[])
 | EApply a b => binary a b (fun x y=>Done(Apply x y))
 | ENil op ty => let '(r,l):=ev ty in
   (bind_computation r (fun t=>match nilof op (Some t) with Some z=>Done z|None=>Missing("nil "++op) end),l)
 | EIsOk a => let '(r,l):=ev a in
   (match r with Done _=>Done(bool_term true)|Stuck=>Done(bool_term false)|Missing reason=>Missing reason end,l)
 | EIsEq a b => let '(ra,la):=ev a in let '(rb,lb):=ev b in
   (match ra,rb with Done x,Done y=>Done(bool_term(term_eqb x y))|Missing reason,_=>Missing reason
    |_,Missing reason=>Missing reason|_,_=>Done(bool_term false) end,(la++lb)%list)
 | EEq a b => binary a b (fun x y=>Done(bool_term(term_eqb x y)))
 | ETypeof a => let '(r,l):=ev a in
   (bind_computation r (fun t=>match typeof t with Some ty=>Done ty|None=>Missing "eo::typeof" end),l)
 | EIf c a b => let '(r,l):=ev c in
   match r with
   | Done (Symbol "true") => let '(r',l'):=ev a in (r',(l'++l)%list)
   | Done (Symbol "false") => let '(r',l'):=ev b in (r',(l'++l)%list)
   | Missing reason => (Missing reason,l)
   | _ => (Stuck,l)
   end
 | ERequires a b body => let '(ra,la):=ev a in let '(rb,lb):=ev b in
   match ra,rb with
   | Done x,Done y => if term_eqb x y then let '(r,l):=ev body in (r,(l++la++lb)%list)
                     else (Stuck,(la++lb)%list)
   | Missing reason,_ => (Missing reason,(la++lb)%list)
   | _,Missing reason => (Missing reason,(la++lb)%list)
   | _,_ => (Stuck,(la++lb)%list)
   end
 | ELet n value body => let '(r,l):=ev value in
   match r with
   | Done t => let '(r',l'):=evaluate_logged nilof extra ops k (S depth) typeof programs ((n,t)::env) body in
     (r',(l'++l)%list)
   | _ => (r,l)
   end
 | ENative name xs => let '(r,l):=args xs in (native_result nilof typeof extra ops name r,l)
 | ECall name xs => let '(r,l):=args xs in
   match named name programs,r with
   | Some p,Done ts => match select_case_with nilof typeof (program_cases p) ts [] with
     | None => (Stuck,l)
     | Some (bs,body) => let '(r',l'):=evaluate_logged nilof extra ops k (S depth) typeof programs bs body in
       (r',match r' with Done v=>Entry (S depth) name ts v::(l'++l)%list|_=>(l'++l)%list end)
     end
   | None,_ => (Missing ("program "++name),l)
   | _,Missing reason => (Missing reason,l)
   | _,_ => (Stuck,l)
   end
 end
 end.
