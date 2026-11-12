(* SMTCoq -- distributed under the CeCILL-C licence (see LICENSE). *)
From Stdlib Require Import List String Bool Arith Lia.
From SMTCoq.checker.eunoia Require Import EoSyntax EoRuntime.
Import ListNotations.
Open Scope string_scope.
Module EoCheckedMemo.
Lemma term_eqb_spec : forall a b, term_eqb a b = true <-> a=b.
Proof.
 induction a as [s|f IHf a IHa]; destruct b as [t|g b]; simpl;
 try (split; [discriminate|congruence]).
 - rewrite String.eqb_eq. split; [intro H; subst; reflexivity|intro H; inversion H; reflexivity].
 - change (term_eqb f g && term_eqb a b = true <-> Apply f a = Apply g b).
   rewrite andb_true_iff, IHf, IHa. split; [intros [-> ->]; reflexivity|intro H; inversion H; auto].
Qed.
Fixpoint terms_eqb (xs ys:list term) := match xs,ys with
 | [],[] => true
 | x::xs,y::ys => if term_eqb x y then terms_eqb xs ys else false
 | _,_ => false end.
Lemma terms_eqb_spec : forall xs ys, terms_eqb xs ys = true <-> xs=ys.
Proof.
 induction xs as [|x xs IH]; destruct ys as [|y ys]; simpl;
 try (split; [discriminate|congruence]); [tauto|].
 change ((term_eqb x y && terms_eqb xs ys)=true <-> x::xs=y::ys).
 rewrite andb_true_iff, term_eqb_spec, IH.
 split; [intros [-> ->]; reflexivity|intro H; inversion H; auto].
Qed.
Record cache_entry := Entry { entry_depth:nat; entry_name:string;
 entry_args:list term; entry_value:term }.
(* Explicit branches keep VM evaluation from comparing a large argument
   vector when the small depth/name keys already disagree. *)
Definition key_eqb depth name args e :=
 if Nat.eqb depth (entry_depth e) then
   if String.eqb name (entry_name e) then terms_eqb args (entry_args e)
   else false
 else false.
Lemma key_eqb_equivalence : forall depth name args e,
 key_eqb depth name args e =
 (Nat.eqb depth (entry_depth e) && String.eqb name (entry_name e) && terms_eqb args (entry_args e)).
Proof.
 intros; unfold key_eqb.
 destruct (Nat.eqb depth (entry_depth e)), (String.eqb name (entry_name e)),
   (terms_eqb args (entry_args e)); reflexivity.
Qed.
Fixpoint cache_lookup depth name args (cache:list cache_entry) :=
 match cache with
 | [] => None
 | e::cache => if key_eqb depth name args e
              then Some (entry_value e) else cache_lookup depth name args cache
 end.
Lemma cache_lookup_sound : forall cache depth name args value,
 cache_lookup depth name args cache = Some value ->
 exists e, In e cache /\ entry_depth e=depth /\ entry_name e=name /\
           entry_args e=args /\ entry_value e=value.
Proof.
 induction cache as [|e cache IH]; intros depth name args value H; [discriminate|].
 change ((if key_eqb depth name args e then Some (entry_value e)
   else cache_lookup depth name args cache)=Some value) in H.
 rewrite key_eqb_equivalence in H.
 destruct (Nat.eqb depth (entry_depth e) && String.eqb name (entry_name e) &&
              terms_eqb args (entry_args e)) eqn:He.
 - rewrite !andb_true_iff, Nat.eqb_eq, String.eqb_eq, terms_eqb_spec in He.
   destruct He as [[Hd Hn] Ha]. inversion H; subst value. exists e; split; [left; reflexivity|]. repeat split; try reflexivity; symmetry; assumption.
 - destruct (IH _ _ _ _ H) as [found [Hin Hspec]]. exists found; split; [right; exact Hin|exact Hspec].
Qed.
Definition call_reference nilof extra ops fuel typeof programs name args :=
 match named name programs with
 | None => Missing ("program " ++ name)
 | Some p => match select_case_with nilof typeof (program_cases p) args [] with
   | None => Stuck
   | Some (bs,body) => evaluate_computation nilof extra ops fuel typeof programs bs body
   end
 end.
Definition cache_valid nilof extra ops budget typeof programs cache :=
 forall e, In e cache -> call_reference nilof extra ops (budget-entry_depth e)
   typeof programs (entry_name e) (entry_args e) = Done (entry_value e).
Definition arguments (ev : expression -> computation term) :=
 fix go (xs:list expression) : computation (list term) :=
 match xs with
 | [] => Done []
 | a::tl => match ev a, go tl with
   | Done t,Done ts => Done (t::ts)
   | Missing reason,_ => Missing reason
   | _,Missing reason => Missing reason
   | _,_ => Stuck end
 end.
Lemma arguments_ext : forall f g,
 (forall e, f e=g e) -> forall xs, arguments f xs=arguments g xs.
Proof. intros f g H xs; induction xs; simpl; [reflexivity|now rewrite H, IHxs]. Qed.
Fixpoint evaluate_cached (nilof : nil_query) (extra : primitive_hook)
    (ops : list (string * term)) (budget : nat) (cache : list cache_entry) (fuel depth : nat) (typeof : term -> option term)
    (programs : list (string * program)) (env : bindings) (e : expression)
    : computation term :=
  match fuel with
  | O => Missing "fuel exhausted"
  | S k =>
    let ev := evaluate_cached nilof extra ops budget cache k (S depth) typeof programs env in
    let fix eval_args (xs : list expression) : computation (list term) :=
      match xs with
      | [] => Done []
      | a :: tl =>
          match ev a, eval_args tl with
          | Done t, Done ts => Done (t :: ts)
          | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
          | _, _ => Stuck end
      end in
    let binary a b f := match ev a, ev b with
      | Done x, Done y => f x y
      | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason
      | _, _ => Stuck end in
    match e with
    | ENil op ty => bind_computation (ev ty) (fun t => match nilof op (Some t) with Some z => Done z | None => Missing ("nil " ++ op) end)
    | EVar n => match lookup n env with Some t => Done t | None => Missing "unbound variable" end
    | ESymbol s => Done (Symbol s)
    | EApply f a => binary f a (fun g b => Done (Apply g b))
    | EIsOk a => match ev a with
        | Done _ => Done (bool_term true) | Stuck => Done (bool_term false) | Missing reason => Missing reason end
    | EIsEq a b => match ev a, ev b with
        | Done x, Done y => Done (bool_term (term_eqb x y))
        | Missing reason, _ => Missing reason
          | _, Missing reason => Missing reason | _, _ => Done (bool_term false) end
    | EEq a b => binary a b (fun x y => Done (bool_term (term_eqb x y)))
    | EIf c a b => match ev c with
        | Done (Symbol "true") => ev a | Done (Symbol "false") => ev b
        | Missing reason => Missing reason | _ => Stuck end
    | ERequires a b body => binary a b (fun x y => if term_eqb x y then ev body else Stuck)
    | ETypeof a => bind_computation (ev a) (fun t => match typeof t with Some ty => Done ty | None => Missing "eo::typeof" end)
    | ELet n value body => bind_computation (ev value) (fun t =>
        evaluate_cached nilof extra ops budget cache k (S depth) typeof programs ((n, t) :: env) body)
    | ENative name args =>
        match eval_args args with
        | Missing reason => Missing reason
        | Stuck =>
            if existsb (String.eqb name) ["eo::is_z"; "eo::is_q"; "eo::is_bin"; "eo::is_str"; "eo::is_bool"]
            then Done (bool_term false) else Stuck
        | Done ts => match native_with_nils nilof typeof extra ops name ts with
            | Some t => Done t
            | None =>
                if existsb (String.eqb name)
                    ["eo::not"; "eo::and"; "eo::or"; "eo::xor";
                     "eo::list_rev"; "eo::list_len"; "eo::list_nth"; "eo::list_find";
                     "eo::list_erase"; "eo::list_erase_all"; "eo::list_setof"; "eo::list_concat";
                     "eo::list_diff"; "eo::list_inter"; "eo::list_minclude"; "eo::list_meq";
                     "eo::list_singleton_elim"; "eo::list_singleton_intro"; "eo::list_repeat";
                     "eo::cons"; "eo::nil"] then Stuck
                else match extra "eo::supports" [Symbol name] with
                | Some (Symbol "true") => Stuck | _ => Missing name end
            end
        end
    | ECall name args =>
        match named name programs, eval_args args with
        | Some p, Done ts =>
            match cache_lookup (S depth) name ts cache with
            | Some value => Done value
            | None => match select_case_with nilof typeof (program_cases p) ts [] with
              | Some (bs, body) => evaluate_cached nilof extra ops budget cache k (S depth) typeof programs bs body
              | None => Stuck end
            end
        | None, _ => Missing ("program " ++ name)
        | _, Missing reason => Missing reason
        | _, _ => Stuck
        end
    end
  end.

Theorem evaluate_cached_refinement : forall nilof extra ops budget cache typeof programs,
 cache_valid nilof extra ops budget typeof programs cache ->
 forall fuel depth env e, fuel+depth=budget ->
 evaluate_cached nilof extra ops budget cache fuel depth typeof programs env e =
 evaluate_computation nilof extra ops fuel typeof programs env e.
Proof.
 intros nilof extra ops budget cache typeof programs Hcache fuel.
 induction fuel as [|fuel IH]; intros depth env e Hbudget; [reflexivity|].
 assert (Hrec : forall env e,
   evaluate_cached nilof extra ops budget cache fuel (S depth) typeof programs env e =
   evaluate_computation nilof extra ops fuel typeof programs env e).
 { intros; apply IH; lia. }
 destruct e; cbn [evaluate_cached evaluate_computation].
 all: fold evaluate_cached evaluate_computation.
 all: try (repeat rewrite Hrec; reflexivity).
 all: try (unfold bind_computation; rewrite Hrec; destruct (evaluate_computation nilof extra ops fuel typeof programs env e1); try reflexivity; apply Hrec).
 all: try reflexivity.
 all: fold (arguments (evaluate_cached nilof extra ops budget cache fuel (S depth) typeof programs env)).
 all: fold (arguments (evaluate_computation nilof extra ops fuel typeof programs env)).
 all: rewrite (arguments_ext _ _ (Hrec env)).
 all: try reflexivity.
 destruct (named s programs) as [p|] eqn:Hnamed; [|reflexivity].
 destruct (arguments (evaluate_computation nilof extra ops fuel typeof programs env) l)
   as [ts| |reason]; try reflexivity.
 destruct (cache_lookup (S depth) s ts cache) as [value|] eqn:Hlookup.
 - destruct (cache_lookup_sound _ _ _ _ _ Hlookup) as [entry [Hin [Hd [Hn [Ha Hv]]]]].
   pose proof (Hcache entry Hin) as Hvalid.
   unfold call_reference in Hvalid.
   rewrite Hd, Hn, Ha, Hv, Hnamed in Hvalid.
   replace (budget-S depth) with fuel in Hvalid by lia.
   symmetry; exact Hvalid.
 - destruct (select_case_with nilof typeof (program_cases p) ts []) as [[bs body]|];
     try reflexivity; apply Hrec.
Qed.
Print Assumptions evaluate_cached_refinement.

Definition call_cached nilof extra ops budget cache depth typeof programs name args :=
 match named name programs with
 | None => Missing ("program " ++ name)
 | Some p => match select_case_with nilof typeof (program_cases p) args [] with
   | None => Stuck
   | Some (bs,body) => evaluate_cached nilof extra ops budget cache (budget-depth) depth
       typeof programs bs body
   end
 end.
Lemma call_cached_refinement : forall nilof extra ops budget cache depth typeof programs name args,
 cache_valid nilof extra ops budget typeof programs cache -> depth<=budget ->
 call_cached nilof extra ops budget cache depth typeof programs name args =
 call_reference nilof extra ops (budget-depth) typeof programs name args.
Proof.
 intros. unfold call_cached, call_reference.
 destruct (named name programs) as [p|]; [|reflexivity].
 destruct (select_case_with nilof typeof (program_cases p) args []) as [[bs body]|]; [|reflexivity].
 apply evaluate_cached_refinement; [assumption|lia].
Qed.
Definition entry_check nilof extra ops budget cache typeof programs e :=
 Nat.leb (entry_depth e) budget &&
 match call_cached nilof extra ops budget cache (entry_depth e) typeof programs
     (entry_name e) (entry_args e) with
 | Done v => term_eqb v (entry_value e)
 | _ => false
 end.
Lemma entry_check_sound : forall nilof extra ops budget cache typeof programs e,
 cache_valid nilof extra ops budget typeof programs cache ->
 entry_check nilof extra ops budget cache typeof programs e = true ->
 call_reference nilof extra ops (budget-entry_depth e) typeof programs
   (entry_name e) (entry_args e) = Done (entry_value e).
Proof.
 intros nilof extra ops budget cache typeof programs e Hcache Hcheck.
 unfold entry_check in Hcheck. apply andb_true_iff in Hcheck. destruct Hcheck as [Hbound Hcheck].
 apply Nat.leb_le in Hbound.
 rewrite call_cached_refinement in Hcheck by assumption.
 destruct (call_reference nilof extra ops (budget-entry_depth e) typeof programs
   (entry_name e) (entry_args e)) as [value| |reason] eqn:Hvalue; try discriminate.
 apply term_eqb_spec in Hcheck. now subst value.
Qed.
Fixpoint validate_entries nilof extra ops budget typeof programs (entries:list cache_entry) :=
 match entries with
 | [] => Some []
 | e::entries => match validate_entries nilof extra ops budget typeof programs entries with
   | None => None
   | Some cache => if entry_check nilof extra ops budget cache typeof programs e
                   then Some (e::cache) else None
   end
 end.
Theorem validate_entries_sound : forall nilof extra ops budget typeof programs entries cache,
 validate_entries nilof extra ops budget typeof programs entries = Some cache ->
 cache_valid nilof extra ops budget typeof programs cache.
Proof.
 intros nilof extra ops budget typeof programs entries; induction entries as [|e entries IH];
 intros cache H; simpl in H.
 - inversion H; subst. intros x Hx; inversion Hx.
 - destruct (validate_entries nilof extra ops budget typeof programs entries) as [prior|] eqn:Hp;
     try discriminate.
   destruct (entry_check nilof extra ops budget prior typeof programs e) eqn:He; try discriminate.
   inversion H; subst cache. specialize (IH prior eq_refl).
   intros x [Hx|Hx].
   + subst x; eapply entry_check_sound; eauto.
   + exact (IH x Hx).
Qed.
Print Assumptions validate_entries_sound.
Definition checked_evaluate nilof extra ops budget typeof programs entries env e :=
 match validate_entries nilof extra ops budget typeof programs entries with
 | None => None
 | Some cache => computed (evaluate_cached nilof extra ops budget cache budget 0 typeof programs env e)
 end.
Theorem checked_evaluate_correct : forall nilof extra ops budget typeof programs entries env e value,
 checked_evaluate nilof extra ops budget typeof programs entries env e = Some value ->
 evaluate_with_nils nilof extra ops budget typeof programs env e = Some value.
Proof.
 intros nilof extra ops budget typeof programs entries env e value H.
 unfold checked_evaluate in H.
 destruct (validate_entries nilof extra ops budget typeof programs entries) as [cache|] eqn:Hcache;
   try discriminate.
 pose proof (validate_entries_sound nilof extra ops budget typeof programs entries cache Hcache) as Hvalid.
 rewrite evaluate_cached_refinement in H by (try assumption; lia).
 exact H.
Qed.
Print Assumptions checked_evaluate_correct.
End EoCheckedMemo.
