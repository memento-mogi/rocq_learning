From Stdlib Require Import Nat List FunctionalExtensionality.
From Fomega Require Export Definitions.

Ltac dauto := try (intros _x; destruct _x; auto).

(* Properties *)
Lemma renTm_typing : forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' (xi x) = Some S) ->
  <[ Delta | Gamma' |-- {ren_Tm id xi t} \in T ]> .
Proof.
  intros Delta Gamma t T H.
  induction H; intros; asolve.
  - apply T_Var. apply H0. assumption.
  - apply T_Abs; try assumption.
    apply IHhas_type. intros. destruct x.
    + simpl in *. assumption.
    + simpl in *. apply H1. assumption.
  - eapply T_App; eauto.
  - eapply T_TAbs; try reflexivity.
    subst GammaS.
    rewrite extRen_Tm with (zeta_Ty:=id) (zeta_Tm:=xi); dauto.
    apply IHhas_type. intros.
    rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [S'|] eqn: EqGx;
    try discriminate.
    rewrite H1 with (S:=S'); try assumption.
  - eapply T_TApp; try eauto.
  - eapply T_Conv; try eauto.
  - apply T_Unit.
Qed.

Lemma renTy_kinding : forall Delta T K,
  <[[ Delta |-- T \in K ]]> ->
  forall Delta' xi,
  (forall X J, nth_error Delta X = Some J -> 
              nth_error Delta' (xi X) = Some J) ->
  <[[ Delta' |-- {ren_Ty xi T} \in K ]]>. 
Proof.
  intros Delta T K H.
  induction H; intros; asolve;
  try (econstructor; auto).
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
Qed.

Lemma renTy_tyeval : forall T1 T2, 
  T1 ==> T2 -> 
  forall xi,
  (ren_Ty xi T1) ==> (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor; apply IHtype_eval_step).
  - subst S. asolve. apply TST_Red. asolve.
    apply ext_Ty. intros. unfold sigma_ty_one. destruct x; asolve.  
Qed.

Lemma renTy_tyeq : forall T1 T2,
  T1 === T2 -> 
  forall xi,
  (ren_Ty xi T1) === (ren_Ty xi T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - apply multi_refl.
  - apply multi_step with (T2:=ren_Ty xi T2).
    + destruct H; [left | right]; apply renTy_tyeval; assumption.
    + apply IHmulti.
Qed.
  
Lemma renTy_typing : forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' Delta' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' x = Some (ren_Ty xi S)) ->
  (forall X K, nth_error Delta X = Some K -> 
              nth_error Delta' (xi X) = Some K) ->
  <[ Delta' | Gamma' |-- {ren_Tm xi id t} \in {ren_Ty xi T} ]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros Gamma' Delta' xi HG HD; asolve.
  - apply T_Var. apply HG. assumption.
  - eapply T_Abs.
    + eapply renTy_kinding; eassumption.
    + erewrite extRen_Tm.
      * apply IHhas_type. 
        { intros. destruct x; simpl; simpl in H1.
          - inversion H1. reflexivity.
          - apply HG. assumption. }
        { intros. apply HD. assumption. }
      * reflexivity.
      * intros. destruct x; auto.
  - eapply T_App; eauto.
  - eapply T_TAbs; try reflexivity.
    subst GammaS. apply IHhas_type. 
    + intros. rewrite nth_error_map in *.
      destruct (nth_error Gamma x) as [S'|] eqn: EqGx;
      try discriminate. simpl in H0. inversion H0.
      rewrite HG with (S:=S'); try assumption.
      asolve. 
    + intros. destruct X; auto.
      simpl in *. auto.
  - simpl in IHhas_type.
    eapply T_TApp with (K:=K);
    unfold sigma_ty_one in *; subst T1';
    try apply IHhas_type.
    + asolve.
    + auto.
    + asolve. apply ext_Ty. intros. destruct x; asolve.
    + eapply renTy_kinding; eassumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + apply renTy_tyeq. assumption.
  - apply T_Unit.
Qed.

Lemma tmsubst_preserves_typing :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S -> <[ Delta | Gamma' |-- {sigma x} \in S ]>) ->
  <[ Delta | Gamma' |-- {subst_Tm id sigma t} \in T ]>.
Proof.
  intros Delta Gamma t T.
  intro H. induction H; intros; asolve.
  - apply T_Abs; try assumption.
    apply IHhas_type. intros. destruct x.
    + apply T_Var. assumption.
    + apply renTm_typing with (Gamma').
      * simpl in H2. apply H1. assumption.
      * intros. simpl. assumption. 
  - apply T_App with (T1:=T1).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - eapply T_TAbs; try reflexivity.
    erewrite ext_Tm with (tau_Ty:=id); try reflexivity; dauto.
    apply IHhas_type. intros.
    subst GammaS. rewrite nth_error_map in H2.
    destruct (nth_error Gamma x) as [S'|] eqn: EqGx; try discriminate.
    simpl in H2. inversion H2. eapply renTy_typing.
    + apply H1. assumption.
    + intros. rewrite nth_error_map. rewrite H0. reflexivity.
    + intros. simpl. assumption.
  - eapply T_TApp; try eassumption.
    apply IHhas_type. assumption.
  - eapply T_Conv; try eassumption.
    apply IHhas_type. assumption.
  - constructor.
Qed.

Lemma tysubst_preserves_kinding : 
  forall Delta T K,
  <[[ Delta |-- T \in K ]]> ->
  forall sigma Delta',
  ( forall X J, nth_error Delta X = Some J ->
    <[[ Delta' |-- {sigma X} \in J ]]> ) ->
  <[[ Delta' |-- {subst_Ty sigma T} \in K ]]>. 
Proof.
  intros Delta T K H.
  induction H; intros; asolve.
  - apply K_Abs. apply IHhas_kind. intros.
    destruct X.
    + apply K_TVar. assumption.
    + apply renTy_kinding with Delta'.
      * apply H0. assumption.
      * intros. assumption.
  - apply K_App with K2.
    + apply IHhas_kind1. assumption.
    + apply IHhas_kind2. assumption.
  - apply K_Arr.
    + apply IHhas_kind1. assumption.
    + apply IHhas_kind2. assumption.
  - apply K_All. apply IHhas_kind.
    intros. destruct X.
    + apply K_TVar. assumption.
    + apply renTy_kinding with Delta'.
      * apply H0. assumption.
      * intros. assumption.
  - apply K_Unit.
Qed.

Lemma tysubst_preserves_tyeval : 
  forall T1 T2,
  T1 ==> T2 ->
  forall sigma,
  (subst_Ty sigma T1) ==> (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros; asolve;
  try (constructor; apply IHtype_eval_step).
  - subst S. apply TST_Red. asolve. unfold sigma_ty_one.
    apply ext_Ty. intros. asolve. destruct x; asolve.
    + apply ext_Ty. intros x. rewrite renRen_Ty. asolve.
    + rewrite idSubst_Ty; auto.
Qed.

Lemma tysubst_preserves_tyeq : 
  forall T1 T2,
  T1 === T2 ->
  forall sigma,
  (subst_Ty sigma T1) === (subst_Ty sigma T2).
Proof.
  intros T1 T2 H. induction H; intros.
  - apply multi_refl.
  - apply multi_step with (T2:=subst_Ty sigma T2).
    + destruct H; [left|right]; apply tysubst_preserves_tyeval;
      assumption.
    + apply IHmulti.
Qed.

Lemma tysubst_preserves_typing :
  forall Delta Gamma t T, 
  <[ Delta | Gamma |-- t \in T ]> ->
  forall sigma Gamma',
  ( forall x U, nth_error Gamma x = Some U ->
    nth_error Gamma' x = Some (subst_Ty sigma U) ) ->
  forall Delta',
  ( forall X K, nth_error Delta X = Some K ->
    <[[ Delta' |-- {sigma X} \in K ]]> ) ->
  <[ Delta' | Gamma' |-- {subst_Tm sigma id t} \in {subst_Ty sigma T} ]>.
Proof.
  intros Delta Gamma t T H.
  induction H; intros sigma Gamma' HG Delta' HD; asolve.
  - apply T_Var. apply HG. apply H.
  - apply T_Abs.
    + apply tysubst_preserves_kinding with Delta; assumption.
    + asimpl. rewrite ext_Tm with (tau_Ty:=sigma) (tau_Tm:=id).
      * apply IHhas_type.
        { intros. destruct x.
          - simpl. inversion H1. reflexivity.
          - simpl. simpl in H1. apply HG. assumption. }
        { assumption. }
      * reflexivity.
      * intro x. destruct x; auto.
  - apply T_App with (subst_Ty sigma T1).
    + apply IHhas_type1; assumption.
    + apply IHhas_type2; assumption.
  - apply T_TAbs with (map (ren_Ty S) Gamma'); try reflexivity.
    subst GammaS. apply IHhas_type.
    + intros. rewrite nth_error_map in *.
      destruct (nth_error Gamma x) as [U'|] eqn: EqGx; try discriminate.
      simpl in H0. rewrite (HG x U' EqGx). simpl. f_equal.
      inversion H0. asolve.
    + intros. destruct X.
      * apply K_TVar. assumption.
      * apply renTy_kinding with Delta'.
        { apply HD. assumption. }
        { intros. assumption. }
  - apply T_TApp with (K:=K) (T1:=(subst_Ty (up_Ty_Ty sigma) T1)).
    + apply IHhas_type.
      * intros. apply HG. assumption.
      * assumption.
    + subst T1'. asolve. apply ext_Ty. intros.
      destruct x; asolve.
      symmetry. apply idSubst_Ty. reflexivity.
    + apply tysubst_preserves_kinding with Delta; assumption.
  - eapply T_Conv.
    + apply IHhas_type; assumption.
    + apply tysubst_preserves_tyeq. assumption. 
  - apply T_Unit.
Qed.

Lemma multi_append : 
  forall X R (S T U: X), (multi R S T) /\ (R T U) -> (multi R S U).
Proof.
  intros. destruct H. generalize dependent U.
  induction H; intros.
  - apply multi_step with U.
    + assumption.
    + apply multi_refl.
  - apply multi_step with T2.
    + assumption.
    + apply IHmulti. assumption.
Qed.

Definition tyeval_append := multi_append Ty type_eval_step.
Definition tyeq_append := multi_append Ty type_eval_step_lr.

Lemma tyeq_sym :
  forall S T, S === T -> T === S.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply tyeq_append with T2. split.
    + assumption.
    + destruct H; [right | left]; assumption.
Qed.

Lemma tyeq_trans :
  forall S T U, (S === U) /\ (U === T) -> S === T.
Proof.
  intros. destruct H as [HS HT].
  generalize dependent T. induction HS; intros U H1.
  - assumption.
  - apply multi_step with T2.
    + assumption.
    + apply IHHS. assumption.
Qed.

Lemma multi_step_implies_tyeq : 
  forall S T, multi type_eval_step S T -> S === T.
Proof.
  intros. induction H.
  - apply multi_refl.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHmulti.
Qed.

Lemma equivalent_types_have_same_contractum: 
  forall S T,
  S === T ->
  exists U, ((multi type_eval_step S U) /\ (multi type_eval_step T U)).
Proof.
  intros. induction H.
  - exists T. split; apply multi_refl.
  - destruct IHmulti as [U' [IHT2 IHT3] ]. destruct H.
    + exists U'. split.
      * apply multi_step with T2; assumption.
      * assumption.
    + inversion IHT2.
      * subst U'. exists T1. split.
        { apply multi_refl. }
        { apply tyeval_append with T2. split; assumption. }
      * replace T4 with T1 in *.
        { exists U'. split; assumption. }
        { admit. }
Admitted.

Lemma confluence_implies_tyeq : 
  forall S T U,
  multi type_eval_step S U /\ multi type_eval_step T U ->
  S === T.
Proof.
  intros. destruct H as [HS HT]. induction HS.
  - apply tyeq_sym. apply multi_step_implies_tyeq. assumption.
  - apply multi_step with T2.
    + left. assumption.
    + apply IHHS. assumption.
Qed.

(* TmAbs invesion *)
Lemma tyeval_preserves_type_form_fun :
  forall S1 S2 T, 
  multi type_eval_step <{{S1 -> S2}}> T ->
  exists T1 T2,
  T = <{{T1 -> T2}}> /\ (multi type_eval_step S1 T1) /\ (multi type_eval_step S2 T2).
Proof.
  intros. remember <{{S1 -> S2}}> as S.
  generalize dependent HeqS. generalize dependent S2. generalize dependent S1.
  induction H; intros.
  - exists S1, S2; repeat split; try assumption; apply multi_refl.
  - rename T1 into S, T2 into U, T3 into T.
    subst S. inversion H.
    + rename S0 into U1. symmetry in H2. subst T1 T2.
      apply IHmulti in H2 as [T1 [T2 [HT [H1 H2] ] ] ].
      exists T1, T2. repeat split; try assumption.
      * apply multi_step with U1; assumption. 
    + rename S0 into U2. symmetry in H2. subst T1 T2.
      apply IHmulti in H2 as [T1 [T2 [HT [H1 H2] ] ] ].
      exists T1, T2. repeat split; try assumption.
      * apply multi_step with U2; assumption.
Qed.

Lemma invert_tyeq_fun : 
  forall S1 S2 T1 T2, 
  <{{S1 -> S2}}> === <{{T1 -> T2}}> ->
  (S1 === T1) /\ (S2 === T2).
Proof.
  intros. apply equivalent_types_have_same_contractum in H as [U [H1 H2] ]. 
  apply tyeval_preserves_type_form_fun in H1 as [U1 [U2 [HU [H11 H12] ] ] ].
  apply tyeval_preserves_type_form_fun in H2 as [V1 [V2 [HV [H21 H22] ] ] ].
  subst U. inversion HV. subst V1 V2. clear HV. split;
  eapply confluence_implies_tyeq; split; eassumption.
Qed.

Lemma invert_typing_abs :
  forall Delta Gamma S1 t1 T,
  <[ Delta | Gamma |-- \:S1, t1 \in T ]> ->
  forall T1 T2,
  T === <{{ T1 -> T2 }}> ->
  (S1 === T1) /\ <[ Delta | S1 :: Gamma |-- t1 \in T2 ]>.
Proof.
  intros Delta Gamma S1 t1 T H. 
  remember <{ \:S1, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - apply invert_tyeq_fun in H1 as [Hl Hr].
    inversion Heqt. subst. split. 
    + assumption.
    + eapply T_Conv; eassumption.
  - apply IHhas_type.
    + assumption.
    + eapply tyeq_trans. split; eassumption.
Qed.


(* TmTAbs inversion *)
Lemma invert_typing_tyabs :   
  forall Delta Gamma J t1 T,
  <[ Delta | Gamma |-- \::J, t1 \in T ]> ->
  forall K T1,
  T === <{{ -/::K, T1 }}> ->
  K = J /\ <[ J :: Delta | map (ren_Ty S) Gamma |-- t1 \in T1 ]>.
Proof.
  intros Delta Gamma J t1 T H. 
  remember <{ \::J, t1 }> as t.
  generalize dependent Heqt.
  induction H; try discriminate; intros.
  - assert ( T1 === T0 ). { admit. }
    assert (K = K0). { admit. }
    + inversion Heqt. subst. split. 
      * reflexivity.
      * eapply T_Conv; eassumption.
  - apply IHhas_type.
    + assumption.
    + eapply tyeq_trans. split; eassumption.
Admitted.


Theorem preservation :
  forall Delta Gamma t T,
  <[ Delta | Gamma |-- t \in T ]> ->
  forall t',
  t --> t' ->
  <[ Delta | Gamma |-- t' \in T ]>.
Proof.
  intros Delta Gamma t T H. induction H; intros.
  - inversion H0.
  - inversion H1.
  - inversion H1.
    + asolve. unfold sigma_tm_one. subst t1.
      apply invert_typing_abs with (T1:=T1) (T2:=T2) in H as [HT1 Ht].
      * apply tmsubst_preserves_typing with (Gamma:=(T::Gamma)).
        { apply Ht. }
        { intros. destruct x; simpl.
          - rewrite renRen_Tm. asolve.
            simpl in H. inversion H. subst S. 
            eapply T_Conv.
            + eassumption.
            + apply tyeq_sym; assumption.
          - apply T_Var. assumption. }
      * apply multi_refl. 
    + apply T_App with T1.
      * apply IHhas_type1. assumption.
      * assumption.
    + apply T_App with T1.
      * assumption.
      * apply IHhas_type2. assumption.
  - inversion H1.
  - inversion H2.
    + subst. asolve. unfold sigma_ty_one.
      apply invert_typing_tyabs with (K:=K) (T1:=T1) in H as [HK Ht].
      * eapply tysubst_preserves_typing.
        { apply Ht. }
        { intros. rewrite nth_error_map in H.
          destruct (nth_error Gamma x) as [V|]; try discriminate.
          simpl in H. inversion H.
          f_equal. asolve. rewrite idSubst_Ty; try reflexivity. }
        { intros. destruct X; simpl. 
          - rewrite renRen_Ty. asolve. simpl in H. inversion H. subst.
            assumption. 
          - apply K_TVar. assumption. }
      * apply multi_refl.
    + eapply T_TApp; try eassumption.
      * apply IHhas_type. assumption.
  - eapply T_Conv.
    + apply IHhas_type. assumption.
    + assumption.
  - inversion H.
Qed. 