From Stdlib Require Import Nat List FunctionalExtensionality.
From Fomega Require Export Definitions.

Ltac dauto := try (intros _x; destruct _x; auto).

(* Properties *)
Lemma renTm_typing : forall Delta Gamma t T,
  <{ Delta | Gamma |-- t \in T }> ->
  forall Gamma' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' (xi x) = Some S) ->
  <{ Delta | Gamma' |-- {ren_Tm id xi t} \in T }>.
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
  <{{ Delta |-- T \in K }}> ->
  forall Delta' xi,
  (forall X J, nth_error Delta X = Some J -> 
              nth_error Delta' (xi X) = Some J) ->
  <{{ Delta' |-- {ren_Ty xi T} \in K }}>.
Proof.
  intros Delta T K H.
  induction H; intros; asolve;
  try (econstructor; auto).
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
  - apply IHhas_kind.
    intros. destruct X; simpl; auto.
Qed.

Lemma renTy_tyequiv : forall T1 T2,
  <{{= T1 = T2 =}}> -> 
  forall xi,
  <{{= {ren_Ty xi T1} = {ren_Ty xi T2} =}}>.
Proof.
  intros T1 T2 H. induction H; intros; asolve.
  - apply TQ_Refl.
  - apply TQ_Sym. auto.
  - eapply TQ_Trans; auto.
  - eapply TQ_Abs. auto.
  - apply TQ_App; auto.
  - apply TQ_Arr; auto.
  - apply TQ_All; auto.
  - apply TQ_Unit.
Qed. 

Lemma renTy_typing : forall Delta Gamma t T,
  <{ Delta | Gamma |-- t \in T }> ->
  forall Gamma' Delta' xi,
  (forall x S, nth_error Gamma x = Some S -> 
              nth_error Gamma' x = Some (ren_Ty xi S)) ->
  (forall X K, nth_error Delta X = Some K -> 
              nth_error Delta' (xi X) = Some K) ->
  <{ Delta' | Gamma' |-- {ren_Tm xi id t} \in {ren_Ty xi T} }>.
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
    + apply renTy_tyequiv. assumption.
  - apply T_Unit.
Qed.

Lemma tmsubst_preserves_typing :
  forall Delta Gamma t T,
  <{ Delta | Gamma |-- t \in T }> ->
  forall Gamma' sigma,
  (forall x S, nth_error Gamma x = Some S -> <{ Delta | Gamma' |-- {sigma x} \in S }>) ->
  <{ Delta | Gamma' |-- {subst_Tm id sigma t} \in T }>.
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
