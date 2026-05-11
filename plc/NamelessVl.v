From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import FunctionalExtensionality.

From PLC Require Export Maps TyTmVl.

Declare Scope plc_scope.
Open Scope plc_scope.

Declare Custom Entry plc_ty.
Declare Custom Entry plc_tm.
Declare Custom Entry plc_tysubst.
Declare Custom Entry plc_tmsubst.

Notation "x" := x (in custom plc_ty at level 0, x constr at level 0) : plc_scope.
Notation "x" := x (in custom plc_tm at level 0, x constr at level 0) : plc_scope.

Notation "<{{ T }}>" := T (T custom plc_ty at level 99) : plc_scope.

Notation "( T )" := T (in custom plc_ty, T custom plc_ty at level 99) : plc_scope.
Notation "T1 -> T2" := (TyArrow T1 T2) (in custom plc_ty at level 50, right associativity) : plc_scope.
Notation "'-/,' T" := (TyForall T) (in custom plc_ty at level 90, T custom plc_ty at level 90) : plc_scope.
Notation "'Unit'" := TyUnit (in custom plc_ty at level 0) : plc_scope.

Notation "<{ t }>" := t (t custom plc_tm at level 200) : plc_scope.

Notation "( t )" := t (in custom plc_tm, t custom plc_tm at level 99) : plc_scope.
Notation "'unit'" := TmUnit (in custom plc_tm at level 0) : plc_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom plc_tm at level 11, left associativity) : plc_scope.
Notation "\: T ',' t" := (TmAbs T t) (in custom plc_tm at level 90, T custom plc_ty at level 99, t custom plc_tm at level 90) : plc_scope.
Notation "t [ T ]" := (TmTApp t T) (in custom plc_tm at level 11, t custom plc_tm, T custom plc_ty at level 0) : plc_scope.
Notation "'\\,' t" := (TmTAbs t) (in custom plc_tm at level 90, t custom plc_tm at level 90) : plc_scope.

Coercion var_ty : nat >-> ty.
Coercion var_vl : nat >-> vl.

Definition sigma_tm_empty : nat -> vl := fun n => var_vl n.
Definition sigma_tm_one (x: nat) (s: vl) : nat -> vl :=
  fun n => if n=?x then s else n.
Definition sigma_ty_empty : nat -> ty := fun n => var_ty n.
Definition sigma_ty_one (X: nat) (S: ty) : nat -> ty :=
  fun n => if n=?X then S else n.

Notation "'(' x '\->' s ')'" := (sigma_tm_one x s) (in custom plc_tmsubst).
Notation "'(' X '\->' S ')'" := (sigma_ty_one X S) (in custom plc_tysubst).

Notation "'[' X ':=' S ']' T" := (subst_ty (sigma_ty_one X S) T)
    (in custom plc_ty at level 5, T custom plc_ty at next level, right associativity).

Notation "'[[' x ':=' s ']]' t" := (subst_tm sigma_ty_empty (sigma_tm_one x s) t)
    (in custom plc_tm at level 10, t custom plc_tm at next level, right associativity).

Notation "'[' X ':=' S ']' t" := (subst_tm (sigma_ty_one X S) sigma_tm_empty t)
    (in custom plc_tm at level 5, t custom plc_tm at next level, right associativity).

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e "
  := (Some e) (at level 60).

Notation " 'fail' "
  := None.

Scheme tm_mut_ind := Induction for tm Sort Prop
with   vl_mut_ind := Induction for vl Sort Prop.

Combined Scheme tm_vl_mut_ind from tm_mut_ind, vl_mut_ind.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try reflexivity.

Definition beta_red t v := 
  ren_tm id Nat.pred (
    subst_tm sigma_ty_empty (sigma_tm_one 0 (ren_vl id S v)) t
  ).

Definition ty_beta_red t T :=
  ren_tm Nat.pred id (
    subst_tm (sigma_ty_one 0 (ren_ty S T)) sigma_tm_empty t
  ).

Fixpoint eval_tm (t: tm) : option tm :=
  match t with
  | <{ t1 t2 }> =>
      match t1, t2 with
      | TmVal <{ \:T, t11' }>, TmVal v2 => 
          return (beta_red t11' v2)
      | TmVal _, TmVal _ => fail
      | TmVal _, t2 =>
          t2' <- eval_tm t2 ;;
          return <{ t1 t2' }>
      | t1, t2 => 
          t1' <- eval_tm t1 ;;
          return <{ t1' t2 }>
      end
  | <{ t1 [T] }> =>
      match t1 with 
      | TmVal <{ \\, t11' }> =>
          return (ty_beta_red t11' T)
      | t1 =>
          t1' <- eval_tm t1 ;;
          return <{ t1' [T] }>
      end
  | TmVal _ => None
  end.

Fixpoint eval_tm_big (t: tm) : option tm :=
  match t with
  | <{ t1 t2 }> =>
      t1' <- eval_tm_big t1 ;;
      t2' <- eval_tm_big t2 ;;
      match t1', t2' with
        | TmVal <{ \:T, t11' }>, TmVal v2 => return <{ [[0:=v2]] t11' }>
        | _, _ => fail
      end
  | <{ t1 [T] }> =>
      t1' <- eval_tm_big t1 ;;
      match t1' with 
      | TmVal <{ \\, t11' }> => return <{ [0:=T] t11' }>
      | _ => fail
      end
  | TmVal _ => return t 
  end.

Definition context := list ty.

Scheme Equality for ty.
Notation "T1 '=^?' T2" := (ty_beq T1 T2) (at level 70, no associativity).

Definition typing_beta_red T U := 
  ren_ty Nat.pred (
    subst_ty (sigma_ty_one 0 (ren_ty S U)) T
  ).

Fixpoint typing (Gamma: context) (t: tm) : option ty :=
  match t with
  | <{ t1 t2 }> =>
      T1 <- typing Gamma t1 ;;
      T2 <- typing Gamma t2 ;;
      match T1 with
        | <{{ T11 -> T12 }}> =>
            if (T11=^?T2) then return T12 else fail
        | _ => fail
      end
  | <{ t1 [T] }> =>
      T1 <- typing Gamma t1 ;;
      match T1 with 
      | <{{ -/, T11 }}> =>
          return typing_beta_red T11 T
      | _ => fail
      end
  | TmVal v => typing_vl Gamma v
  end
with typing_vl (Gamma: context) (v: vl) : option ty := 
  match v with
  | var_vl X => List.nth_error Gamma X
  | <{ \:T, t1 }> =>
      T1 <- typing (T :: Gamma) t1 ;;
      return <{{T -> T1}}>
  | <{ \\, t1 }> => 
      T1 <- typing (map (ren_ty S) Gamma) t1 ;;
      return <{{-/, T1}}>
  | <{ unit }> => return <{{Unit}}>
  end.

Lemma normal_form_abs : forall v T1 T2,
  typing nil (TmVal v) = Some <{{T1 -> T2}}> ->
  exists T t, v = <{ \:T, t }>.
Proof.
  intros v T1 T2 H.
  destruct v; simpl in H; try discriminate.
  - rewrite nth_error_nil in H. discriminate.
  - eauto.
  - destruct (typing nil t); discriminate.
Qed.

Lemma normal_form_tyabs : forall v T,
  typing nil (TmVal v) = Some <{{-/, T}}> ->
  exists t, v = <{ \\, t }>.
Proof.
  intros v T H.
  destruct v; simpl in H; try discriminate.
  - rewrite nth_error_nil in H. discriminate.
  - destruct (typing (t :: nil) t0); discriminate.
  - eauto.
Qed.

Theorem Progress : forall t T,
  typing nil t = Some T ->
  (exists t', eval_tm t = Some t') \/ (exists v, t = TmVal v).
Proof.
  induction t; intros.
  - left. simpl in H.
    destruct (typing nil t1) as [T1|] eqn: Tyt1;
    destruct (typing nil t2) as [T2|] eqn: Tyt2;
    try discriminate.
    destruct T1 as [|T11 T12| | ] eqn:EqT1; try discriminate.
    destruct (T11 =^? T2) eqn: EqT2; try discriminate.
    inversion H.
    specialize (IHt1 <{{T11->T12}}>) as [ [t1' IHt1']|[v1' IHt1'] ];
    try reflexivity.
    + exists <{ t1' t2 }>.
      simpl. rewrite IHt1'. destruct t1; try reflexivity.
      simpl in IHt1'. discriminate.
    + specialize (IHt2 T2) as [ [t2' IHt2']|[v2' IHt2'] ];
      try reflexivity.
      * exists <{ t1 t2' }>.
        simpl. rewrite IHt2'. subst t1.
        destruct v1' eqn: Ev1'; destruct t2 eqn: Et2;
        try reflexivity; try discriminate IHt2'.
      * subst t1 t2. apply normal_form_abs in Tyt1 as [T' [t' Eqt'] ].
        subst v1'. eexists. reflexivity.
  - left. simpl in H.
    destruct (typing nil t) as [T1|] eqn: Tyt; try discriminate.
    destruct T1 as [| | T11 | ] eqn:EqT1; try discriminate.
    specialize (IHt <{{-/, T11}}>) as [ [t1' IHt1']|[v1' IHt1'] ];
    try reflexivity.
    + eexists. simpl. rewrite IHt1'. destruct t; try reflexivity.
      simpl in IHt1'. discriminate.
    + subst t. apply normal_form_tyabs in Tyt as [t' Ht'].
      subst. eexists. reflexivity.
  - right. eexists. reflexivity.
Qed.

Definition shift_tm t := ren_tm id S t.
Definition shift_ty T := ren_ty S T.

Lemma ty_beq_eq : forall T1 T2,
  T1 =^? T2 = true <-> T1 = T2.
Proof.
  intros T1 T2.
  split; intro H.
  - apply internal_ty_dec_bl. assumption.
  - subst. apply internal_ty_dec_lb. reflexivity.
Qed.

Lemma ty_beq_refl : 
forall T, T =^? T = true.
Proof.
  intros T. apply ty_beq_eq. reflexivity.
Qed.

Lemma invert_typing_app : forall Gamma t1 t2 T, 
  typing Gamma <{ t1 t2 }> = return T ->
  exists T1, (
    typing Gamma t1 = return <{{T1 -> T}}> /\
    typing Gamma t2 = return T1
  ).
Proof.
  intros Gamma t1 t2 T H.
  simpl in H.
  destruct (typing Gamma t1) as [T1|] eqn:E1; try discriminate.
  destruct (typing Gamma t2) as [T2|] eqn:E2; try discriminate.
  destruct T1 as [|T11 T12| |]; try discriminate.
  destruct (T11 =^? T2) eqn:E3; try discriminate.
  apply ty_beq_eq in E3. subst T2.
  inversion H; subst.
  eexists; eauto.
Qed.

Lemma invert_typing_tyapp : forall Gamma t1 S T, 
  typing Gamma <{ t1 [S] }> = return T ->
  exists T1, (
    typing Gamma t1 = return <{{ -/, T1 }}> /\
    T = typing_beta_red T1 S
  ).
Proof.
  intros Gamma t S T H.
  simpl in H.
  destruct (typing Gamma t) as [T1'|] eqn:Eq; try discriminate.
  destruct T1' as [| | T11 |]; try discriminate.
  inversion H; subst.
  eexists. split; reflexivity.
Qed.

Lemma invert_typing_abs : forall Gamma T1 t T,
  typing_vl Gamma <{ \:T1,t }> = return T ->
  exists T2, (
    typing (T1 :: Gamma) t = return T2 /\
    T = <{{ T1 -> T2 }}>
  ).
Proof.
  intros Gamma T1 t T H.
  simpl in H.
  destruct (typing (T1 :: Gamma) t) as [T2|] eqn:Eq; try discriminate.
  inversion H; subst.
  eexists; eauto.
Qed.

Lemma invert_typing_tyabs : forall Gamma t T,
  typing_vl Gamma <{ \\, t }> = return T ->
  exists T1, (
    typing (map (ren_ty S) Gamma) t = return T1 /\
    T = <{{ -/, T1 }}>
  ).
Proof.
  intros Gamma t T H.
  simpl in H.
  destruct (typing (map (ren_ty S) Gamma) t) as [T1|] eqn:Eq; try discriminate.
  inversion H; subst.
  eexists; eauto.
Qed.

Lemma weaking_var :
  (
    forall t Gamma T,
    typing Gamma t = Some T ->
    forall Delta xi,
    (forall x U, nth_error Gamma x = Some U -> 
                nth_error Delta (xi x) = Some U) ->
    typing Delta (ren_tm id xi t) = Some T
  ) /\ (
    forall v Gamma T,
    typing_vl Gamma v = Some T ->
    forall Delta xi,
    (forall x U, nth_error Gamma x = Some U -> 
                  nth_error Delta (xi x) = Some U) ->
    typing_vl Delta (ren_vl id xi v) = Some T
  ).
Proof.
  apply tm_vl_mut_ind; intros.
  - simpl. rename H into IHt1. rename H0 into IHt2.
    specialize (invert_typing_app _ _ _ _ H1) as [T1 [Ht1 Ht2] ].
    rewrite IHt1 with (T:=<{{ T1 -> T }}>) (Gamma:=Gamma);
    try assumption.
    rewrite IHt2 with (T:=T1) (Gamma:=Gamma); try assumption.
    rewrite ty_beq_refl. reflexivity.
  - simpl. rename H into IHt.
    specialize (invert_typing_tyapp _ _ _ _ H0) as [T1 [Ht1 HT] ].
    rewrite IHt with (T:=<{{ -/, T1 }}>) (Gamma:=Gamma); try assumption.
    replace (ren_ty id t0) with t0 by (symmetry; apply rinstId'_ty).
    f_equal. symmetry. assumption.
  - simpl. simpl in H0. apply H with (Gamma:=Gamma); assumption.
  - simpl in *. apply H0. assumption.
  - simpl in *.
    replace (ren_ty id t) with t by (symmetry; apply rinstId'_ty).
    destruct (typing (t :: Gamma) t0) eqn: Tyt; try discriminate.
    inversion H0.
    assert (Ht: 
      typing (t::Delta) (ren_tm (upRen_vl_ty id) (upRen_vl_vl xi) t0) = return t1
    ).
    { replace (upRen_vl_ty id) with (@id nat) by (unfold upRen_vl_ty; reflexivity).
      apply H with (Gamma:=(t::Gamma)); try assumption. 
      intros. destruct x; simpl in *.
      - assumption.
      - apply H1. assumption. }
    rewrite Ht. reflexivity.
  - simpl in *.
    replace (upRen_ty_ty id) with (@id nat) by
    ( unfold upRen_ty_ty; unfold unscoped.up_ren;
      apply functional_extensionality; destruct x; reflexivity).
    destruct (typing (map (ren_ty S) Gamma) t) eqn: Tyt; try discriminate.
    inversion H0.
    assert (Ht:
      typing (map (ren_ty S) Delta) (ren_tm id (upRen_ty_vl xi) t) = return t0
    ).
    { apply H with (map (ren_ty S) Gamma); try assumption.
      intros. unfold upRen_ty_vl.
      rewrite nth_error_map in *.
      destruct (nth_error Gamma x) eqn: NthG.
      - rewrite H1 with (U:=t1); assumption.
      - discriminate H2. }
    rewrite Ht. reflexivity.
  - simpl in *. assumption.
Qed.

Lemma sigma_ty_empty_stable : forall T,
  T = subst_ty sigma_ty_empty T.
Proof.
  intros T. unfold sigma_ty_empty. symmetry. apply idSubst_ty.
  reflexivity.
Qed.

Lemma weaking_tyvar :
  (
    forall t Gamma T,
    typing Gamma t = Some T ->
    forall Delta xi,
    (forall x U, nth_error Gamma x = Some U -> 
                 nth_error Delta x = Some (ren_ty xi U)) ->
    typing Delta (ren_tm xi id t) = Some (ren_ty xi T)
  ) /\ (
    forall v Gamma T,
    typing_vl Gamma v = Some T ->
    forall Delta xi,
    (forall x U, nth_error Gamma x = Some U -> 
                 nth_error Delta x = Some (ren_ty xi U)) ->
    typing_vl Delta (ren_vl xi id v) = Some (ren_ty xi T)
  ).
Proof.
  apply tm_vl_mut_ind; intros; simpl.
  - rename t into t1, t0 into t2, H into IH1, H0 into IH2.
    apply invert_typing_app in H1 as [T1 [Tyt1 Tyt2] ].
    rewrite IH1 with (Gamma:=Gamma) (T:=<{{T1->T}}>); try assumption.
    rewrite IH2 with (Gamma:=Gamma) (T:=T1); try assumption.
    cbn [ren_ty]. rewrite ty_beq_refl. reflexivity.
  - apply invert_typing_tyapp in H0 as [T1 [Tyt EqT] ].
    rewrite H with (Gamma:=Gamma) (T:=<{{ -/, T1}}>); try assumption.
    cbn [ren_ty]. subst T.
    asolve. f_equal. apply ext_ty. intros.
    asolve. destruct x; asolve.
  - apply H with (Gamma:=Gamma); assumption.
  - cbv [id]. apply H0. assumption.
  - simpl in H0.
    destruct (typing (t :: Gamma) t0) eqn: Tyt; try discriminate.
    inversion H0.
    replace (upRen_vl_vl id) with (@id nat);
    try (apply functional_extensionality; intro x; destruct x; reflexivity).
    rewrite H with (Gamma:=(t::Gamma)) (T:=t1); try assumption.
    + asimpl. reflexivity.
    + asimpl. intros. destruct x; simpl; simpl in H2.
      * inversion H2. reflexivity.
      * apply H1. assumption.
  - simpl in H0.
    destruct (typing (map (ren_ty S) Gamma) t) as [T1|] eqn: Tyt; try discriminate.
    rewrite H with (Gamma:=map (ren_ty S) Gamma) (T:=T1); try assumption.
    + inversion H0. reflexivity.
    + asimpl. unfold unscoped.scons, core.funcomp.
      intros. rewrite nth_error_map in *. 
      destruct (nth_error Gamma x) as [V|] eqn: HG; try discriminate.
      simpl in H2. inversion H2. apply H1 in HG.
      rewrite HG. asolve. 
  - simpl in H. inversion H. reflexivity.
Qed.

Lemma context_shift : forall Gamma x sigma T,
  typing_vl Gamma (sigma x) = return T ->
  typing_vl (map (ren_ty S) Gamma) (up_ty_vl sigma x) = return ren_ty S T.
Proof.
  intros. unfold up_ty_vl, core.funcomp, unscoped.shift, unscoped.id.
  apply weaking_tyvar with (Gamma:=Gamma).
  - apply H.
  - intros x' U Hnth.
    rewrite nth_error_map.
    rewrite Hnth. reflexivity.
Qed.

Theorem var_subst_preserves_typing :
  (
    forall t Gamma T,
    typing Gamma t = Some T ->
    forall Delta sigma,
    (forall x U, nth_error Gamma x = Some U -> typing_vl Delta (sigma x) = Some U) ->
    typing Delta (subst_tm id sigma t) = Some T
  ) /\ (
    forall v Gamma T,
    typing_vl Gamma v = Some T ->
    forall Delta sigma,
    (forall x U, nth_error Gamma x = Some U -> typing_vl Delta (sigma x) = Some U) ->
    typing_vl Delta (subst_vl id sigma v) = Some T
  ).
Proof.
  apply tm_vl_mut_ind; intros.
  - (* TmApp *)
    simpl in *.
    destruct (typing Gamma t) as [T1|] eqn:E1; try discriminate.
    destruct (typing Gamma t0) as [T2|] eqn:E2; try discriminate.
    destruct T1 as [|T11 T12| |]; try discriminate.
    destruct (T11 =^? T2) eqn:E3; try discriminate.
    inversion H1; subst.
    simpl.
    rewrite H with (Delta:=Delta) (sigma:=sigma) (Gamma:=Gamma) (T:=<{{T11->T}}>); auto.
    rewrite H0 with (Delta:=Delta) (sigma:=sigma) (Gamma:=Gamma) (T:=T2); auto.
    rewrite E3. reflexivity.
  - (* TmTApp *)
    simpl in *.
    destruct (typing Gamma t) as [T1|] eqn:E1; try discriminate.
    destruct T1 as [| | T11 |]; try discriminate.
    inversion H0; subst.
    simpl.
    rewrite H with (Delta:=Delta) (sigma:=sigma) (Gamma:=Gamma) (T:=<{{-/,T11}}>); auto.
    replace (subst_ty (fun x0 : nat => id x0) t0) with t0; try reflexivity.
    rewrite instId'_ty. reflexivity.
  - (* TmVal *)
    simpl in *.
    apply H with Gamma; auto.
  - (* var_vl *)
    simpl in *.
    apply H0. assumption.
  - (* TmAbs *)
    simpl in *.
    destruct (typing (t :: Gamma) t0) as [T1|] eqn:E1; try discriminate.
    inversion H0; subst.
    rewrite H with (Gamma:=(t::Gamma)) (T:=T1).
    + rewrite instId'_ty. reflexivity.
    + assumption.
    + intros. rewrite instId'_ty.
      destruct x as [|x']; simpl; simpl in H2.
      * assumption.
      * unfold core.funcomp, unscoped.shift, unscoped.id.
        apply weaking_var with (Gamma:=Delta); auto.
  - (* TmTAbs *)
    simpl in *.
    destruct (typing (map (ren_ty S) Gamma) t) as [T1|] eqn:E1; try discriminate.
    inversion H0; subst.
    assert (subst_tm (up_ty_ty (fun x0 : nat => id x0)) (up_ty_vl sigma) t
    = subst_tm (fun x : nat =>  x) (up_ty_vl sigma) t).
    { apply ext_tm; try reflexivity.
      intros. destruct x; reflexivity. }
    rewrite H2. rewrite (H _ _ E1); try reflexivity.
    intros. rewrite nth_error_map in H3.
    destruct (nth_error Gamma x) as [U' |] eqn: EqU'; try discriminate.
    simpl in H3. inversion H3. subst U. apply H1 in EqU'.
    apply context_shift. assumption.
  - (* TmUnit *)
    simpl in *.
    inversion H; subst; reflexivity.
Qed.

Lemma tyvar_subst_preserves_typing :
  (
    forall t Gamma T,
    typing Gamma t = Some T ->
    forall Delta sigma,
    (forall x U, nth_error Gamma x = Some U ->
    nth_error Delta x = Some (subst_ty sigma U)) ->
    typing Delta (subst_tm sigma id t) = Some (subst_ty sigma T)
  ) /\ (
    forall v Gamma T,
    typing_vl Gamma v = Some T ->
    forall Delta sigma,
    (forall x U, nth_error Gamma x = Some U ->
    nth_error Delta x = Some (subst_ty sigma U)) ->
    typing Delta (subst_tm sigma id (TmVal v)) = Some (subst_ty sigma T)
  ).
Proof.
  apply tm_vl_mut_ind; intros.
  - rename t into t1, t0 into t2, H into IH1, H0 into IH2.
    simpl. apply invert_typing_app in H1 as [T11 [Ty1 Ty2] ].
    rewrite IH1 with (Gamma:=Gamma) (T:=<{{T11->T}}>); try assumption.
    rewrite IH2 with (Gamma:=Gamma) (T:=T11); try assumption.
    simpl. rewrite ty_beq_refl. reflexivity.
  - rename t0 into U.
    simpl. apply invert_typing_tyapp in H0 as [T1 [Ht HT] ].
    rewrite H with (Gamma:=Gamma) (T:=<{{-/,T1}}>); try assumption.
    subst T. asimpl. aunfold.
    f_equal. apply ext_ty. intros y.
    destruct y; asimpl; aunfold; simpl.
    + apply ext_ty. intros. rewrite renRen_ty.
      unfold core.funcomp. simpl. rewrite rinstId'_ty. reflexivity.
    + apply instId'_ty.
  - apply H with (Gamma:=Gamma); try assumption.
  - simpl. apply H0. apply H.
  - simpl. rename t into T1.
    replace (up_vl_vl (fun x0 : nat => id x0)) with (fun x : nat => (var_vl x));
    try (apply functional_extensionality; destruct x; auto).
    apply invert_typing_abs in H0 as [T2 [Ht HT] ].
    rewrite H with (Gamma:=(T1::Gamma)) (T:=T2); try assumption.
    + subst T. asimpl; aunfold.
      replace (fun x0 : nat => ren_ty id (sigma x0)) with sigma.
      * reflexivity.
      * apply functional_extensionality. intros.
        rewrite rinstId'_ty. reflexivity.
    + intros. destruct x; simpl; simpl in H0.
      * inversion H0. asimpl. aunfold.
        asimpl. reflexivity.
      * rewrite H1 with (U:=U); try assumption.
        f_equal. apply ext_ty. intros.
        destruct x0; asimpl; reflexivity. 
  - simpl. apply invert_typing_tyabs in H0 as [T1 [Ht HT] ].
    subst T. erewrite H; try apply Ht.
    + reflexivity.
    + intros. rewrite nth_error_map in *.
      destruct (nth_error Gamma x) as [V|] eqn: HG; try discriminate.
      rewrite H1 with (U:=V); try assumption.
      simpl. f_equal. simpl in H0. inversion H0.
      asimpl. aunfold. reflexivity.
  - simpl in *. inversion H. reflexivity.
Qed.  

Theorem Preservation : forall Gamma t t' T,
  typing Gamma t = Some T ->
  eval_tm t = Some t' ->
  typing Gamma t' = Some T.
Proof.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma t' T Hty Heval.
  - apply invert_typing_app in Hty as [T1 [Hty1 Hty2] ].
    simpl in Heval. destruct t1 eqn: Eqt1;
    try (
      rewrite <- Eqt1 in *;
      destruct (eval_tm t1) as [t1' |] eqn: evt1';
      inversion Heval;
      simpl; rewrite IHt1 with (T:=<{{T1->T}}>); auto;
      rewrite Hty2; rewrite ty_beq_refl; reflexivity
    ).
    + destruct (eval_tm t2) as [t2' |] eqn: evt2'.
      * destruct t2 eqn: Eqt2; 
        try (
          rewrite <- Eqt2 in *;
          destruct v eqn: Eqv; rewrite <- Eqv in *; inversion Heval;
          simpl; simpl in Hty1; rewrite Hty1;
          apply IHt2 with (t':=t2') in Hty2; try reflexivity;
          rewrite Hty2; rewrite ty_beq_refl; reflexivity
        ).
        discriminate.
      * destruct v; destruct t2; try discriminate.
        inversion Heval. simpl in Hty2.
        simpl in Hty1. destruct (typing (t :: Gamma) t0) eqn: Tyt0;
        try discriminate. inversion Hty1. subst t t2.
        specialize var_subst_preserves_typing as [X _].
        unfold beta_red. asimpl.
        unfold core.funcomp. 
        apply X with (Gamma:=(T1::Gamma)); try assumption.
        intros. destruct x; asimpl; try assumption.
        simpl in H. inversion H. subst T1. assumption.
  - rename t into t1.
    apply invert_typing_tyapp in Hty as [T1 [Hty HT] ].
    simpl in Heval.
    destruct (eval_tm t1) as [t1' |] eqn: evt1'.
    + destruct t1 eqn: Eqt1;
      try (
        rewrite <- Eqt1 in *; inversion Heval;
        simpl; rewrite IHt with (T:=<{{-/, T1}}>); auto;
        subst T; reflexivity
      ).
      simpl in evt1'. discriminate.
    + destruct t1 eqn: Eqt1; try destruct v; try discriminate.
      simpl in Hty.
      destruct (typing (map (ren_ty S) Gamma) t) as [T1'| ] eqn: Ht ; try discriminate.
      inversion Hty. subst T1'. inversion Heval.
      unfold ty_beta_red. rename t0 into T0.
      rewrite HT.
      asimpl. unfold core.funcomp.
      specialize tyvar_subst_preserves_typing as [X _].
      apply X with (Gamma:=(map (ren_ty S) Gamma)) ; try assumption.
      intros. rewrite nth_error_map in H.
      destruct (nth_error Gamma x) as [V|]; try discriminate.
      simpl in H. inversion H. asimpl. unfold core.funcomp, sigma_ty_one.
      simpl. f_equal. symmetry. apply instId'_ty.
  - simpl in Heval. discriminate.
Qed.
