From Stdlib Require Import Nat.
From Stdlib Require Import List.
From Stdlib Require Import FunctionalExtensionality.

From PLC Require Export Maps TyAndTm.

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
Coercion var_tm : nat >-> tm.

Definition sigma_tm_empty : nat -> tm := fun n => var_tm n.
Definition sigma_tm_one (x: nat) (s: tm) : nat -> tm :=
  fun n => if n=?x then s else var_tm n.
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

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try auto.

Definition beta_red t v := 
  ren_tm id Nat.pred (
    subst_tm sigma_ty_empty (sigma_tm_one 0 (ren_tm id S v)) t
  ).

Definition ty_beta_red t T :=
  ren_tm Nat.pred id (
    subst_tm (sigma_ty_one 0 (ren_ty S T)) sigma_tm_empty t
  ).

Fixpoint eval_tm (t: tm) : option tm :=
  match t with
  | <{ t1 t2 }> =>
      match t1, t2 with
      | <{ \:T, t11' }>, <{ \:_, _ }>
      | <{ \:T, t11' }>, <{ \\, _ }>
      | <{ \:T, t11' }>, <{ unit }>
          => return (beta_red t11' t2)
      | <{ \\, _ }>, <{ \:_, _ }>
      | <{ \\, _ }>, <{ \\, _ }>
      | <{ \\, _ }>, <{ unit }>
      | <{ unit }>, <{ \:_, _ }>
      | <{ unit }>, <{ \\, _ }>
      | <{ unit }>, <{ unit }>
           => fail
      |  <{ \:_, _ }>, t2
      |  <{ \\, _ }>,  t2
      |  <{ unit }>,  t2 =>
          t2' <- eval_tm t2 ;;
          return <{ t1 t2' }>
      | t1, t2 => 
          t1' <- eval_tm t1 ;;
          return <{ t1' t2 }>
      end
  | <{ t1 [T] }> =>
      match t1 with 
      | <{ \\, t11' }> =>
          return (ty_beta_red t11' T)
      | _ =>
          t1' <- eval_tm t1 ;;
          return <{ t1' [T] }>
      end
  | _ => None
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
  | var_tm X => List.nth_error Gamma X
  | <{ \:T, t1 }> =>
      T1 <- typing (T :: Gamma) t1 ;;
      return <{{T -> T1}}>
  | <{ \\, t1 }> => 
      T1 <- typing (map (ren_ty S) Gamma) t1 ;;
      return <{{-/, T1}}>
  | <{ unit }> => return <{{Unit}}>
  end.

Definition IsValue (t: tm) :=
  (exists T t1, t = <{ \:T, t1 }>) \/ (exists t1, t = <{ \\, t1 }>) \/ (t = <{ unit }>).

Lemma normal_form_abs : forall v T1 T2,
  IsValue v ->
  typing nil v = Some <{{T1 -> T2}}> ->
  exists T t, v = <{ \:T, t }>.
Proof.
  intros v T1 T2 H.
  destruct H; auto. destruct H.
  - intros. destruct H as [t1 H]. subst v.
    simpl in H0. destruct (typing nil t1); discriminate.
  - intros. subst v. discriminate H0.
Qed.

Lemma normal_form_tyabs : forall v T,
  IsValue v ->
  typing nil v = Some <{{-/, T}}> ->
  exists t, v = <{ \\, t }>.
Proof.
  intros v T H.
  destruct H.
  - intros. destruct H as [T' [t' H] ]. subst v.
    simpl in H0. destruct (typing (T' :: nil) t') as [T2|] eqn:E; discriminate.
  - destruct H; auto.
    intros. subst v. discriminate.
Qed.

Theorem Progress : forall t T,
  typing nil t = Some T ->
  (exists t', eval_tm t = Some t') \/ IsValue t.
Proof.
  induction t; intros.
  - simpl in H. rewrite nth_error_nil in H. discriminate.
  - left. simpl in H.
    destruct (typing nil t1) as [T1|] eqn: Tyt1;
    destruct (typing nil t2) as [T2|] eqn: Tyt2;
    try discriminate.
    destruct T1 as [|T11 T12| | ] eqn:EqT1; try discriminate.
    destruct (T11 =^? T2) eqn: EqT2; try discriminate.
    inversion H.
    specialize (IHt1 <{{T11->T12}}>) as [ [t1' IHt1']|IHt1' ]; 
    try reflexivity.
    + exists <{ t1' t2 }>.
      simpl. rewrite IHt1'. destruct t1; try discriminate; reflexivity.
    + specialize (IHt2 T2) as [ [t2' IHt2']|IHt2' ];
      try reflexivity.
      * exists <{ t1 t2' }>.
        simpl. rewrite IHt2'.
        destruct IHt1' as [ [U [t11 IHt1'] ] | [ [t11 IHt1'] | ] ];
        subst t1; destruct t2 eqn: Et2;
        try reflexivity; try discriminate.
      * apply normal_form_abs in Tyt1 as [T' [t' Eqt'] ]; try assumption.
        subst t1. destruct IHt2' as [ [U [t21 IHt2'] ] | [ [t21 IHt2'] |] ];
        eexists; subst t2; reflexivity.
  - left. simpl in H.
    destruct (typing nil t) as [T1|] eqn: Tyt; try discriminate.
    destruct T1 as [| | T11 | ] eqn:EqT1; try discriminate.
    specialize (IHt <{{-/, T11}}>) as [ [t1' IHt1']|[ [U [t11 IHt1'] ] | [ [ t11 IHt1' ]|] ] ];
    try reflexivity.
    + eexists. simpl. rewrite IHt1'. destruct t; try reflexivity.
      simpl in IHt1'. discriminate.
    + subst t. simpl in Tyt. destruct (typing (U :: nil) t11); discriminate.
    + apply normal_form_tyabs in Tyt as [t' Ht'].
      * eexists. subst t. reflexivity.
      * right. left. eexists. apply IHt1'.
    + subst t. simpl in Tyt. discriminate.
  - right. left. eexists. eexists. reflexivity.
  - right. right. left. eexists. reflexivity. 
  - right. right. right. reflexivity.
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
  typing Gamma <{ \:T1,t }> = return T ->
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
  typing Gamma <{ \\, t }> = return T ->
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

Lemma weaking_var : forall t Gamma T,
  typing Gamma t = Some T ->
  forall Delta xi,
  (forall x U, nth_error Gamma x = Some U -> 
              nth_error Delta (xi x) = Some U) ->
  typing Delta (ren_tm id xi t) = Some T.
Proof.
  induction t; intros; simpl.
  - replace (ren_tm id xi n) with (var_tm (xi n)); try reflexivity.
    apply H0. assumption.
  - apply invert_typing_app in H as [T1 [Ht1 Ht2] ].
    rewrite IHt1 with (T:=<{{ T1 -> T }}>) (Gamma:=Gamma);
    try assumption.
    rewrite IHt2 with (T:=T1) (Gamma:=Gamma); try assumption.
    rewrite ty_beq_refl. reflexivity.
  - apply invert_typing_tyapp in H as [T1 [Ht1 HT] ].
    rewrite IHt with (T:=<{{ -/, T1 }}>) (Gamma:=Gamma); try assumption.
    replace (ren_ty id t0) with t0 by (symmetry; apply rinstId'_ty).
    f_equal. symmetry. assumption.
  - rename t into T1. apply invert_typing_abs in H as [U [Ht HT] ].
    inversion HT. rewrite rinstId'_ty.
    rewrite IHt with (T:=U) (Gamma:=(T1::Gamma)); auto.
    intros. destruct x as [|x']; simpl; simpl in H1; try assumption.
    apply H0. assumption.
  - apply invert_typing_tyabs in H as [T1 [Ht HT] ]. subst T.
    replace (upRen_ty_ty id) with (@id nat);
    try (apply functional_extensionality; destruct x; reflexivity).
    erewrite IHt; try eassumption; try reflexivity.
    intros x U. repeat rewrite nth_error_map. intros.
    destruct (nth_error Gamma x) as [UG|] eqn: HG; try discriminate.
    apply H0 in HG. asolve. rewrite HG. simpl.
    simpl in H. assumption.
  - simpl in H. assumption.
Qed.

Lemma sigma_ty_empty_stable : forall T,
  T = subst_ty sigma_ty_empty T.
Proof.
  intros T. unfold sigma_ty_empty. symmetry. apply idSubst_ty.
  reflexivity.
Qed.

Lemma weaking_tyvar :
  forall t Gamma T,
  typing Gamma t = Some T ->
  forall Delta xi,
  (forall x U, nth_error Gamma x = Some U -> 
                nth_error Delta x = Some (ren_ty xi U)) ->
  typing Delta (ren_tm xi id t) = Some (ren_ty xi T).
Proof.
  induction t; intros; simpl.
  - apply H0. assumption. 
  - apply invert_typing_app in H as [T1 [Tyt1 Tyt2] ].
    rewrite IHt1 with (Gamma:=Gamma) (T:=<{{T1->T}}>); try assumption.
    rewrite IHt2 with (Gamma:=Gamma) (T:=T1); try assumption.
    cbn [ren_ty]. rewrite ty_beq_refl. reflexivity.
  - apply invert_typing_tyapp in H as [T1 [Tyt EqT] ].
    rewrite IHt with (Gamma:=Gamma) (T:=<{{ -/, T1}}>); try assumption.
    cbn [ren_ty]. subst T.
    asolve. f_equal. apply ext_ty. intros.
    asolve. destruct x; asolve.
  - rename t into T1. apply invert_typing_abs in H as [T2 [Ht HT] ].
    subst T. replace (upRen_tm_tm id) with (@id nat);
    try (apply functional_extensionality; destruct x; reflexivity).
    erewrite IHt with (Gamma:=(T1::Gamma)) (T:=T2); try eassumption; try asolve.
    destruct x; simpl; intros.
    + inversion H. reflexivity.
    + apply H0. assumption.
  - apply invert_typing_tyabs in H as [T1 [Ht HT] ]. subst T.
    replace (upRen_ty_tm id) with (@id nat);
    try (apply functional_extensionality; destruct x; reflexivity).
    erewrite IHt; try eassumption; try asolve.
    intros. rewrite nth_error_map in *.
    destruct (nth_error Gamma x) as [UG|] eqn: HG; try discriminate.
    apply H0 in HG. rewrite HG. simpl in H. inversion H. subst U.
    asolve.
  - simpl in H. inversion H. reflexivity.
Qed.

Theorem var_subst_preserves_typing :
  forall t Gamma T,
  typing Gamma t = Some T ->
  forall Delta sigma,
  (forall x U, nth_error Gamma x = Some U -> typing Delta (sigma x) = Some U) ->
  typing Delta (subst_tm id sigma t) = Some T.
Proof.
  induction t; intros; simpl.
  - apply H0. assumption.
  - apply invert_typing_app in H as [T1 [Tyt1 Tyt2] ].
    rewrite IHt1 with (Gamma:=Gamma) (T:=<{{T1->T}}>); try assumption.
    rewrite IHt2 with (Gamma:=Gamma) (T:=T1); try assumption.
    rewrite ty_beq_refl. reflexivity.
  - apply invert_typing_tyapp in H as [T1 [Tyt HT] ].
    rewrite IHt with (Gamma:=Gamma) (T:=<{{-/,T1}}>); try assumption.
    subst T. asolve. f_equal. apply ext_ty. intros.
    renamify. reflexivity.
  - rename t into T1.
    apply invert_typing_abs in H as [T2 [Tyt HT] ]. subst T.
    rewrite IHt with (Gamma:=(T1::Gamma)) (T:=T2); try assumption.
    + rewrite instId'_ty. reflexivity.
    + intros. destruct x; simpl in H; asolve.
      apply weaking_var with (Gamma:=Delta).
      * apply H0. assumption.
      * intros. simpl. assumption.
  - apply invert_typing_tyabs in H as [T1 [Tyt HT] ]. subst T.
    replace (up_ty_ty (fun x : nat => id x)) with (fun x : nat => var_ty x);
    try (apply functional_extensionality; destruct x; auto).
    erewrite IHt with (Gamma:=(map (ren_ty S) Gamma)) (T:=T1); auto.
    intros. asolve. rewrite nth_error_map in H.
    destruct (nth_error Gamma x) as [V|] eqn: HG; try discriminate.
    simpl in H. inversion H. eapply weaking_tyvar.
    + apply H0; assumption.
    + intros. rewrite nth_error_map. rewrite H1.
      reflexivity.
  - simpl in H. assumption.
Qed.

Lemma tyvar_subst_preserves_typing :
  forall t Gamma T,
  typing Gamma t = Some T ->
  forall Delta sigma,
  (forall x U, nth_error Gamma x = Some U ->
  nth_error Delta x = Some (subst_ty sigma U)) ->
  typing Delta (subst_tm sigma id t) = Some (subst_ty sigma T).
Proof.
  induction t; intros; simpl.
  - apply H0; assumption.
  - apply invert_typing_app in H as [T11 [Ty1 Ty2] ].
    rewrite IHt1 with (Gamma:=Gamma) (T:=<{{T11->T}}>); try assumption.
    rewrite IHt2 with (Gamma:=Gamma) (T:=T11); try assumption.
    simpl. rewrite ty_beq_refl. reflexivity.
  - rename t0 into T1.
    apply invert_typing_tyapp in H as [T2 [Ht HT] ]. subst T.
    rewrite IHt with (Gamma:=Gamma) (T:=<{{-/,T2}}>); try assumption.
    asolve. f_equal. apply ext_ty. destruct x; asolve.
    + apply ext_ty. intros. asolve.
    + apply instId'_ty.
  - rename t into T1.
    apply invert_typing_abs in H as [T2 [Tyt HT] ]. subst T.
    replace (up_tm_tm (fun x : nat => id x)) with (fun x : nat => var_tm x);
    try (apply functional_extensionality; destruct x; reflexivity).
    rewrite IHt with (Gamma:=(T1::Gamma)) (T:=T2); try assumption.
    + asolve. replace (fun x : nat => ren_ty id (sigma x)) with sigma;
      try (apply functional_extensionality); asolve.
    + intros. replace (up_tm_ty sigma) with sigma;
      try (apply functional_extensionality; asolve).
      destruct x; simpl in H; simpl.
      * inversion H. reflexivity.
      * apply H0. assumption.
  - apply invert_typing_tyabs in H as [T1 [Tyt HT] ]. subst T.
    replace (up_ty_tm (fun x : nat => id x)) with (fun x : nat => var_tm x);
    try (apply functional_extensionality; destruct x; auto).
    erewrite IHt with (Gamma:=(map (ren_ty S) Gamma)) (T:=T1); auto.
    intros. rewrite nth_error_map in *.
    (* asolve. rewrite nth_error_map in H. *)
    destruct (nth_error Gamma x) as [V|] eqn: HG; try discriminate.
    simpl in H. inversion H. apply H0 in HG. rewrite HG.
    simpl. f_equal. asolve. 
  - simpl in *. inversion H. reflexivity.
Qed.  

Theorem Preservation : forall Gamma t t' T,
  typing Gamma t = Some T ->
  eval_tm t = Some t' ->
  typing Gamma t' = Some T.
Proof.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma t' T Hty Heval; try discriminate. 
  - apply invert_typing_app in Hty as [T1 [Hty1 Hty2] ].
    simpl in Heval. destruct (eval_tm t1) as [t1' |] eqn: evt1.
    + destruct t1 eqn: Eqt1; try discriminate;
      subst t1; inversion Heval; simpl;
      rewrite IHt1 with (T:=<{{T1->T}}>); auto;
      rewrite Hty2; rewrite ty_beq_refl; reflexivity.
    + destruct t1 eqn: Eqt1; try discriminate; [rename t into T1'|].
      * apply invert_typing_abs in Hty1 as [T2 [Tyt HT] ]. inversion HT.
        subst T1' T.
        destruct (eval_tm t2) as [t2'|] eqn: evt2.
        { destruct t2 eqn: Eqt2; try discriminate; rewrite <- Eqt2 in *;
          inversion Heval; simpl; rewrite Tyt;
          rewrite IHt2 with (T:=T1); auto; rewrite ty_beq_refl;
          reflexivity. }
        { destruct t2 eqn: Eqt2; try discriminate; rewrite <- Eqt2 in *;
          inversion Heval; unfold beta_red; asolve;
          apply var_subst_preserves_typing with (Gamma:=(T1::Gamma)); auto;
          intros; destruct x; simpl in H; asolve; inversion H;
          subst T1; assumption. }
      * apply invert_typing_tyabs in Hty1 as [X [_  contra] ].
        discriminate.
  - rename t0 into U, t into t1. 
    apply invert_typing_tyapp in Hty as [T1 [Tyt1 HT] ]. subst T.
    simpl in Heval. destruct (eval_tm t1) as [t1'|] eqn: evt1.
    + destruct t1 eqn: Eqt1; try discriminate; rewrite <- Eqt1 in *;
      inversion Heval; simpl;
      rewrite IHt with (T:=<{{-/,T1 }}>); auto.
    + destruct t1 eqn: Eqt1; try discriminate.
      apply invert_typing_tyabs in Tyt1 as [T1' [Ht HT] ].
      inversion HT. subst T1'.
      inversion Heval. unfold ty_beta_red. asolve.
      eapply tyvar_subst_preserves_typing; try eassumption.
      intros. rewrite nth_error_map in H.
      destruct (nth_error Gamma x) as [V|] eqn: HG; try discriminate.
      simpl in H. inversion H. f_equal. asolve. symmetry. apply instId'_ty.
Qed.
