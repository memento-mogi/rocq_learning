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

(* 変数に関するフォールバック *)
Notation "x" := x (in custom plc_ty at level 0, x constr at level 0) : plc_scope.
Notation "x" := x (in custom plc_tm at level 0, x constr at level 0) : plc_scope.

(* 型と項をくくるための括弧表記 *)
Notation "<{{ T }}>" := T (T custom plc_ty at level 99) : plc_scope.

(* ----- 型 (ty) の Notation ----- *)
Notation "( T )" := T (in custom plc_ty, T custom plc_ty at level 99) : plc_scope.
Notation "T1 -> T2" := (TyArrow T1 T2) (in custom plc_ty at level 50, right associativity) : plc_scope.
Notation "'-/,' T" := (TyForall T) (in custom plc_ty at level 90, T custom plc_ty at level 90) : plc_scope.
Notation "'Unit'" := TyUnit (in custom plc_ty at level 0) : plc_scope.

Notation "<{ t }>" := t (t custom plc_tm at level 200) : plc_scope.

(* ----- 項 (term) の Notation ----- *)
Notation "( t )" := t (in custom plc_tm, t custom plc_tm at level 99) : plc_scope.
Notation "'unit'" := TmUnit (in custom plc_tm at level 0) : plc_scope.

(* 関数適用 (左結合) *)
Notation "t1 t2" := (TmApp t1 t2) (in custom plc_tm at level 11, left associativity) : plc_scope.
(* 関数抽象: \:T, t *)
Notation "\: T ',' t" := (TmAbs T t) (in custom plc_tm at level 90, T custom plc_ty at level 99, t custom plc_tm at level 90) : plc_scope.

(* 型適用: t [T] *)
Notation "t [ T ]" := (TmTApp t T) (in custom plc_tm at level 11, t custom plc_tm, T custom plc_ty at level 0) : plc_scope.
Notation "'\\,' t" := (TmTAbs t) (in custom plc_tm at level 90, t custom plc_tm at level 90) : plc_scope.

Coercion var_ty : nat >-> ty.
Coercion var_vl : nat >-> vl.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold X : core.
Hint Unfold Y : core.
Hint Unfold Z : core.

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
  - destruct v; simpl; simpl in H; simpl in H0.
    + apply H1. assumption.
    + replace (ren_ty id t) with t by (symmetry; apply rinstId'_ty).
      simpl. replace (ren_ty id t) with t in H by (symmetry; apply rinstId'_ty) .
      apply H with (Gamma:=Gamma); assumption.
    + apply H with (Gamma:=Gamma); assumption.
    + assumption.
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
      intros. destruct x0; simpl in *.
      - assumption.
      - apply H1. assumption. }
    rewrite Ht. reflexivity.
  - simpl in *.
    replace (upRen_ty_ty id) with (@id nat) by
    ( unfold upRen_ty_ty; unfold unscoped.up_ren;
      apply functional_extensionality; destruct x0; reflexivity).
    destruct (typing (map (ren_ty S) Gamma) t) eqn: Tyt; try discriminate.
    inversion H0.
    assert (Ht:
      typing (map (ren_ty S) Delta) (ren_tm id (upRen_ty_vl xi) t) = return t0
    ).
    { apply H with (map (ren_ty S) Gamma); try assumption.
      intros. unfold upRen_ty_vl.
      rewrite nth_error_map in *.
      destruct (nth_error Gamma x0) eqn: NthG.
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

Lemma typingbeta_ren_commutable : forall T U xi,
  typing_beta_red (ren_ty (upRen_ty_ty xi) T) (ren_ty xi U) =
  ren_ty xi (typing_beta_red T U).
Proof.
  induction T; intros;
  unfold typing_beta_red, sigma_ty_one in *.
  - simpl in *. destruct n as [|n'] eqn: Eqn'.
    + simpl. repeat rewrite (renRen_ty S pred).
      unfold core.funcomp. simpl. repeat rewrite rinstId'_ty.
      reflexivity.
    + reflexivity.
  - simpl in *. rewrite IHT1. rewrite IHT2. reflexivity.
  - simpl. Search up_ty_ty. admit.
  - reflexivity.
Admitted.  

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
    
    rewrite typingbeta_ren_commutable.
    reflexivity.
  - 
  
Admitted.
  

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
      destruct x0 as [|x0']; simpl; simpl in H2.
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
      intros. destruct x0; reflexivity. }
    rewrite H2. rewrite (H _ _ E1); try reflexivity.
    intros. rewrite nth_error_map in H3.
    destruct (nth_error Gamma x0) as [U' |] eqn: EqU'; try discriminate.
    simpl in H3. inversion H3. subst U. apply H1 in EqU'.
    apply context_shift. assumption.
  - (* TmUnit *)
    simpl in *.
    inversion H; subst; reflexivity.
Qed.




Theorem var_subst_preserves_typing :
  (
    forall t Gamma s T S,
    typing (S :: Gamma) t = return T ->
    typing_vl Gamma s = return S ->
    typing Gamma (beta_red t s) = return T
  ) /\ (
    forall v Gamma s T S,
      typing_vl (S :: Gamma) v = return T ->
      typing_vl Gamma s = return S ->
      typing Gamma (beta_red (TmVal v) s) = return T
  ).
Proof.
  apply tm_vl_mut_ind; intros.
  - simpl; unfold beta_red in *.
    rename H into IHt1. rename H0 into IHt2.
    apply invert_typing_app in H1 as [T1 [Ht1 Ht2] ].
    rewrite IHt1 with (T:=<{{T1->T}}>) (S:=S); try assumption.
    rewrite IHt2 with (T:=T1) (S:=S); try assumption.
    rewrite ty_beq_refl. reflexivity.
  - simpl; unfold beta_red in *. rename H into IH.
    apply invert_typing_tyapp in H0 as [T1 [Ht HT] ].
    rewrite IH with (T:=<{{-/,T1}}>) (S:=S); try assumption.
    replace (subst_ty sigma_ty_empty t0) with t0.
    + subst T. rewrite rinstId'_ty. reflexivity.
    + apply sigma_ty_empty_stable.
  - simpl; unfold beta_red in *. rename H into IH.
    simpl in IH. rewrite IH with (T:=T) (S:=S); auto.
  - simpl; unfold beta_red in *. unfold sigma_tm_one.
    destruct n as [|n'] eqn: Eqn; simpl; simpl in H0.
    + rewrite renRen_vl. unfold core.funcomp, id.
      simpl. rewrite rinstId'_vl.
      simpl in H. rewrite H0. assumption.
    + simpl in H. assumption.
  - simpl. simpl in H0. rewrite instId'_ty. rewrite rinstId'_ty.
    destruct (typing (t::S::Gamma) t0) as [T1|] eqn: Tyt0; try discriminate.
    inversion H0. 
    replace (upRen_vl_ty id) with (@id nat) by (unfold upRen_vl_ty; reflexivity).
    replace (up_vl_ty sigma_ty_empty) with sigma_ty_empty by (unfold up_vl_ty; reflexivity).
    unfold beta_red in H.
    replace (upRen_vl_vl pred) with (@id nat).
    + admit.
    + apply functional_extensionality. intros.
      unfold upRen_vl_vl, unscoped.up_ren, unscoped.scons. destruct x0.
      * reflexivity.
      * simpl. unfold core.funcomp. 
    unfold up_vl_vl, unscoped.scons, unscoped.var_zero,
    unscoped.id, unscoped.shift, core.funcomp.
    simpl in H. admit.
  - simpl; unfold beta_red in *.
    replace (upRen_ty_ty id) with (@id nat) by (apply functional_extensionality; intros; destruct x0; reflexivity).
    replace (up_ty_ty sigma_ty_empty) with sigma_ty_empty by (apply functional_extensionality; intros; destruct x0; reflexivity).
    simpl in H0.
    destruct (typing (ren_ty Datatypes.S S :: map (ren_ty Datatypes.S) Gamma) t) as [T1|] eqn: Tyt1;
    inversion H0.
    apply H with (s:=s) in Tyt1.
    + replace (upRen_ty_vl pred) with pred
      by (apply functional_extensionality; intros; destruct x0; reflexivity).
      replace (up_ty_vl (sigma_tm_one 0 (ren_vl id Datatypes.S s))) with (sigma_tm_one 0 (ren_vl id Datatypes.S s)).
      rewrite Tyt1. reflexivity.
      * admit.
    + admit.
    

    rewrite weaking_var with (Gamma:=(S::t::Gamma)) (T:=T1).
    + reflexivity.
    + admit.
    + intros. destruct x0 as [|x0'].
      * simpl; simpl in H2.  assumption.
      * simpl. simpl in H2.  destruct x0'.
        { simpl in H2. simpl. admit.    }
        { simpl in H2. simpl. assumption. }
    
    Search subst_tm.
    + simpl in IH.
      rewrite IH with (T:=T) (S:=S); auto.
    + simpl in IH.
      rewrite IH with (T:=T) (S:=S); auto.
    + assumption.
  - 
   
Admitted.


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
        apply var_subst_preserves_typing with T1; assumption.
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
      admit.
  - discriminate.
Admitted.

