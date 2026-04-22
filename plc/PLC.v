From Stdlib Require Import FunctionalExtensionality.

From PLC Require Export Maps.

(** * Polymorphic lambda calculus *)

(** *** Types *)
Inductive ty : Type :=
  | TyVar (X: string)
  | TyArrow (T1 T2: ty)
  | TyForall (X: string) (T1: ty)
  | TyUnit 
.

Inductive tm : Type :=
  | TmVar (x: string)
  | TmAbs (x: string) (T: ty) (t: tm)
  | TmApp (t1 t2: tm)
  | TmTyAbs (X: string) (t: tm)
  | TmTyApp (t: tm) (T: ty)
  | TmUnit
.

Declare Scope plc_scope.
Open Scope plc_scope.

Declare Custom Entry plc_ty.
Declare Custom Entry plc_tm.

(* 変数に関するフォールバック *)
Notation "x" := x (in custom plc_ty at level 0, x constr at level 0) : plc_scope.
Notation "x" := x (in custom plc_tm at level 0, x constr at level 0) : plc_scope.

(* 型と項をくくるための括弧表記 *)
Notation "<{{ T }}>" := T (T custom plc_ty at level 99) : plc_scope.

(* ----- 型 (ty) の Notation ----- *)
Notation "( T )" := T (in custom plc_ty, T custom plc_ty at level 99) : plc_scope.
Notation "T1 -> T2" := (TyArrow T1 T2) (in custom plc_ty at level 50, right associativity) : plc_scope.
Notation "'-/' X , T" := (TyForall X T) (in custom plc_ty at level 90, X constr at level 0, T custom plc_ty at level 90) : plc_scope.
Notation "'Unit'" := TyUnit (in custom plc_ty at level 0) : plc_scope.

Notation "<{ t }>" := t (t custom plc_tm at level 200) : plc_scope.

(* ----- 項 (term) の Notation ----- *)
Notation "( t )" := t (in custom plc_tm, t custom plc_tm at level 99) : plc_scope.
Notation "'unit'" := TmUnit (in custom plc_tm at level 0) : plc_scope.

(* 関数適用 (左結合) *)
Notation "t1 t2" := (TmApp t1 t2) (in custom plc_tm at level 11, left associativity) : plc_scope.
(* 関数抽象: \x:T, t *)
Notation "\ x : T , t" := (TmAbs x T t) (in custom plc_tm at level 90, x constr at level 0, T custom plc_ty at level 99, t custom plc_tm at level 90) : plc_scope.

(* 型適用: t [T] *)
Notation "t [ T ]" := (TmTyApp t T) (in custom plc_tm at level 11, t custom plc_tm, T custom plc_ty at level 0) : plc_scope.

Coercion TyVar : string >-> ty.
Coercion TmVar : string >-> tm.

Notation "'\\' X , t" := (TmTyAbs X t) (in custom plc_tm at level 90, X constr at level 0, t custom plc_tm at level 90) : plc_scope.

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

Reserved Notation "'[' x ':=' s ']' t" (in custom plc_tm at level 5, x global, s custom plc_tm,
      t custom plc_tm at next level, right associativity).

Fixpoint subst (x: string) (s: tm) (t: tm) : tm :=
  match t with
  | TmVar y => if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{[x:=s] t1 ([x:=s] t2)}>
  | <{\\X, t1}> =>
      <{\\X, [x:=s] t1}>
  | <{t1 [T]}> =>
      <{[x:=s]t1 [T]}>
  | <{unit}> => <{unit}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom plc_tm).

Reserved Notation "'[' X ':=' S ']' T" (in custom plc_ty at level 5, X global, S custom plc_ty,
      T custom plc_ty at next level, right associativity).

Fixpoint ty_subst (X: string) (S T: ty) : ty :=
  match T with
  | TyVar Y =>
      if String.eqb X Y then S else T
  | <{{T1 -> T2}}> =>
      <{{[X:=S]T1 -> [X:=S]T2}}>
  | <{{-/Y, T1}}> =>
      if String.eqb X Y then T else <{{-/Y, [X:=S]T1}}>
  | <{{Unit}}> => <{{Unit}}>
  end

where "'[' X ':=' S ']' T" := (ty_subst X S T) (in custom plc_ty).

Reserved Notation "'[[' x ':=' s ']]' t" (in custom plc_tm at level 6, x global, s custom plc_tm,
      t custom plc_tm at next level, right associativity).

Fixpoint tm_ty_subst (X: string) (S: ty) (t: tm) : tm :=
  match t with
  | TmVar y => y
  | <{\x:T, t1}> =>
      <{\x:[X:=S]T, [[X:=S]] t1}>
  | <{t1 t2}> =>
      <{[[X:=S]] t1 ([[X:=S]] t2)}>
  | <{\\Y, t1}> =>
      if String.eqb X Y then t else <{\\Y, [[X:=S]] t1}>
  | <{t1 [T]}> =>
      <{[[X:=S]]t1 [([X:=S]T)]}>
  | <{unit}> => <{unit}>
  end

where "'[[' X ':=' S ']]' t" := (tm_ty_subst X S t) (in custom plc_tm).

Reserved Notation "t '-->' t'" (at level 40).

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_tyabs : forall X t1,
      value <{\\X, t1}>
  | v_unit :
      value <{unit}>
.

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t v,
         value v ->
         <{(\x:T, t) v}> --> <{ [x:=v]t }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_TApp : forall t1 t1' T,
         t1 --> t1' ->
         <{t1[T]}> --> <{t1'[T]}>
  | ST_TAppAbs : forall X t1 T,
         <{(\\X, t1) [T]}> --> <{[[X:=T]] t1}>

where "t '-->' t'" := (step t t').

Inductive multi {X:Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | multi_refl  : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                   R x y ->
                   multi R y z ->
                   multi R x z.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Definition context := partial_map ty.

Notation "x '|->' v ';' m " := (update m x v)
  (in custom plc_tm at level 0, x constr at level 0, v  custom plc_ty, right associativity) : plc_scope.

Notation "x '|->' v " := (update empty x v)
  (in custom plc_tm at level 0, x constr at level 0, v custom plc_ty) : plc_scope.

Notation "'empty'" := empty (in custom plc_tm) : plc_scope.

Reserved Notation "<{ Gamma '|--' t '\in' T }>"
            (at level 0, Gamma custom plc_tm at level 200, t custom plc_tm, T custom plc_ty).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      <{ Gamma |-- x \in T1 }>
  | T_Abs : forall Gamma x T1 T2 t1,
      <{ x |-> T2 ; Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \x:T2, t1 \in T2 -> T1 }>
  | T_App : forall T1 T2 Gamma t1 t2,
      <{ Gamma |-- t1 \in T2 -> T1 }> ->
      <{ Gamma |-- t2 \in T2 }> ->
      <{ Gamma |-- t1 t2 \in T1 }>
  | T_TAbs : forall Gamma t1 X T1,
      <{ Gamma |-- t1 \in T1 }> ->
      <{ Gamma |-- \\X, t1 \in -/X, T1 }>
  | T_TApp : forall Gamma t1 X T1 S T1', 
      T1' = <{{[X:=S]T1}}> ->
      <{ Gamma |-- t1 \in -/X, T1 }> ->
      <{ Gamma |-- t1 [S] \in T1' }>
  | T_Unit : forall Gamma,
      <{ Gamma |-- unit \in Unit }>

where "<{ Gamma '|--' t '\in' T }>" := (has_type Gamma t T) : plc_scope.

(* Props *)
(* Progress *)
Lemma normal_form_abs: forall t T1 T2, 
  value t ->
  <{ empty |-- t \in T1 -> T2 }> ->
  exists x t1, t = <{\x: T1, t1}>.
Proof.
  intros t T1 T2 Hv.
  destruct Hv; intros; inversion H.
  - exists x0, t1. reflexivity.
Qed.

Lemma normal_form_tyabs: forall t X T,
  value t ->
  <{ empty |-- t \in -/X, T }> ->
  exists t1, t = <{\\X, t1}>.
Proof.
  intros. destruct H; intros; inversion H0.
  - exists t1. reflexivity.
Qed.

Theorem progress: forall t T,
  <{ empty |-- t \in T }> ->
  value t \/ exists t', t --> t'.
Proof.
  intros. remember empty as Gamma.
  induction H; subst Gamma.
  - discriminate H.
  - left. apply v_abs.
  - right. destruct IHhas_type1 as [IH1|IH1]; try reflexivity.
    + destruct IHhas_type2 as [IH2|IH2]; try reflexivity.
      * specialize (normal_form_abs _ _ _ IH1 H) as [x_ [t_ Hnf] ].
        subst t1.
        exists <{[x_:=t2]t_}>. constructor. apply IH2.
      * destruct IH2 as [t2' IH2].
        exists <{t1 t2'}>. apply ST_App2; assumption.
    + destruct IH1 as [t1' IH1].
      exists <{t1' t2}>. apply ST_App1; assumption.
  - left. apply v_tyabs.
  - right. destruct IHhas_type as [IH|IH]; try reflexivity.
    + specialize (normal_form_tyabs _ _ _ IH H0) as [t1' Hnf]. subst t1.
      eexists. apply ST_TAppAbs.
    + destruct IH as [t1' IH]. eexists. apply ST_TApp. apply IH.
  - left. apply v_unit.
Qed.

(* Preservation *)
(* Variables *)
Inductive var_appears_free_in (x : string) : tm -> Prop :=
  | vaf_var : var_appears_free_in x <{x}>
  | vaf_app1 : forall t1 t2,
      var_appears_free_in x t1 ->
      var_appears_free_in x <{t1 t2}>
  | vaf_app2 : forall t1 t2,
      var_appears_free_in x t2 ->
      var_appears_free_in x <{t1 t2}>
  | vaf_abs : forall y T1 t1,
      y <> x  ->
      var_appears_free_in x t1 ->
      var_appears_free_in x <{\y:T1, t1}>
  | vaf_tyapp : forall t T,
      var_appears_free_in x t ->
      var_appears_free_in x <{t[T]}>
  | vaf_tyabs : forall X t,
      var_appears_free_in x t ->
      var_appears_free_in x <{\\X, t}>.
Hint Constructors var_appears_free_in : core.

Inductive not_var_appears_free_in (x : string) : tm -> Prop :=
  | nvaf_var : forall (y: string),
      y <> x ->
      not_var_appears_free_in x <{y}>
  | nvaf_app : forall t1 t2,
      not_var_appears_free_in x t1 ->
      not_var_appears_free_in x t2 ->
      not_var_appears_free_in x <{t1 t2}>
  | nvaf_abs1 : forall T1 t1,
      not_var_appears_free_in x <{\x:T1, t1}>
  | nvaf_abs2 : forall y T1 t1,
      y <> x ->
      not_var_appears_free_in x t1 ->
      not_var_appears_free_in x <{\y:T1, t1}>
  | nvaf_tyapp : forall t T,
      not_var_appears_free_in x t ->
      not_var_appears_free_in x <{t[T]}>
  | nvaf_tyabs : forall X t,
      not_var_appears_free_in x t ->
      not_var_appears_free_in x <{\\X, t}>
  | nvaf_unit :
      not_var_appears_free_in x <{unit}>.
Hint Constructors not_var_appears_free_in : core.

Lemma notvaf_nvaf_iff : forall x t,
  ~ var_appears_free_in x t <-> not_var_appears_free_in x t.
Proof.
  intros x t. split; intro H.
  - induction t.
    + constructor. intros contra. subst. apply H. constructor.
    + destruct (x=?x0)%string eqn: Eqx.
      * rewrite eqb_eq in Eqx. subst. constructor. 
      * constructor.
        { apply eqb_neq. rewrite eqb_sym. assumption. }
        { apply IHt. intro contra. apply H. constructor.
          - apply eqb_neq. rewrite eqb_sym. assumption.
          - assumption. }
    + constructor; [apply IHt1| apply IHt2]; 
      intro Hvaf; apply H; [apply vaf_app1 | apply vaf_app2];
      assumption.
    + constructor. apply IHt. intro Hvaf. apply H.
      constructor. assumption.
    + constructor. apply IHt. intro Hvaf. apply H.
      constructor. assumption.
    + constructor.    
  - intro contra. induction contra; inversion H; subst; auto.
Qed.

Inductive var_appears_bounded_in (x : string) : tm -> Prop :=
  | vab_app1 : forall t1 t2,
      var_appears_bounded_in x t1 ->
      var_appears_bounded_in x <{t1 t2}>
  | vab_app2 : forall t1 t2,
      var_appears_bounded_in x t2 ->
      var_appears_bounded_in x <{t1 t2}>
  | vab_abs1 : forall T1 t1,
      var_appears_bounded_in x <{\x:T1, t1}>
  | vab_abs2 : forall y T1 t1,
      y <> x ->
      var_appears_bounded_in x t1 ->
      var_appears_bounded_in x <{\y:T1, t1}>
  | vab_tyabs : forall X t,
      var_appears_bounded_in x t ->
      var_appears_bounded_in x <{\\X, t}>
  | vab_tyapp : forall t T,
      var_appears_bounded_in x t ->
      var_appears_bounded_in x <{t[T]}>.
Hint Constructors var_appears_bounded_in : core.

Inductive not_var_appears_bounded_in (x : string) : tm -> Prop :=
  | nvab_var : forall (y: string),
      not_var_appears_bounded_in x <{y}>
  | nvab_app : forall t1 t2,
      not_var_appears_bounded_in x t1 ->
      not_var_appears_bounded_in x t2 ->
      not_var_appears_bounded_in x <{t1 t2}>
  | nvab_abs : forall y T1 t1,
      y <> x ->
      not_var_appears_bounded_in x t1 ->
      not_var_appears_bounded_in x <{\y:T1, t1}>
  | nvab_tyabs : forall X t,
      not_var_appears_bounded_in x t ->
      not_var_appears_bounded_in x <{\\X, t}>
  | nvab_tyapp : forall t T,
      not_var_appears_bounded_in x t ->
      not_var_appears_bounded_in x <{t[T]}>
  | nvab_unit :
      not_var_appears_bounded_in x <{unit}>.
Hint Constructors not_var_appears_bounded_in : core.

Lemma notvab_nvab_iff : forall x t,
  ~ var_appears_bounded_in x t <-> not_var_appears_bounded_in x t.
Proof.
  intros x t. split; intro H.
  - induction t.
    + constructor.
    + destruct (x =? x0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst. exfalso.
        apply H. constructor.
      * apply nvab_abs.
        -- intro contra. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- apply IHt. intro contra. apply H. apply vab_abs2; auto.
            intro contra2. subst. rewrite String.eqb_refl in Heq. discriminate.
    + constructor; [apply IHt1|apply IHt2]; intro contra; apply H; eauto.
    + constructor. apply IHt. intro Hvab. apply H.
      constructor. assumption.
    + constructor. apply IHt. intro Hvab. apply H.
      constructor. assumption.
    + constructor. 
  - intro contra. induction contra; inversion H; subst; auto.
Qed.

Inductive var_bounded_left_notfree_right : tm -> Prop :=
  | vblnfr_var : forall (x: string),
      var_bounded_left_notfree_right <{x}>
  | vblnfr_abs : forall x T1 t1,
      var_bounded_left_notfree_right t1 ->
      var_bounded_left_notfree_right <{\x:T1, t1}>
  | vblnfr_app : forall t1 t2,
      ( forall x,
        var_appears_free_in x t2 ->
        ~ var_appears_bounded_in x t1 ) ->
      var_bounded_left_notfree_right t1 ->
      var_bounded_left_notfree_right t2 ->
      var_bounded_left_notfree_right <{t1 t2}>
  | vblnfr_tyabs : forall X t,
      var_bounded_left_notfree_right t ->
      var_bounded_left_notfree_right <{\\X, t}>
  | vblnfr_tyapp : forall t T,
      var_bounded_left_notfree_right t ->
      var_bounded_left_notfree_right <{t[T]}>
  | vblnfr_unit :
      var_bounded_left_notfree_right <{unit}>.
Hint Constructors var_bounded_left_notfree_right : core.

(* Type Variables *)
Inductive tyvar_appears_free_in_ty (X: string) : ty -> Prop :=
  | tvaf_var :
      tyvar_appears_free_in_ty X (TyVar X)
  | tvaf_arrow1 : forall T1 T2,
      tyvar_appears_free_in_ty X T1 ->
      tyvar_appears_free_in_ty X <{{T1 -> T2}}>
  | tvaf_arrow2 : forall T1 T2,
      tyvar_appears_free_in_ty X T2 ->
      tyvar_appears_free_in_ty X <{{T1 -> T2}}>
  | tvaf_forall : forall Y T1,
      X <> Y ->
      tyvar_appears_free_in_ty X T1 ->
      tyvar_appears_free_in_ty X <{{-/Y, T1}}>.

Inductive not_tyvar_appears_free_in_ty (X: string) : ty -> Prop :=
  | ntvaf_var : forall Y,
      X <> Y ->
      not_tyvar_appears_free_in_ty X (TyVar Y)
  | ntvaf_arrow : forall T1 T2,
      not_tyvar_appears_free_in_ty X T1 ->
      not_tyvar_appears_free_in_ty X T2 ->
      not_tyvar_appears_free_in_ty X <{{T1 -> T2}}>
  | ntvaf_forall_bound : forall T1,
      not_tyvar_appears_free_in_ty X <{{-/X, T1}}>
  | ntvaf_forall_free : forall Y T1,
      X <> Y ->
      not_tyvar_appears_free_in_ty X T1 ->
      not_tyvar_appears_free_in_ty X <{{-/Y, T1}}>
  | ntvaf_unit :
      not_tyvar_appears_free_in_ty X <{{Unit}}>.

Lemma nottvaf_ntvaf_iff : forall X T,
  ~ tyvar_appears_free_in_ty X T <-> not_tyvar_appears_free_in_ty X T.
Proof.
  intros X T. split; intro H.
  - induction T.
    + destruct (X =? X0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst. exfalso. apply H. constructor.
      * constructor. intro contra. subst. rewrite eqb_refl in Heq. discriminate.
    + constructor.
      * apply IHT1. intro contra. apply H. apply tvaf_arrow1; auto.
      * apply IHT2. intro contra. apply H. apply tvaf_arrow2; auto.
    + destruct (X =? X0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst. constructor.
      * apply ntvaf_forall_free.
        -- intro contra. subst. rewrite eqb_refl in Heq. discriminate.
        -- apply IHT. intro contra. apply H. apply tvaf_forall; auto.
           intro contra_eq. subst. rewrite eqb_refl in Heq. discriminate.
    + constructor.
  - intro contra. induction contra; inversion H; subst; auto.
Qed.

Inductive tyvar_appears_bounded_in_ty  (X: string) : ty -> Prop :=
  | tvab_arrow1 : forall T1 T2,
      tyvar_appears_bounded_in_ty X T1 ->
      tyvar_appears_bounded_in_ty X <{{T1 -> T2}}>
  | tvab_arrow2 : forall T1 T2,
      tyvar_appears_bounded_in_ty X T2 ->
      tyvar_appears_bounded_in_ty X <{{T1 -> T2}}>
  | tvab_forall_bound : forall T1,
      tyvar_appears_bounded_in_ty X <{{-/X, T1}}>
  | tvab_forall : forall Y T1,
      tyvar_appears_bounded_in_ty X T1 ->
      tyvar_appears_bounded_in_ty X <{{-/Y, T1}}>
.

Inductive not_tyvar_appears_bounded_in_ty (X: string) : ty -> Prop :=
  | ntvab_var : forall Y,
      not_tyvar_appears_bounded_in_ty X (TyVar Y)
  | ntvab_arrow : forall T1 T2,
      not_tyvar_appears_bounded_in_ty X T1 ->
      not_tyvar_appears_bounded_in_ty X T2 ->
      not_tyvar_appears_bounded_in_ty X <{{T1 -> T2}}>
  | ntvab_forall : forall Y T1,
      X <> Y ->
      not_tyvar_appears_bounded_in_ty X T1 ->
      not_tyvar_appears_bounded_in_ty X <{{-/Y, T1}}>
  | ntvab_unit :
      not_tyvar_appears_bounded_in_ty X <{{Unit}}>
.

Lemma nottvab_ntvab_iff : forall X T,
  ~ tyvar_appears_bounded_in_ty X T <-> not_tyvar_appears_bounded_in_ty X T.
Proof.
  intros X T. split; intro H.
  - induction T.
    + constructor.
    + constructor.
      * apply IHT1. intro contra. apply H. apply tvab_arrow1; auto.
      * apply IHT2. intro contra. apply H. apply tvab_arrow2; auto.
    + destruct (X =? X0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst.
        exfalso. apply H. constructor.
      * apply ntvab_forall.
        -- intro contra. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- apply IHT. intro contra. apply H. apply tvab_forall; auto.
    + constructor.
  - intro contra. induction contra; inversion H; subst; auto.
Qed.

Inductive tyvar_appears_free_in_term (X: string) : tm -> Prop :=
  | tvaft_abs1 : forall x T t,
      tyvar_appears_free_in_ty X T ->
      tyvar_appears_free_in_term X (TmAbs x T t)
  | tvaft_abs2 : forall x T t,
      tyvar_appears_free_in_term X t ->
      tyvar_appears_free_in_term X (TmAbs x T t)
  | tvaft_app1 : forall t1 t2,
      tyvar_appears_free_in_term X t1 ->
      tyvar_appears_free_in_term X (TmApp t1 t2)
  | tvaft_app2 : forall t1 t2,
      tyvar_appears_free_in_term X t2 ->
      tyvar_appears_free_in_term X (TmApp t1 t2)
  | tvaft_tyabs : forall Y t,
      X <> Y ->
      tyvar_appears_free_in_term X t ->
      tyvar_appears_free_in_term X (TmTyAbs Y t)
  | tvaft_tyapp1 : forall t T,
      tyvar_appears_free_in_term X t ->
      tyvar_appears_free_in_term X (TmTyApp t T)
  | tvaft_tyapp2 : forall t T,
      tyvar_appears_free_in_ty X T ->
      tyvar_appears_free_in_term X (TmTyApp t T).

Inductive not_tyvar_appears_free_in_term (X: string) : tm -> Prop :=
  | ntvaft_var : forall x,
      not_tyvar_appears_free_in_term X (TmVar x)
  | ntvaft_abs : forall x T t,
      not_tyvar_appears_free_in_ty X T ->
      not_tyvar_appears_free_in_term X t ->
      not_tyvar_appears_free_in_term X (TmAbs x T t)
  | ntvaft_app : forall t1 t2,
      not_tyvar_appears_free_in_term X t1 ->
      not_tyvar_appears_free_in_term X t2 ->
      not_tyvar_appears_free_in_term X (TmApp t1 t2)
  | ntvaft_tyabs1 : forall t,
      not_tyvar_appears_free_in_term X (TmTyAbs X t)
  | ntvaft_tyabs2 : forall Y t,
      X <> Y ->
      not_tyvar_appears_free_in_term X t ->
      not_tyvar_appears_free_in_term X (TmTyAbs Y t)
  | ntvaft_tyapp : forall t T,
      not_tyvar_appears_free_in_term X t ->
      not_tyvar_appears_free_in_ty X T ->
      not_tyvar_appears_free_in_term X (TmTyApp t T)
  | ntvaft_unit :
      not_tyvar_appears_free_in_term X TmUnit.

Lemma nottvaft_ntvaft_iff : forall X t,
  ~ tyvar_appears_free_in_term X t <-> not_tyvar_appears_free_in_term X t.
Proof.
  intros X t. split; intro H.
  - induction t.
    + constructor.
    + constructor.
      * apply nottvaf_ntvaf_iff. intro contra. apply H. apply tvaft_abs1. assumption.
      * apply IHt. intro contra. apply H. apply tvaft_abs2. assumption.
    + constructor.
      * apply IHt1. intro contra. apply H. apply tvaft_app1. assumption.
      * apply IHt2. intro contra. apply H. apply tvaft_app2. assumption.
    + destruct (X =? X0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst. constructor.
      * constructor.
        -- intro contra. subst. rewrite String.eqb_refl in Heq. discriminate.
        -- apply IHt. intro contra. apply H. apply tvaft_tyabs; auto.
           intro contra_eq. subst. rewrite String.eqb_refl in Heq. discriminate.
    + constructor.
      * apply IHt. intro contra. apply H. apply tvaft_tyapp1. assumption.
      * apply nottvaf_ntvaf_iff. intro contra. apply H. apply tvaft_tyapp2. assumption.
    + constructor.
  - intro contra. induction contra; inversion H; subst; auto.
    + apply nottvaf_ntvaf_iff in H3. apply H3. assumption.
    + apply nottvaf_ntvaf_iff in H4. apply H4. assumption.
Qed.

Inductive tyvar_appears_bounded_in_term (X: string) : tm -> Prop :=
  | tvabt_abs1 : forall x T t,
      tyvar_appears_bounded_in_ty X T ->
      tyvar_appears_bounded_in_term X (TmAbs x T t)
  | tvabt_abs2 : forall x T t,
      tyvar_appears_bounded_in_term X t ->
      tyvar_appears_bounded_in_term X (TmAbs x T t)
  | tvabt_app1 : forall t1 t2,
      tyvar_appears_bounded_in_term X t1 ->
      tyvar_appears_bounded_in_term X (TmApp t1 t2)
  | tvabt_app2 : forall t1 t2,
      tyvar_appears_bounded_in_term X t2 ->
      tyvar_appears_bounded_in_term X (TmApp t1 t2)
  | tvabt_tyabs : forall Y t,
      tyvar_appears_bounded_in_term X t ->
      tyvar_appears_bounded_in_term X (TmTyAbs Y t)
  | tvabt_tyabs_bound : forall t,
      tyvar_appears_bounded_in_term X (TmTyAbs X t)
  | tvabt_tyapp1 : forall t T,
      tyvar_appears_bounded_in_term X t ->
      tyvar_appears_bounded_in_term X (TmTyApp t T)
  | tvabt_tyapp2 : forall t T,
      tyvar_appears_bounded_in_ty X T ->
      tyvar_appears_bounded_in_term X (TmTyApp t T)
.
Inductive not_tyvar_appears_bounded_in_term (X: string) : tm -> Prop :=
  | ntvabt_var : forall x,
      not_tyvar_appears_bounded_in_term X (TmVar x)
  | ntvabt_abs : forall x T t,
      not_tyvar_appears_bounded_in_term X t ->
      not_tyvar_appears_bounded_in_ty X T ->
      not_tyvar_appears_bounded_in_term X (TmAbs x T t)
  | ntvabt_app : forall t1 t2,
      not_tyvar_appears_bounded_in_term X t1 ->
      not_tyvar_appears_bounded_in_term X t2 ->
      not_tyvar_appears_bounded_in_term X (TmApp t1 t2)
  | ntvabt_tyabs : forall Y t,
      X <> Y ->
      not_tyvar_appears_bounded_in_term X t ->
      not_tyvar_appears_bounded_in_term X (TmTyAbs Y t)
  | ntvabt_tyapp : forall t T,
      not_tyvar_appears_bounded_in_term X t ->
      not_tyvar_appears_bounded_in_ty X T ->
      not_tyvar_appears_bounded_in_term X (TmTyApp t T)
  | ntvabt_unit :
      not_tyvar_appears_bounded_in_term X TmUnit
.

Lemma nottvabt_ntvabt_iff : forall X t,
  ~ tyvar_appears_bounded_in_term X t <-> not_tyvar_appears_bounded_in_term X t.
Proof.
  intros X t. split; intro H.
  - induction t; constructor.
    + apply IHt. intro contra. apply H. apply tvabt_abs2; auto.
    + apply nottvab_ntvab_iff. intro contra. apply H. apply tvabt_abs1; auto.
    + apply IHt1. intro contra. apply H. apply tvabt_app1; auto.
    + apply IHt2. intro contra. apply H. apply tvabt_app2; auto.
    + destruct (X =? X0)%string eqn:Heq.
      * rewrite String.eqb_eq in Heq. subst. exfalso. apply H. apply tvabt_tyabs_bound.
      * intro contra. subst. rewrite String.eqb_refl in Heq. discriminate.
    + apply IHt. intro contra. apply H. apply tvabt_tyabs; auto.
    + apply IHt. intro contra. apply H. apply tvabt_tyapp1; auto.
    + apply nottvab_ntvab_iff. intro contra. apply H. apply tvabt_tyapp2; auto.
  - intro contra. induction contra; inversion H; subst; auto.
    + apply nottvab_ntvab_iff in H5. apply H5. assumption.
    + apply nottvab_ntvab_iff in H4. apply H4. assumption.
Qed.

Definition tyvar_appears_free_in_context (X: string) (Gamma: context) :=
  exists x T, Gamma x = Some T /\ tyvar_appears_free_in_ty X T.

Definition not_tyvar_appears_free_in_context (X: string) (Gamma: context) :=
  forall x T, Gamma x = Some T -> not_tyvar_appears_free_in_ty X T.

Lemma nottvafc_ntvafc_iff : forall X Gamma, 
  ~ tyvar_appears_free_in_context X Gamma <-> not_tyvar_appears_free_in_context X Gamma.
Proof.
  intros X Gamma. split; intro H.
  - unfold not_tyvar_appears_free_in_context.
    intros x T Hctx. apply nottvaf_ntvaf_iff.
    intro contra. apply H. unfold tyvar_appears_free_in_context.
    exists x, T. split; assumption.
  - intro contra. unfold tyvar_appears_free_in_context in contra.
    destruct contra as [x [T [Hctx Htvaf] ] ].
    unfold not_tyvar_appears_free_in_context in H.
    apply H in Hctx. apply nottvaf_ntvaf_iff in Hctx.
    apply Hctx. assumption.
Qed.

Definition tyvar_appears_bounded_in_context (X: string) (Gamma: context) :=
  exists x T, Gamma x = Some T /\ tyvar_appears_bounded_in_ty X T.

Definition not_tyvar_appears_bounded_in_context (X: string) (Gamma: context) :=
  forall x T, Gamma x = Some T -> not_tyvar_appears_bounded_in_ty X T.

Lemma nottvabc_ntvabc_iff : forall X Gamma, 
  ~ tyvar_appears_bounded_in_context X Gamma <-> not_tyvar_appears_bounded_in_context X Gamma.
Proof.
  intros X Gamma. split; intro H.
  - unfold not_tyvar_appears_bounded_in_context.
    intros x T Hctx. apply nottvab_ntvab_iff.
    intro contra. apply H. unfold tyvar_appears_bounded_in_context.
    exists x, T. split; assumption.
  - intro contra. unfold tyvar_appears_bounded_in_context in contra.
    destruct contra as [x [T [Hctx Htvab] ] ].
    unfold not_tyvar_appears_bounded_in_context in H.
    apply H in Hctx. apply nottvab_ntvab_iff in Hctx.
    apply Hctx. assumption.
Qed.

Inductive tyvar_bounded_left_notfree_right : tm -> Prop :=
  | tvblnfr_var : forall (x: string),
      tyvar_bounded_left_notfree_right <{x}>
  | tvblnfr_abs : forall x T1 t1,
      tyvar_bounded_left_notfree_right t1 ->
      tyvar_bounded_left_notfree_right <{\x:T1, t1}>
  | tvblnfr_app : forall t1 t2,
      tyvar_bounded_left_notfree_right t1 ->
      tyvar_bounded_left_notfree_right t2 ->
      tyvar_bounded_left_notfree_right <{t1 t2}>
  | tvblnfr_tyabs : forall X t,
      tyvar_bounded_left_notfree_right t ->
      tyvar_bounded_left_notfree_right <{\\X, t}>
  | tvblnfr_tyapp : forall t T,
      ( forall X,
        tyvar_appears_free_in_ty X T ->
        ~ tyvar_appears_bounded_in_term X t ) ->
      tyvar_bounded_left_notfree_right t ->
      tyvar_bounded_left_notfree_right <{t[T]}>
  | tvblnfr_unit :
      tyvar_bounded_left_notfree_right <{unit}>.
Hint Constructors tyvar_bounded_left_notfree_right : core.

Inductive bounded_tyvar_unique : tm -> Prop :=
  | btvuni_var : forall x,
      bounded_tyvar_unique (TmVar x)
  | btvuni_abs : forall x T t,
      bounded_tyvar_unique t ->
      bounded_tyvar_unique (TmAbs x T t)
  | btvuni_app : forall t1 t2,
      bounded_tyvar_unique t1 ->
      bounded_tyvar_unique t2 ->
      bounded_tyvar_unique (TmApp t1 t2)
  | btvuni_tyabs : forall X t,
      not_tyvar_appears_bounded_in_term X t ->
      bounded_tyvar_unique t ->
      bounded_tyvar_unique (TmTyAbs X t)
  | btvuni_tyapp : forall t T,
      bounded_tyvar_unique t ->
      bounded_tyvar_unique (TmTyApp t T)
  | btvuni_unit :
      bounded_tyvar_unique TmUnit
.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     <{ Gamma  |-- t \in T }>  ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; intros; econstructor.
  - apply H0. assumption.
  - apply IHHt. apply includedin_update. apply H.
  - apply IHHt1. assumption.
  - apply IHHt2. assumption.
  - apply IHHt. assumption.
  - apply H.
  - apply IHHt. assumption.
Qed.

Lemma context_invariance : forall Gamma Gamma' t T,
     <{ Gamma |-- t \in T }> ->
     (forall x, var_appears_free_in x t -> Gamma x = Gamma' x) ->
     <{ Gamma' |-- t \in T }>.
Proof.
  intros.
  generalize dependent Gamma'.
  induction H as [| ? x0 ????? | | | |]; intros; auto.
  - apply T_Var. rewrite <- H. symmetry. apply H0. apply vaf_var.
  - apply T_Abs. apply IHhas_type. intros.
    unfold update. unfold t_update. destruct (x0 =? x1)%string eqn:Eqx0.
    + reflexivity.
    + apply H0. apply vaf_abs.
      * rewrite <- eqb_neq. apply Eqx0.
      * apply H1.
  - eapply T_App.
    + apply IHhas_type1. intros. apply H1. apply vaf_app1. apply H2.
    + apply IHhas_type2. intros. apply H1. apply vaf_app2. apply H2.
  - constructor. apply IHhas_type. auto.
  - apply T_TApp with (X:=X0) (T1:=T1); try assumption.
    apply IHhas_type. auto.
  - constructor.
Qed.

Lemma var_subst_preserves_typing : forall Gamma x U t v T,
  ( forall y,
      var_appears_free_in y v -> ~ var_appears_bounded_in y t) ->
  <{ x |-> U ; Gamma |-- t \in T }> ->
  <{ Gamma |-- v \in U }>   ->
  <{ Gamma |-- [x:=v]t \in T }>.
Proof.
  intros Gamma x U t v T Hvar Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G Hv; simpl; eauto.
  - destruct (x =? x0)%string eqn: Eqx. 
    + subst. rewrite eqb_eq in Eqx. rewrite Eqx in H.
      unfold update in H. unfold t_update in H.
      rewrite eqb_refl in H. inversion H.
      rewrite <- H1; assumption. 
    + subst. apply T_Var. unfold update in H.
      unfold t_update in H. rewrite Eqx in H.
      apply H. 
  - destruct (x =? x0)%string eqn: Eqx.
    + apply T_Abs. apply weakening with (Gamma:= <{ x0 |-> T2; Gamma }>).
      * intros y T Hin. rewrite G in Hin. rewrite eqb_eq in Eqx.
        rewrite Eqx in Hin. rewrite update_shadow in Hin.
        apply Hin.
      * apply Ht.
    + apply T_Abs. apply IHHt.
      * intros y' Hy'. apply Hvar in Hy'. intro Hy''.
        rewrite notvab_nvab_iff in Hy'.
        inversion Hy'. rewrite <- notvab_nvab_iff in H3.
        apply H3. assumption.
      * rewrite G. rewrite update_permute.
        { reflexivity. }
        { rewrite <- eqb_neq. apply Eqx. }
      * apply context_invariance with (Gamma:=Gamma'); try assumption.
        intros y Hy. apply Hvar in Hy .
        rewrite notvab_nvab_iff in Hy. inversion Hy.
        unfold update, t_update. rewrite <- eqb_neq in H1.
        rewrite H1. reflexivity.
  - apply T_App with T2;
    [apply IHHt1 | apply IHHt2];
    try assumption;
    intros; apply Hvar in H; rewrite notvab_nvab_iff in *;
    inversion H; assumption.
  - constructor. apply IHHt; auto. 
    intros y Hyf Hyb. apply Hvar in Hyf.
    apply Hyf. constructor. assumption.
  - apply T_TApp with (X:=X0) (T1:=T1).
    + assumption.
    + apply IHHt; try assumption.
      intros y Hyf Hyb. apply Hvar in Hyf.
      apply Hyf. constructor. assumption.
  - apply T_Unit.
Qed.

Definition context_ty_subst X S (Gamma: context) : context :=
    fun x =>
      match Gamma x with
      | Some T => Some (<{{[X:=S] T}}>)
      | None => None
      end.

Lemma ntvaf_subst_eq_ty : forall X S T,
  not_tyvar_appears_free_in_ty X T ->
  T = <{{ [X:=S] T }}>.
Proof.
  intros X S T H.
  induction H; simpl;
  try rewrite eqb_refl;
  try (apply eqb_neq in H; rewrite H);
  try reflexivity.
  - rewrite <- IHnot_tyvar_appears_free_in_ty1.
    rewrite <- IHnot_tyvar_appears_free_in_ty2.
    reflexivity.
  - rewrite <- IHnot_tyvar_appears_free_in_ty. reflexivity.
Qed.

Lemma ntvaf_subst_eq_context : forall X S Gamma,
  not_tyvar_appears_free_in_context X Gamma ->
  Gamma = context_ty_subst X S Gamma.
Proof.
  unfold not_tyvar_appears_free_in_context, context_ty_subst.
  intros X T Gamma H. apply functional_extensionality.
  intros x. destruct (Gamma x) eqn: EqY.
  - f_equal. apply ntvaf_subst_eq_ty. apply H with x. 
    assumption.
  - reflexivity.
Qed.

Lemma update_subst_context : forall x X S T Gamma,
  context_ty_subst X S <{ x |-> T; Gamma }> =
  <{ x |-> <{{[X:=S]T}}> ; (context_ty_subst X S Gamma) }> .
Proof.
  intros. apply functional_extensionality.
  intro y. unfold context_ty_subst, update, t_update.
  destruct (x0 =? y)%string; reflexivity.
Qed.

Lemma ntvab_subst_preservation : forall X Y T S,
  not_tyvar_appears_bounded_in_ty X T ->
  not_tyvar_appears_bounded_in_ty X S ->
  not_tyvar_appears_bounded_in_ty X <{{ [Y := S] T }}>.
Proof.
  intros X Y T S HT HS. induction T; simpl.
  - destruct (Y=?X0)%string; assumption.
  - inversion HT. constructor.
    + apply IHT1. assumption.
    + apply IHT2. assumption.
  - destruct (Y=?X0)%string.
    + assumption.
    + inversion HT. constructor;
      try apply IHT; assumption.
  - assumption.
Qed.

Lemma ntvab_typing : forall X Gamma t T,
  not_tyvar_appears_bounded_in_context X Gamma ->
  not_tyvar_appears_bounded_in_term X t ->
  <{ Gamma |-- t \in T }> ->
  not_tyvar_appears_bounded_in_ty X T.
Proof.
  intros X Gamma t T Hctx Htm Hty.
  induction Hty; inversion Htm; subst.
  - apply Hctx with (x:=x0). assumption.
  - apply ntvab_arrow.
    + unfold not_tyvar_appears_bounded_in_context, update, t_update in Hctx.
      assumption.
    + apply IHHty; try assumption.
      intros y Ty Hy. unfold update, t_update in Hy.
      destruct (x0 =? y)%string.
      * inversion Hy. inversion Htm. subst. assumption.
      * apply Hctx with (x:=y). assumption.
  - apply IHHty1 in Hctx; try assumption.
    inversion Hctx; assumption.
  - apply ntvab_forall.
    + assumption.
    + apply IHHty; assumption.
  - apply IHHty in Hctx; try assumption.
    inversion Hctx. inversion Htm.
    apply ntvab_subst_preservation; assumption.
  - apply ntvab_unit.
Qed.

Lemma ty_subst_distribution : forall X Y S1 S2 T,
  X <> Y ->
  not_tyvar_appears_bounded_in_ty X T ->
  not_tyvar_appears_free_in_ty Y S1 ->
  <{{ [X:=S1]([Y:=S2]T) }}> = <{{ [Y:=[X:=S1]S2]([X:=S1]T) }}>.
Proof.
  intros X Y S1 S2 T Neq H1 H2.
  induction T.
  - simpl.
    destruct (Y=?X0)%string eqn: EqY;
    destruct (X=?X0)%string eqn: EqX;
    simpl.
    + exfalso.
      apply eqb_eq in EqX. apply eqb_eq in EqY. subst.
      apply Neq. reflexivity.
    + rewrite EqY. reflexivity.
    + rewrite EqX. apply ntvaf_subst_eq_ty. apply H2.
    + rewrite EqX. rewrite EqY. reflexivity.
  - simpl. inversion H1.
    rewrite IHT1; try assumption.
    rewrite IHT2; try assumption.
    reflexivity.
  - inversion H1. simpl.
    apply eqb_neq in H3 as NeqX.
    destruct (Y=?X0)%string eqn: EqY; simpl.
    + rewrite NeqX. apply eqb_eq in EqY. subst.
      simpl. rewrite eqb_refl. reflexivity.
    + rewrite NeqX. rewrite IHT.
      * simpl. rewrite EqY. reflexivity. 
      * assumption.
  - reflexivity.
Qed.

Ltac IH_solve IH Htvblnfr :=
  apply IH; try reflexivity;
  try (intros _Y _HY; apply Htvblnfr in _HY as [_HYt _HYG];
      inversion _HYt; split); 
  assumption.

Lemma tysubst_preserves_typing : forall Gamma Gamma' X S t T,
  not_tyvar_appears_bounded_in_context X Gamma ->
  not_tyvar_appears_bounded_in_term X t ->
  ( forall Y,
      tyvar_appears_free_in_ty Y S ->
      not_tyvar_appears_bounded_in_term Y t /\ not_tyvar_appears_bounded_in_context Y Gamma )->
  <{ Gamma |-- t \in T }> ->
  Gamma' = context_ty_subst X S Gamma ->
  <{ Gamma' |-- [[X:=S]]t \in [X:=S]T }>.
Proof.
  intros Gamma Gamma' X S t T Hntabc Hntabt Htvblnfr H.
  generalize dependent Gamma'.
  induction H; simpl; intros;
  inversion Hntabt; subst.
  - apply T_Var. unfold context_ty_subst in *.
    destruct (Gamma x0).
    + f_equal. injection H as H'. rewrite H'. reflexivity.
    + discriminate.
  - apply T_Abs. rewrite <- update_subst_context.
    apply IHhas_type; try reflexivity; try assumption.
    + unfold not_tyvar_appears_bounded_in_context in *.
      unfold update, t_update. intros.
      destruct (x0=?x1)%string.
      * inversion H0. subst. assumption.
      * apply Hntabc with x1. assumption.
    + intros Y HY. apply Htvblnfr in HY as [HYt HYG]. split.
      * inversion HYt. assumption.
      * intros x T Hx. unfold update, t_update in Hx.
        destruct (x0=?x)%string.
        { inversion Hx. subst. inversion HYt. assumption. }
        { apply HYG in Hx. assumption. }
  - eapply T_App.
    + IH_solve IHhas_type1 Htvblnfr.
    + IH_solve IHhas_type2 Htvblnfr.
  - apply eqb_neq in H3. rewrite H3. apply T_TAbs.
    IH_solve IHhas_type Htvblnfr.
  - apply ntvab_typing with (X:=X) in H0 as HT; try assumption.
    inversion HT.
    apply T_TApp with (X:=X0) (S:=<{{[X:=S]S0}}>)
    (T1:=<{{[X:=S]T1}}>) (T1':=<{{[X:=S]([X0:=S0]T1)}}>).
    + apply ty_subst_distribution; try assumption.
      apply nottvaf_ntvaf_iff. intro HX0S.
      apply Htvblnfr in HX0S as [Ht HG].
      inversion Ht.
      specialize (ntvab_typing _ _ _ _ HG H8 H0) as contra.
      apply nottvab_ntvab_iff in contra. apply contra. constructor.
    + apply eqb_neq in H2. simpl in IHhas_type. rewrite H2 in IHhas_type.
      IH_solve IHhas_type Htvblnfr.
  - apply T_Unit.
Qed.

Ltac IH_solve_2 IH Htvb Ctvabt Htvf1 Ctvaft Htvf2 :=
  apply IH; try reflexivity; try assumption;
  try (intros; apply Htvb; apply Ctvabt; assumption);
  try (intros; apply Htvf1; apply Ctvaft; assumption);
  try (intros _X _H; apply Htvf2 in _H; inversion _H; assumption).

Theorem type_preservation: forall Gamma t t' T,
  var_bounded_left_notfree_right t ->
  tyvar_bounded_left_notfree_right t ->
  bounded_tyvar_unique t ->
  ( forall X,
      tyvar_appears_bounded_in_term X t ->
      not_tyvar_appears_bounded_in_context X Gamma ) ->
  ( forall X,
      tyvar_appears_free_in_term X t ->
      not_tyvar_appears_bounded_in_context X Gamma ) ->
  ( forall X,
      tyvar_appears_free_in_context X Gamma ->
      not_tyvar_appears_bounded_in_term X t ) ->
  <{ Gamma |-- t \in T }> ->
  t --> t' ->
  <{ Gamma |-- t' \in T }>.
Proof.
  intros Gamma t t' T Hvblnr Htvblnr Hbtvu Htvb Htvf1 Htvf2 HT.
  generalize dependent t'.
  induction HT;
  intros t' HSt; inversion HSt;
  inversion Hvblnr; inversion Htvblnr; inversion Hbtvu;
  subst.
  - inversion HT1. subst.
    apply var_subst_preserves_typing with (U:=T2); try assumption.
    * intros y Hfy Hby. apply H5 in Hfy.
      apply Hfy. destruct (y=?x0)%string eqn: Eqy.
      { apply eqb_eq in Eqy. subst y. constructor. }
      { rewrite eqb_sym in Eqy. apply eqb_neq in Eqy. constructor;
        assumption. }
  - apply T_App with T2; try assumption. 
    IH_solve_2 IHHT1 Htvb tvabt_app1 Htvf1 tvaft_app1 Htvf2.
  - apply T_App with T2; try assumption.
    IH_solve_2 IHHT2 Htvb tvabt_app2 Htvf1 tvaft_app2 Htvf2.
  - eapply T_TApp.  
    * reflexivity.
    * IH_solve_2 IHHT Htvb tvabt_tyapp1 Htvf1 tvaft_tyapp1 Htvf2.
  - inversion HT. subst.
    apply tysubst_preserves_typing with Gamma.
    + apply Htvb. constructor. apply tvabt_tyabs_bound.
    + inversion H11. assumption.
    + intros. split.
      * apply H8 in H. rewrite nottvabt_ntvabt_iff in H.
        inversion H. assumption.
      * apply Htvf1. apply tvaft_tyapp2. assumption.
    + assumption.
    + assert (HG: not_tyvar_appears_free_in_context X0 Gamma).
      { apply nottvafc_ntvafc_iff. intros H. apply Htvf2 in H.
        apply nottvabt_ntvabt_iff in H. apply H. apply tvabt_tyapp1.
        apply tvabt_tyabs_bound. }
      apply ntvaf_subst_eq_context. assumption.
Qed.