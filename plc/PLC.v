From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import FunctionalExtensionality.

From PLC Require Import Maps.

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

Check <{ \\ X , unit }>.
(* Check <{{ (Bool -> Bool) -> Bool }}>. *)

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

(* Examples *)
  Example step_appabs_example :
    <{ (\x:Unit, x) unit }> --> <{ unit }>.
  Proof.
    apply ST_AppAbs.
    constructor.
  Qed.

  Example step_app1_example :
    <{ ((\x:Unit, x) unit) unit }> --> <{ (unit) unit }>.
  Proof.
    apply ST_App1.
    apply ST_AppAbs.
    constructor.
  Qed.

  Example step_app2_example :
    <{ (\x:Unit, x) ((\x:Unit, x) unit) }> --> <{ (\x:Unit, x) unit }>.
  Proof.
    apply ST_App2.
    - constructor.
    - apply ST_AppAbs.
      constructor.
  Qed.

  Example step_tappabs_example :
    <{ (\\X, \x: X, x) [Unit] unit }> -->* <{ unit }>.
  Proof.
    eapply multi_step.
    - apply ST_App1. apply ST_TAppAbs.
    - simpl. eapply multi_step.
      + apply ST_AppAbs. constructor.
      + simpl. apply multi_refl. 
  Qed.

  Example step_tapp_example :
    <{ ((\\X, unit) [Unit]) [Unit] }> --> <{ (unit) [Unit] }>.
  Proof.
    apply ST_TApp.
    apply ST_TAppAbs.
  Qed.

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

Lemma weakening_empty : forall Gamma t T,
     <{ empty |-- t \in T }> ->
     <{ Gamma |-- t \in T }>.
Proof.
  intros Gamma t T.
  eapply weakening.
  unfold includedin. intros. discriminate.
Qed.

Lemma type_preservation_subst: forall Gamma x s S t T,
  <{ x |-> S; Gamma |-- t \in T }> ->
  <{ empty |-- s \in S }> ->
  <{ Gamma |-- [x:=s] t \in T }>.
Proof.
  intros Gamma x s S t T Ht Hs.
  remember (x |-> S; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; simpl; intros; subst.
  - unfold update in H. unfold t_update in H.
    destruct (x=?x0)%string eqn: Eqx.
    + inversion H. subst. apply weakening_empty.
      assumption.
    + apply T_Var. apply H.
  - destruct (x=?x0)%string eqn: Eqx.
    + apply T_Abs.
      apply weakening with (Gamma:=x0 |-> T2; x |-> S; Gamma0).
      * unfold includedin. intros.
        apply eqb_eq in Eqx. subst x.
        rewrite <- update_shadow with (v1:=S). apply H.
      * apply Ht.
    + apply T_Abs. apply IHHt.
      apply update_permute. apply eqb_neq. apply Eqx.
  - eapply T_App.
    * apply IHHt1. reflexivity.
    * apply IHHt2. reflexivity.
  - apply T_TAbs. apply IHHt. reflexivity.
  - apply T_TApp with (X:=X0) (T1:=T1).
    * reflexivity.
    * apply IHHt. reflexivity.
  - apply T_Unit.
Qed.

Definition context_ty_subst X S (Gamma: context) : context :=
    fun x =>
      match Gamma x with
      | Some T => Some (<{{[X:=S] T}}>)
      | None => None
      end.

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

Definition closed T :=
  forall X, not_tyvar_appears_free_in_ty X T.

Lemma ntvaf_subst_ty : forall X S T,
  not_tyvar_appears_free_in_ty X T ->
  T = <{{ [X:=S] T }}>.
Proof.
  intros. induction H; simpl;
  try rewrite eqb_refl;
  try (apply eqb_neq in H; rewrite H);
  try reflexivity.
  - rewrite <- IHnot_tyvar_appears_free_in_ty1.
    rewrite <- IHnot_tyvar_appears_free_in_ty2.
    reflexivity.
  - rewrite <- IHnot_tyvar_appears_free_in_ty. reflexivity.
Qed.

Lemma update_subst_context : forall x X S T Gamma,
  context_ty_subst X S <{ x |-> T; Gamma }> =
  <{ x |-> <{{[X:=S]T}}> ; (context_ty_subst X S Gamma) }> .
Proof.
  intros. apply functional_extensionality.
  intro y. unfold context_ty_subst, update, t_update.
  destruct (x0 =? y)%string; reflexivity.
Qed.

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

Definition not_tyvar_appears_bounded_in_context (X: string) (Gamma: context) :=
  forall x T, Gamma x = Some T -> not_tyvar_appears_bounded_in_ty X T .

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
    + rewrite EqX. apply ntvaf_subst_ty. apply H2.
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

Lemma type_preservation_tysubst : forall Gamma Gamma' X S t T,
  <{ Gamma |-- t \in T }> ->
  not_tyvar_appears_bounded_in_context X Gamma ->
  not_tyvar_appears_bounded_in_term X t ->
  closed S ->
  Gamma' = context_ty_subst X S Gamma ->
  <{ Gamma' |-- [[X:=S]]t \in [X:=S]T }>.
Proof.
  intros Gamma Gamma' X S t T H.
  generalize dependent Gamma'.
  induction H; simpl; intros; subst.
  - apply T_Var. unfold context_ty_subst in *.
    destruct (Gamma x0).
    + f_equal. injection H as H'. rewrite H'. reflexivity.
    + discriminate.
  - apply T_Abs. rewrite <- update_subst_context.
    apply IHhas_type.
    + unfold not_tyvar_appears_bounded_in_context.
      unfold update, t_update. intros y T subH.
      destruct (x0 =? y)%string.
      * inversion subH. inversion H1. subst. assumption.
      * unfold not_tyvar_appears_bounded_in_context in H0.
        apply H0 with y. assumption.
    + inversion H1. assumption.
    + assumption. 
    + reflexivity.
  - eapply T_App.
    + apply IHhas_type1;
      try reflexivity; inversion H2; assumption.
    + apply IHhas_type2;
      try reflexivity; inversion H2; assumption.
  - inversion H1. apply eqb_neq in H5. rewrite H5. apply T_TAbs.
    apply IHhas_type; try reflexivity; assumption.
  - inversion H2.
    apply ntvab_typing with (X:=X) in H0; try assumption.
    inversion H0. 
    apply T_TApp with (X:=X0) (T1:=<{{[X:=S]T1}}>).
    + apply ty_subst_distribution; try assumption.
      * apply H3. 
    + apply eqb_neq in H9. 
      simpl in IHhas_type. rewrite H9 in IHhas_type. 
      apply IHhas_type;
      try reflexivity; inversion H2; assumption.
    - apply T_Unit.
Qed.

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

Inductive applied_type_is_closed : tm -> Prop :=
  | atic_var : forall x,
      applied_type_is_closed (TmVar x)
  | atic_abs : forall x T t,
      applied_type_is_closed t ->
      applied_type_is_closed (TmAbs x T t)
  | atic_app : forall t1 t2,
      applied_type_is_closed t1 ->
      applied_type_is_closed t2 ->
      applied_type_is_closed (TmApp t1 t2)
  | atic_tyabs : forall X t,
      applied_type_is_closed t ->
      applied_type_is_closed (TmTyAbs X t)
  | atic_tyapp : forall t T,
      applied_type_is_closed t ->
      closed T ->
      applied_type_is_closed (TmTyApp t T)
  | atic_unit :
      applied_type_is_closed TmUnit
.

Theorem type_preservation: forall t t' T,
  bounded_tyvar_unique t ->
  applied_type_is_closed t ->
  <{ empty |-- t \in T }> ->
  t --> t' ->
  <{ empty |-- t' \in T }>.
Proof.
  intros t t' T Hbounded Hclosed HT.
  generalize dependent t'.
  remember empty as Gamma.
  induction HT;
  intros t' HSt; inversion HSt; subst.
  - inversion HT1. subst.
    apply type_preservation_subst with (S:=T2).
    * apply H1.
    * apply HT2.
  - apply T_App with T2; try assumption.
    inversion Hbounded. inversion Hclosed.
    apply IHHT1; try reflexivity; assumption.
  - apply T_App with T2; try assumption.
    inversion Hbounded. inversion Hclosed.
    apply IHHT2; try reflexivity; assumption.
  - eapply T_TApp.  
    * reflexivity.
    * inversion Hbounded. inversion Hclosed.
    apply IHHT; try reflexivity; assumption.
  - inversion HT.
    apply type_preservation_tysubst with empty.
    + assumption.
    + unfold not_tyvar_appears_bounded_in_context.
      intros. discriminate.
    + inversion Hbounded. inversion H6. subst. assumption.
    + inversion Hclosed. assumption.
    + apply functional_extensionality.
      unfold context_ty_subst. reflexivity.
Qed.
 
