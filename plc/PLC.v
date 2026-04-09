From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.

From PLC Require Import Maps.

(** * Polymorphic lambda calculus *)

(** ** Syntax *)

(** *** Types *)

(**
<<
t ::= t -> t     (* Function *)
    | forall t   (* Type generalization *)
    | i          (* Type variable (DeBruijn index) *)
    | unit       (* Unit type *)
    | t * t      (* Product *)
    | t + t      (* Sum *)
>>
  *)
Fixpoint bnat (n : nat) : Type :=
  match n with
  | O => Empty_set
  | S n => option (bnat n)
  end.

(* Inductive ty (n : nat) : Type :=
| Tyvar : bnat n -> ty n
| Arrow : ty n -> ty n -> ty n
| Forall : ty (S n) -> ty n
| Unit : ty n
. *)

(* Arguments Arrow  {n}.
Arguments Forall {n}.
Arguments Tyvar  {n}.
Arguments Unit   {n}. *)

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

Hint Constructors has_type : core.

Example has_type_abs_example :
  <{ empty |-- \x:Unit, x \in Unit -> Unit }>.
Proof.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.

Example has_type_app_example :
  <{ empty |-- (\x:Unit, x) unit \in Unit }>.
Proof.
  eapply T_App.
  - apply has_type_abs_example.
  - apply T_Unit.
Qed.

Example typing_example_1 :
  <{ empty |-- \x:Unit, x \in Unit -> Unit }>.
Proof.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.

Example typing_example_2 :
  <{ empty |-- \\X, \x:X, x \in -/X, X -> X }>.
Proof.
  apply T_TAbs.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.

Example typing_example_3 :
  <{ empty |-- (\\X, \x:X, x) [Unit] \in Unit -> Unit }>.
Proof.
  eapply T_TApp.
  2: (apply T_TAbs; apply T_Abs; apply T_Var; reflexivity).
  reflexivity.
Qed.

(* Props *)
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

Lemma type_preservation_subst: forall Gamma x s S t T,
  <{ x |-> S; Gamma |-- t \in T }> ->
  <{ Gamma |-- s \in S }> ->
  <{ Gamma |-- [x:=s] t \in T }>.
Proof.
  intros Gamma x s S t T Ht Hs.
  remember (x |-> S; Gamma) as Gamma'.
  induction Ht; simpl; subst.
  - unfold update in H. unfold t_update in H.
    destruct (x=?x0)%string eqn: Eqx.
    + inversion H. subst. assumption.
    + apply T_Var. apply H.
  - destruct (x=?x0)%string eqn: Eqx.
    (* + apply  *)
Admitted.

Lemma type_preservation_tysubst: forall Gamma X S t T,
  <{ Gamma |-- t \in T }> ->
  <{ Gamma |-- [[X:=S]]t \in [X:=S]T }>.
Proof.
  intros Gamma X S t T H.
  induction H; simpl.
  - simpl.
Admitted.


Theorem type_preservation: forall Gamma t t' T,
  <{ Gamma |-- t \in T }> ->
  t --> t' ->
  <{ Gamma |-- t' \in T }>.
Proof.
  intros Gamma t t' T HT.
  generalize dependent t'.
  induction HT;
  intros t' HSt; inversion HSt; subst.
  - inversion HT1. admit.
  - apply T_App with T2; try assumption.
    apply IHHT1. apply H2.
  - apply T_App with T2; try assumption.
    apply IHHT2. apply H3.
  - eapply T_TApp.  
    * reflexivity.
    * apply IHHT. assumption.
  - admit.
Admitted.
 
