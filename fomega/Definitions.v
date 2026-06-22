From Stdlib Require Import Nat List FunctionalExtensionality.
From Fomega Require Export Maps syntax.

Declare Scope fomega_scope.
Open Scope fomega_scope.
Notation "n =? m" := (Nat.eqb n m) : fomega_scope.

Declare Custom Entry fomega_ki.
Declare Custom Entry fomega_ty.
Declare Custom Entry fomega_tm.
Declare Custom Entry fomega_tysubst.
Declare Custom Entry fomega_tmsubst.

(* Kinds (カインド) *)
Notation "<{| K |}>" := K (K custom fomega_ki at level 99) : fomega_scope.

Notation "x" := x (in custom fomega_ki at level 0, x constr at level 0) : fomega_scope.
Notation "( K )" := K (in custom fomega_ki at level 0, K custom fomega_ki at level 99) : fomega_scope.
Notation "{ K }" := K (in custom fomega_ki at level 0, K constr at level 99, only parsing) : fomega_scope.
Notation "*" := KiStar (in custom fomega_ki at level 0) : fomega_scope.
Notation "K1 '~>' K2" := (KiArr K1 K2) (in custom fomega_ki at level 50, right associativity) : fomega_scope.

(* Types (型) *)
Notation "<{{ T }}>" := T (T custom fomega_ty at level 99) : fomega_scope.

Notation "x" := x (in custom fomega_ty at level 0, x constr at level 0) : fomega_scope.
Notation "( T )" := T (in custom fomega_ty at level 0, T custom fomega_ty at level 99) : fomega_scope.
Notation "{ T }" := T (in custom fomega_ty at level 0, T constr at level 99, only parsing) : fomega_scope.
Notation "\:: K ',' T" := (TyAbs K T) (in custom fomega_ty at level 90, K custom fomega_ki at level 99, T custom fomega_ty at level 99) : fomega_scope.
Notation "T1 T2" := (TyApp T1 T2) (in custom fomega_ty at level 11, left associativity) : fomega_scope.
Notation "T1 -> T2" := (TyFun T1 T2) (in custom fomega_ty at level 50, right associativity) : fomega_scope.
Notation "-/:: K ',' T" := (TyForall K T) (in custom fomega_ty at level 90, K custom fomega_ki at level 99, T custom fomega_ty at level 99) : fomega_scope.
Notation "'Unit'" := TyUnit (in custom fomega_ty at level 0) : fomega_scope.

(* Terms (項) *)
Notation "<{ t }>" := t (t custom fomega_tm at level 99) : fomega_scope.

Notation "x" := x (in custom fomega_tm at level 0, x constr at level 0) : fomega_scope.
Notation "( t )" := t (in custom fomega_tm at level 0, t custom fomega_tm at level 99) : fomega_scope.
Notation "{ t }" := t (in custom fomega_tm at level 0, t constr at level 99, only parsing) : fomega_scope.
Notation "\: T ',' t" := (TmAbs T t) (in custom fomega_tm at level 90, T custom fomega_ty at level 99, t custom fomega_tm at level 90) : fomega_scope.
Notation "t1 t2" := (TmApp t1 t2) (in custom fomega_tm at level 11, left associativity) : fomega_scope.
Notation "t [ T ]" := (TmTApp t T) (in custom fomega_tm at level 11, left associativity, T custom fomega_ty at level 0) : fomega_scope.
Notation "\:: K ',' t" := (TmTAbs K t) (in custom fomega_tm at level 90, K custom fomega_ki at level 99, t custom fomega_tm at level 90) : fomega_scope.
Notation "'unit'" := TmUnit (in custom fomega_tm at level 0) : fomega_scope.

Coercion TyVar : nat >-> Ty.
Coercion TmVar : nat >-> Tm.

Definition sigma_tm_empty : nat -> Tm := fun n => TmVar n.
Definition sigma_tm_one (x: nat) (s: Tm) : nat -> Tm :=
  fun n => if n=?x then s else TmVar n.
Definition sigma_ty_empty : nat -> Ty := fun n => TyVar n.
Definition sigma_ty_one (X: nat) (S: Ty) : nat -> Ty :=
  fun n => if n=?X then S else n.

Notation "'(' x '\->' s ')'" := (sigma_tm_one x s) (in custom fomega_tmsubst).
Notation "'(' X '\->' S ')'" := (sigma_ty_one X S) (in custom fomega_tysubst).
Notation "'[[' X ':=' S ']]' T" := (subst_Ty (sigma_ty_one X S) T)
    (in custom fomega_ty at level 5, T custom fomega_ty at next level, right associativity).
Notation "'[' x ':=' s ']' t" := (subst_Tm sigma_ty_empty (sigma_tm_one x s) t)
    (in custom fomega_tm at level 10, t custom fomega_tm at next level, right associativity).
Notation "'[[' X ':=' S ']]' t" := (subst_Tm (sigma_ty_one X S) sigma_tm_empty t)
    (in custom fomega_tm at level 5, t custom fomega_tm at next level, right associativity).

Definition shift_Tm_Tm t := ren_Tm id S t.
Definition shift_Ty_Tm t := ren_Tm S id t.
Definition shift_Ty T := ren_Ty S T.

Reserved Notation "t '-->' t'" (at level 40).

Inductive value : Tm -> Prop :=
  | v_abs : forall T t1,
      value <{\:T, t1}>
  | v_tyabs : forall K t1,
      value <{\::K , t1}>
  | v_unit :
      value <{unit}>
.

Definition tm_tm_betared t v := 
  ren_Tm id Nat.pred (
    subst_Tm sigma_ty_empty (sigma_tm_one 0 (ren_Tm id S v)) t
  ).

Definition tm_ty_betared t T :=
  ren_Tm Nat.pred id (
    subst_Tm (sigma_ty_one 0 (ren_Ty S T)) sigma_tm_empty t
  ).

Inductive step : Tm -> Tm -> Prop :=
  | ST_AppAbs : forall T t v,
         value v ->
         <{(\:T, t) v}> --> tm_tm_betared t v
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_TAppAbs : forall K t1 T,
      <{(\::K, t1) [T]}> --> tm_ty_betared t1 T
  | ST_TApp : forall t1 t1' T,
         t1 --> t1' ->
         <{t1[T]}> --> <{t1'[T]}>

where "t '-->' t'" := (step t t').

Definition tm_context := list Ty.
Definition ty_context := list Ki.

Reserved Notation "<{{ Delta '|--' T '\in' K }}>" (at level 0, Delta at level 99, T custom fomega_ty, K custom fomega_ki).

Inductive has_kind : ty_context -> Ty -> Ki -> Prop :=
  | K_TVar : forall Delta X K1,
      nth_error Delta X = Some K1 ->
      <{{ Delta |-- X \in K1 }}>
  | K_Abs : forall Delta T1 K1 K2,
      <{{ K1 :: Delta |-- T1 \in K2 }}> ->
      <{{ Delta |-- \::K1, T1 \in K1 ~> K2 }}>
  | K_App : forall Delta T1 T2 K1 K2,
      <{{ Delta |-- T1 \in K2 ~> K1 }}> ->
      <{{ Delta |-- T2 \in K2 }}> ->
      <{{ Delta |-- T1 T2 \in K1 }}>
  | K_Arr : forall Delta T1 T2,
      <{{ Delta |-- T1 \in * }}> ->
      <{{ Delta |-- T2 \in * }}> ->
      <{{ Delta |-- T1 -> T2 \in * }}>
  | K_All : forall Delta T1 K1,
      <{{ K1 :: Delta |-- T1 \in * }}> ->
      <{{ Delta |-- -/::K1, T1 \in * }}>
  | K_Unit : forall Delta,
      <{{ Delta |-- Unit \in * }}>
where "<{{ Delta '|--' T '\in' K }}>" := (has_kind Delta T K) : fomega_scope.

Reserved Notation "<{{= T1 = T2 =}}>" (at level 0, T1 custom fomega_ty, T2 custom fomega_ty).

Inductive type_eq : Ty -> Ty -> Prop :=
  | TQ_Refl : forall T1,
      <{{= T1 = T1 =}}>
  | TQ_Sym : forall T1 T2,
      <{{= T1 = T2 =}}> ->
      <{{= T2 = T1 =}}>
  | TQ_Trans : forall T1 T2 T3,
      <{{= T1 = T2 =}}> ->
      <{{= T2 = T3 =}}> ->
      <{{= T1 = T3 =}}>
  | TQ_Abs : forall T1 T2 K1,
      <{{= T1 = T2 =}}> ->
      <{{= \::K1, T1 = \::K1, T2 =}}>
  | TQ_App : forall T1 T2 S1 S2,
      <{{= T1 = S1 =}}> ->
      <{{= T2 = S2 =}}> ->
      <{{= T1 T2 = S1 S2 =}}>
  | TQ_Arr : forall T1 T2 S1 S2,
      <{{= T1 = S1 =}}> ->
      <{{= T2 = S2 =}}> ->
      <{{= T1 -> T2 = S1 -> S2 =}}>
  | TQ_All : forall T1 T2 K1,
      <{{= T1 = T2 =}}> ->
      <{{= -/::K1, T1 = -/::K1, T2 =}}>
  | TQ_Unit :
      <{{= Unit = Unit =}}>
where "<{{= T1 = T2 =}}>" := (type_eq T1 T2) : fomega_scope.

Reserved Notation "<{ Delta '|' Gamma '|--' t '\in' T }>" (at level 0, Delta at level 99, Gamma at level 99, t custom fomega_tm, T custom fomega_ty).

Definition ty_ty_betared T1 T2 :=
  ren_Ty Nat.pred (
    subst_Ty (sigma_ty_one 0 (ren_Ty S T2)) T1
  ).

Inductive has_type : ty_context -> tm_context -> Tm -> Ty -> Prop :=
  | T_Var : forall Delta Gamma x T1,
      nth_error Gamma x = Some T1 ->
      <{ Delta | Gamma |-- x \in T1 }>
  | T_Abs : forall Delta Gamma T1 T2 t1,
      <{{ Delta |-- T1 \in * }}> ->
      <{ Delta | T1 :: Gamma |-- t1 \in T2 }> ->
      <{ Delta | Gamma |-- \:T1, t1 \in T1 -> T2 }>
  | T_App : forall Delta Gamma t1 t2 T1 T2,
      <{ Delta | Gamma |-- t1 \in T1 -> T2 }> ->
      <{ Delta | Gamma |-- t2 \in T1 }> ->
      <{ Delta | Gamma |-- t1 t2 \in T2 }>
  | T_TAbs : forall Delta Gamma GammaS t1 K T1,
      <{ K :: Delta | GammaS |-- t1 \in T1 }> ->
      GammaS = map (ren_Ty S) Gamma ->
      <{ Delta | Gamma |-- \::K, t1 \in -/::K, T1 }>
  | T_TApp : forall Delta Gamma t1 K T1 S T1', 
      <{ Delta | Gamma |-- t1 \in -/::K, T1 }> ->
      T1' = ty_ty_betared T1 S ->
      <{{ Delta |-- S \in K }}> ->
      <{ Delta | Gamma |-- t1 [S] \in T1' }>
  | T_Conv : forall Delta Gamma t T1 T2,
      <{ Delta | Gamma |-- t \in T1 }> ->
      <{{= T1 = T2 =}}> ->
      <{ Delta | Gamma |-- t \in T2 }>
  | T_Unit : forall Delta Gamma,
      <{ Delta | Gamma |-- unit \in Unit }>

where "<{ Delta '|' Gamma '|--' t '\in' T }>" := (has_type Delta Gamma t T) : fomega_scope.

Ltac aunfold := unfold core.funcomp, unscoped.scons, unscoped.shift, unscoped.id.
Ltac asolve := simpl; asimpl; aunfold; simpl; try auto.
Ltac dauto := try (intros _x; destruct _x; auto).