From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Nat.

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
Notation "'-/', T" := (TyForall T) (in custom plc_ty at level 90, T custom plc_ty at level 90) : plc_scope.
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
Notation "'(' X '\->' S ')'" := (sigma_tm_one X S) (in custom plc_tmsubst).

Notation "'[' X ':=' S ']' T" := (subst_ty (sigma_tm_one X S) T)
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

Fixpoint eval_tm (t: tm) : option tm :=
  match t with
  | <{ t1 t2 }> =>
      match t1, t2 with
      | TmVal <{ \:T, t11' }>, TmVal v2 => return <{ [[0:=v2]] t11' }>
      | TmVal <{ \:T, t11' }>, t2 =>
          t2' <- eval_tm t2 ;;
          return <{ t1 t2' }>
      | TmVal _, t2 => fail
      | t1, t2 => 
          t1' <- eval_tm t1 ;;
          return <{ t1' t2 }>
      end
  | <{ t1 [T] }> =>
      match t1 with 
      | TmVal <{ \\, t11' }> => return <{ [0:=T] t11' }>
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