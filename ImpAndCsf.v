(** * Import modules and define nottions *)
Set Warnings "-notation-overridden".
Set Warnings "-stdlib-vector".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.
From Stdlib Require Fin.
From Stdlib Require Vector.
From Stdlib Require Import Logic.ProofIrrelevance.
From Equations Require Import Equations.

Local Notation "[ ]" := (Vector.nil _) (format "[ ]").
Local Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity).
Local Notation "[ x ; .. ; y ]" := 
    (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).

Local Notation "v [@ p ]" := (Vector.nth v p) (at level 1).
Local Notation "<\ H />" := (Fin.of_nat_lt H) (at level 1).

Axiom functional_extensionality : 
  forall {X Y: Type} (f g: X -> Y), (forall args, f args = g args) -> f = g.

(** * Define Constant Step Functions (CSF) *)
Inductive csf : nat -> Type :=
  | Zero : csf 0
  | Succ : csf 1
  | Proj (n i: nat) (H: i < n) : csf n
  | Comp (m n: nat) (f: csf m) (gs: Vector.t (csf n) m) : csf n.

(** * Define evaluation of CSF *)
Definition lt01 : 0 < 1.
Proof. apply le_n. Qed.

Fixpoint csf_eval {argn: nat} (f: csf argn) : Vector.t nat argn -> nat :=
  match f in csf argn' return Vector.t nat argn' -> nat with
  | Zero => fun (args: Vector.t nat 0) => 0
  | Succ => 
      fun (args: Vector.t nat 1) => S (args [@ <\lt01/>])
  | Proj n _ H =>
      fun (args: Vector.t nat n) => args [@ <\H/>]
  | Comp m n f gs =>
      fun (args: Vector.t nat n) =>
        (csf_eval f) (Vector.map (fun f => f args) (Vector.map (csf_eval) gs))
  end.

(** * Define non-loop Imp *)
Inductive ident : Type :=
  | Id (n: nat).

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : ident)
  | ASucc (a1: aexp).

(* Coercion AId : ident >-> aexp. *)
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/  ' '[v' e ']' '/' }> ']'") : com_scope.
Notation "x" := x%nat (in custom com at level 0, x constr at level 0).
Notation "x ++"   := (ASucc x) (in custom com at level 50, right associativity).
Notation "| x |"   := (AId (Id x)) (in custom com at level 85).

Open Scope com_scope.

Definition state := ident -> nat.
Definition empty_st : state := (fun _ =>  0).
Definition st_update (i: ident) (v: nat) (st: state) :=
  match i with
  | Id n =>
    fun i' =>
      match i' with
      | Id n' => if (n' =? n) then v else (st i')
      end
  end.

Notation "x '!->' v ';' st" := (st_update x v st)
  (at level 0, x constr, v at level 200, right associativity).

Notation "x '!->' v" := (st_update x v empty_st) (at level 0, x constr, v at level 200).

Inductive com : Type :=
  | CSkip
  | CAsgn (x : ident) (a : aexp)
  | CSeq (c1 c2 : com).

Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn (Id x) y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.

(** * Define evaluation of non-loop Imp *)
Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x 
  | <{a1 ++}> => S (aeval st a1)
  end.

Fixpoint ceval_st (c: com) (st: state) : state :=
  match c with
  | <{ skip }> => st
  | <{ x := a }> => ((Id x) !-> (aeval st a) ; st)
  | <{ c1; c2 }> => (ceval_st c2) (ceval_st c1 st)
  end.

Fixpoint vec_to_state {n: nat} (m: nat) (v: Vector.t nat n) : state :=
  match n, v with
  | O, _ => empty_st
  | S n', v =>
      let x := Vector.hd v in
      let xs := Vector.tl v in
        ((Id (S(m - n))) !-> x; (vec_to_state m xs))
  end.

Definition ceval (c: com) {argn: nat} (args: Vector.t nat argn) : nat :=
  ((ceval_st c) (vec_to_state argn args)) (Id 0).

Fixpoint shift_com i k n : com :=
  match k with
  | O => <{ skip }>
  | S k' => <{ (i + k' + n) := |(i + k')| ;
              (shift_com i k' n) }>
  end.

(** * Define conversion from CSF to Imp *)
Fixpoint unshift_com i k n : com :=
  match k with
  | O => <{ skip }>
  | S k' => <{ i := |(i + n)| ;
              (unshift_com (S i) k' n) }>
  end.

Fixpoint comvec_to_com (j: nat) {k: nat} (g_coms: Vector.t com k) : com :=
  match g_coms with
  | [] => <{ skip }>
  | (g_com :: g_coms') =>
        <{ g_com; j := |0|; (comvec_to_com (S j) g_coms') }>
  end.

Fixpoint used_state_idx {n: nat} (f: csf n) : nat :=
  match f with
  | Zero => 0
  | Succ => 1
  | Proj n i H => n
  | Comp m n f gs =>
    max (Vector.fold_left max n (Vector.map used_state_idx gs)) (used_state_idx f) +
    m + n
  end.

Fixpoint csf_to_com {argn: nat} (f: csf argn) :=
  match f with
  | Zero => <{ 0 := 0 }>
  | Succ => <{ 0 := |1|++ }>
  | Proj n i H => <{ 0 := |(S i)| }>
  | Comp m n f gs =>
      let u := max (Vector.fold_left max n (Vector.map used_state_idx gs)) (used_state_idx f) in
      let gs' := Vector.map csf_to_com gs in
        <{ (comvec_to_com (S u) gs');
          (shift_com 1 n (u+m));
          (unshift_com 1 m u);
          (csf_to_com f);
          (unshift_com 1 n (u+m)) }>
  end.

(** * Proof of csf_eq_com  *)
(* usefull tactical *)
Ltac neq_rewrite n m :=
  assert (__Neq__: n <> m) by lia;
  rewrite <- Nat.eqb_neq in __Neq__;
  rewrite __Neq__;
  try reflexivity;
  clear __Neq__.

(* Projection *)
Lemma vec_to_state_shift : forall n m i (v: Vector.t nat n),
  n <= m -> (vec_to_state m v) (Id i) = (vec_to_state (S m) v) (Id (S i)).
Proof.
  intros. induction v.
  - reflexivity.
  - simpl. rewrite IHv. 
    + replace (S (m - S n)) with (m - n) by lia. reflexivity.
    + apply le_S_n. apply le_S. apply H.
Qed.

Lemma csf_to_com_is_valid_proj : forall n i H, 
  csf_eval (Proj n i H) = ceval (csf_to_com (Proj n i H)).
Proof.
  intros. apply functional_extensionality. 
  intros. simpl. generalize dependent i. unfold ceval.
  induction n.
  + inversion H.
  + cbn [csf_to_com]. simpl. rewrite sub_diag. intros. induction i.
    * rewrite Nat.eqb_refl. rewrite (Vector.eta args).
      reflexivity.
    * rewrite Nat.eqb_sym. simpl.
      rewrite <- vec_to_state_shift; try auto.
      cbn [csf_to_com] in IHn. simpl in IHn.
      apply le_S_n in H as H_.
      rewrite <- IHn with (H:=H_).
      rewrite (Vector.eta args). simpl.
      rewrite <- (ProofIrrelevance.proof_irrelevance _ H_ _).
      reflexivity.
Qed.

(* Composition *)
(* Strong induction principle *)
Definition Vector_Forall_csf (P : forall n (f: csf n), Prop) {n m} (v : Vector.t (csf n) m) :=
  Vector.fold_right (fun g acc => P n g /\ acc) v True.

Fixpoint csf_ind_strong
  (n : nat) (f : csf n) 
  (P : forall n, csf n -> Prop)
  (H_Zero : P 0 Zero)
  (H_Succ : P 1 Succ)
  (H_Proj : forall n i (H : i < n), P n (Proj n i H))
  (H_Comp : forall m n (f : csf m) (gs : Vector.t (csf n) m),
    P m f ->
    Vector_Forall_csf P gs ->
    P n (Comp m n f gs))
  {struct f} : P n f :=
  match f with
  | Zero => H_Zero
  | Succ => H_Succ
  | Proj n i H => H_Proj n i H
  | Comp m n f' gs =>
      let IH_f' := csf_ind_strong m f' P H_Zero H_Succ H_Proj H_Comp in
      let fix vec_ind {k} (v : Vector.t (csf n) k) : Vector_Forall_csf P v :=
        match v with
        | [] => I
        | h :: t => conj (csf_ind_strong n h P H_Zero H_Succ H_Proj H_Comp) (vec_ind t)
        end
      in
      H_Comp m n f' gs IH_f' (vec_ind gs)
  end.

(* Lemmas on shift/unshift *)
Lemma shift_is_valid_out_of_range: forall st j i k n,
  j < i + n \/ (i + k + n) <= j ->
  ceval_st (shift_com i k n) st (Id j) = st (Id j).
Proof.
  intros.
  generalize dependent i. generalize dependent st. induction k.
  - simpl. reflexivity.
  - intros. cbn [shift_com ceval_st aeval].
    rewrite IHk; try lia. simpl.
    neq_rewrite j (i + k + n).
Qed.

Lemma shift_is_valid_in_range: forall st j i k n,
  i <= j < (i + k) ->
  ceval_st (shift_com i k n) st (Id (j+n)) = st (Id j).
Proof.
  intros.
  generalize dependent i. generalize dependent st. induction k.
  - lia. (* discriminate hypothesis *)
  - intros st i [Hl Hr]. cbn [shift_com ceval_st aeval].
    inversion Hr as [Eqj|ik'].
    + replace (i + k) with j by lia. simpl.
      rewrite shift_is_valid_out_of_range; try lia.
      rewrite Nat.eqb_refl. reflexivity.
    + replace (i + k) with ik' by lia.
      rewrite IHk; try lia.
      simpl. neq_rewrite j (ik' + n).
Qed.

Lemma unshift_is_valid_out_of_range: forall st j i k n,
  j < i \/ (i + k) <= j ->
  ceval_st (unshift_com i k n) st (Id j) = st (Id j).
Proof.
  intros.
  generalize dependent i. generalize dependent st. induction k.
  - simpl. reflexivity.
  - intros. cbn [unshift_com ceval_st aeval].
    rewrite IHk; try lia. simpl.
    neq_rewrite j i.
Qed.

Lemma unshift_is_valid_in_range: forall st j i k n,
  i <= j < (i + k) ->
  ceval_st (unshift_com i k n) st (Id j) = st (Id (j+n)).
Proof.
  intros.
  generalize dependent i. generalize dependent st. induction k.
  - lia. (* discriminate hypothesis *)
  - intros st i [Hl Hr]. cbn [unshift_com ceval_st aeval].
    inversion Hl as [Eqij|j'].
    + rewrite unshift_is_valid_out_of_range; try lia.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + rewrite H0. rewrite IHk; try lia.
      simpl. neq_rewrite (j + n) i.
Qed.

(* Lemmas on Vector.fold_left max i v *)
Lemma vec_fold_max_lemma_1: forall n (v: Vector.t nat n) i u,
  Vector.fold_left max i v <= u -> i <= u.
Proof.
  induction v.
  - auto.
  - simpl. intros. apply IHv in H. lia.
Qed.

Lemma vec_fold_max_lemma_2: forall n (v: Vector.t nat n) i j,
  i <= j ->
  Vector.fold_left max i v <= Vector.fold_left max j v.
Proof.
  induction v; simpl.
  - auto.
  - intros. apply IHv. lia.
Qed.

Lemma vec_fold_max_lemma_3: forall n (v: Vector.t nat n) i j u,
  i <= j ->
  Vector.fold_left max j v <= u ->
  Vector.fold_left max i v <= u.
Proof.
  simpl. intros. specialize (vec_fold_max_lemma_2 n v i j) as H1.
  lia.
Qed.

Lemma vec_fold_max_lemma_4: forall n m (v: Vector.t nat m),
  n <= Vector.fold_left max n v.
Proof.
  induction v.
  - simpl. lia.
  - simpl. specialize (vec_fold_max_lemma_2 _ v n (max n h)) as H.
    lia.
Qed.

(* used_state_idx is valid *)
Definition used_state_idx_prop n (f: csf n) :=
  forall i st,
    (used_state_idx f) < i ->
    ceval_st (csf_to_com f) st (Id i) = st (Id i).

Lemma used_state_idx_is_valid_vec:
  forall n m (gs: Vector.t (csf n) m) i u st,
  Vector_Forall_csf used_state_idx_prop gs -> 
  Vector.fold_left max n (Vector.map used_state_idx gs) <= u ->
  u + m < i ->
  ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st (Id i) = st (Id i).
Proof.
  intros n m gs. induction gs as [|g m' gs'].
  - reflexivity.
  - intros. cbn [Vector.map comvec_to_com ceval_st aeval].
    rewrite IHgs'; try lia.
    + simpl. neq_rewrite i (S u). apply H.
      assert (used_state_idx g <= u).
      { simpl in H0.
        apply vec_fold_max_lemma_1 with (v:=(Vector.map used_state_idx gs')).
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx g))); lia. }
      lia.
    + apply H.
    + simpl in H0.
      apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx g))); lia.
Qed.

Lemma used_state_idx_is_valid: forall n (f: csf n),
  used_state_idx_prop n f.
Proof.
  intros n f. apply (csf_ind_strong n f); clear n f;
  unfold used_state_idx_prop; simpl.
  - intros. neq_rewrite i 0.
  - intros. neq_rewrite i 0.
  - intros. neq_rewrite i0 0.
  - intros * * * * IHf IHgs * * Hi.
    remember (max (Vector.fold_left max n (Vector.map used_state_idx gs)) (used_state_idx f)) as u.
    rewrite unshift_is_valid_out_of_range; try lia.
    rewrite IHf; try lia.
    rewrite unshift_is_valid_out_of_range; try lia.
    rewrite shift_is_valid_out_of_range; try lia.
    apply used_state_idx_is_valid_vec; try lia.
    apply IHgs.
Qed.

(* Command (csf_to_com f) does not change arguments in state *)
Definition csf_com_does_not_change_args_prop n (f: csf n) :=
  forall i st,
    0 < i <= n ->
    ceval_st (csf_to_com f) st (Id i) = st (Id i).

Lemma csf_com_does_not_change_args_vec:
  forall n m (gs: Vector.t (csf n) m) i u st,
  Vector_Forall_csf csf_com_does_not_change_args_prop gs -> 
  0 < i <= n ->
  n <= u ->
  m <= u ->
  ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st (Id i) = st (Id i).
Proof.
  intros n m gs. induction gs; intros.
  - simpl. reflexivity.
  - cbn [Vector.map comvec_to_com ceval_st aeval].
    rewrite IHgs.
    + simpl. neq_rewrite i (S u). apply H. apply H0.
    + apply H.
    + apply H0.
    + lia.
    + lia.
Qed.

Lemma argn_is_le_used_state_idx: forall n (f: csf n),
  n <= used_state_idx f.
Proof.
  induction f; simpl; lia.
Qed.

Lemma csf_com_does_not_change_args: forall n f,
  csf_com_does_not_change_args_prop n f.
Proof.
  intros n f. unfold csf_com_does_not_change_args_prop.
  apply (csf_ind_strong n f); clear n f.
  - lia. (* discriminate hypothesis *)
  - simpl. intros. neq_rewrite i 0.
  - simpl. intros. neq_rewrite i0 0.
  - intros * * * * IHf IHgs * * Hi. simpl.
    remember (max (Vector.fold_left max 0 (Vector.map used_state_idx gs)) (used_state_idx f)) as u.
    rewrite unshift_is_valid_in_range; try lia.
    rewrite used_state_idx_is_valid; try lia.
    rewrite unshift_is_valid_out_of_range; try lia.
    rewrite shift_is_valid_in_range; try lia.
    apply csf_com_does_not_change_args_vec.
    + apply IHgs.
    + apply Hi.
    + assert (Hn: n <= (Vector.fold_left max n (Vector.map used_state_idx gs))).
      { apply vec_fold_max_lemma_4. }
      lia.
    + assert (Hm: m <= (used_state_idx f)).
      { apply argn_is_le_used_state_idx. }
      lia.
Qed.

(* (comvec_to_com (S u) v) does not change states[i] when max used_state_idx < i <= u *)
Lemma comvec_does_not_change_state:
  forall n m (gs: Vector.t (csf n) m) i u st,
    Vector.fold_left max n (Vector.map used_state_idx gs) < i ->
    i <= u ->
    ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st (Id i) = st (Id i).
Proof.
  induction gs.
  - intros. reflexivity.
  - cbn [Vector.map Vector.fold_left comvec_to_com ceval_st aeval].
    intros. rewrite IHgs.
    + simpl. neq_rewrite i (S u). apply used_state_idx_is_valid.
      destruct i.
      * inversion H.
      * apply le_n_S. apply le_S_n in H.
        apply vec_fold_max_lemma_1 in H. lia.
    + destruct i.
      * inversion H.
      * apply le_n_S. apply le_S_n in H.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
    + lia.
Qed.

(* The result of (csf_to_com f) does not change when the arguments are the same *)
Definition csf_com_eq_with_same_arg_prop n (f: csf n) :=
  forall st st', 
    (forall i, 1 <= i <= n -> st (Id i) = st' (Id i)) ->
    ceval_st (csf_to_com f) st (Id 0) = ceval_st (csf_to_com f) st' (Id 0).

Lemma csf_com_eq_with_same_arg_vec:
  forall n m (gs: Vector.t (csf n) m) i u st st',
    Vector_Forall_csf csf_com_eq_with_same_arg_prop gs ->
    (forall i, 1 <= i <= n -> st (Id i) = st' (Id i)) ->
    1 <= i <= m ->
    Vector.fold_left max n (Vector.map used_state_idx gs) <= u ->
    ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st (Id (i + u)) =
    ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st' (Id (i + u)).
Proof.
  induction gs; intros.
  - lia.
  - cbn [Vector.map comvec_to_com ceval_st aeval].
    destruct H1. inversion H1 as [|i'].
    + repeat (rewrite comvec_does_not_change_state; try lia).
      * simpl. repeat (rewrite Nat.eqb_refl). apply H.
        apply H0.
      * apply le_n_S. simpl in H2.
        apply vec_fold_max_lemma_3 with (j:=max n (used_state_idx h)); lia.
      * apply le_n_S. simpl in H2.
        apply vec_fold_max_lemma_3 with (j:=max n (used_state_idx h)); lia.
    + replace (S i' + u) with (i' + S u) by lia. apply IHgs.
      * apply H.
      * intros j Hj. simpl. apply vec_fold_max_lemma_1 in H2.
        neq_rewrite j (S u).
        repeat (rewrite csf_com_does_not_change_args; try lia).
        apply H0. lia.
      * lia.
      * simpl in H2.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
Qed.

Lemma csf_com_eq_with_same_arg: forall n (f: csf n),
  csf_com_eq_with_same_arg_prop n f.
Proof.
  intros n f. apply csf_ind_strong; clear n f;
  unfold csf_com_eq_with_same_arg_prop.
  - reflexivity.
  - intros. simpl. f_equal. apply H. lia.
  - intros. simpl. apply H0. lia.
  - intros * * * * IHf IHgs * * H. 
    cbn [csf_to_com ceval_st]. 
    remember (max (Vector.fold_left max n (Vector.map used_state_idx gs)) (used_state_idx f)) as u.
    repeat (rewrite unshift_is_valid_out_of_range; try lia).
    apply IHf. intros i [Hil Hir].
    repeat (rewrite unshift_is_valid_in_range; try lia).
    repeat (rewrite shift_is_valid_out_of_range; try lia).
    apply csf_com_eq_with_same_arg_vec; try lia; try assumption.
Qed.

Lemma csfvec_com_eq_with_same_arg: forall n m (gs: Vector.t (csf n) m) i u st st',
  (forall j, 1 <= j <= n -> st (Id j) = st' (Id j)) ->
  Vector.fold_left max n (Vector.map used_state_idx gs) <= u ->
  u < i <= u + m ->
  ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st (Id i) =
  ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs)) st' (Id i).
Proof.
  induction gs.
  - simpl. lia.
  - intros * * * * H Hu [Hil Hir].
    cbn [Vector.map comvec_to_com ceval_st aeval].
    inversion Hil as [|i'].
    + repeat (rewrite comvec_does_not_change_state; try lia).
      * simpl. rewrite Nat.eqb_refl.
        apply csf_com_eq_with_same_arg. apply H.
      * simpl in Hu. apply le_n_S.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
      * simpl in Hu. apply le_n_S.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
    + apply IHgs; try lia.
      * intros. simpl. simpl in Hu.
        apply vec_fold_max_lemma_1 in Hu.
        neq_rewrite j (S u).
        repeat (rewrite csf_com_does_not_change_args; try lia).
        apply H. lia.
      * simpl in Hu.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
Qed.

(* Prove csf_to_com is valid *)
Definition csf_to_com_is_valid_prop (n: nat) (f: csf n) :=
  csf_eval f = ceval (csf_to_com f).

Lemma comvec_to_com_is_valid: forall m n (gs: Vector.t (csf n) m) args i u ,
  1 <= i <= m ->
  Vector.fold_left max n (Vector.map used_state_idx gs) <= u ->
  Vector_Forall_csf csf_to_com_is_valid_prop gs ->
  vec_to_state m (Vector.map (fun g' : Vector.t nat n -> nat => g' args)
    (Vector.map csf_eval gs)) (Id i) =
  ceval_st (comvec_to_com (S u) (Vector.map csf_to_com gs))
    (vec_to_state n args) (Id (i + u)).
Proof.
  induction gs.
  - intros. lia.
  - intros.
    cbn [Vector.map vec_to_state comvec_to_com ceval_st aeval].
    cbv [Vector.hd Vector.tl Vector.caseS].
    rewrite sub_diag. simpl.
    destruct H as [Hil Hir]. inversion Hil as [|i'].
    + simpl. rewrite comvec_does_not_change_state.
      * rewrite Nat.eqb_refl. unfold Vector_Forall_csf in H1.
        simpl in H1. destruct H1 as [H1 _].
        apply (f_equal (fun f => f args)) in H1.
        rewrite H1. reflexivity.
      * simpl in H0. apply le_n_S.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
      * lia.
    + neq_rewrite (S i') 1. rewrite <- vec_to_state_shift; try lia.
      simpl. rewrite IHgs with (u:=(S u)); try lia.
      * replace (i' + S u) with (S (i' + u)) by lia.
        apply csfvec_com_eq_with_same_arg; try lia.
        { intros. simpl in H0. apply vec_fold_max_lemma_1 in H0.
          neq_rewrite j (S u). symmetry.
          apply csf_com_does_not_change_args. lia. }
        { simpl in H0. 
          apply vec_fold_max_lemma_3 with (j:=max n (used_state_idx h)); lia. }
      * simpl in H0. 
        apply vec_fold_max_lemma_3 with (j:=max n (used_state_idx h)); lia.
      * apply H1.
Qed.
  
Lemma csf_to_com_is_valid: forall (n: nat) (f: csf n),
  csf_to_com_is_valid_prop n f.
Proof.
  intros. apply csf_ind_strong; unfold csf_to_com_is_valid_prop.
  - apply functional_extensionality. apply Vector.case0.
    reflexivity.
  - apply functional_extensionality. intros.
    rewrite (Vector.eta args). reflexivity.
  - apply csf_to_com_is_valid_proj.
  - intros. rename H into IHf. rename H0 into IHgs.
    apply functional_extensionality. intros.  
    unfold ceval. cbn [csf_to_com].
    remember (max (Vector.fold_left max n (Vector.map used_state_idx gs)) (used_state_idx f)) as u.
    cbn [ceval_st].
    rewrite unshift_is_valid_out_of_range; try lia. 
    cbn [csf_eval].
    unfold ceval in IHf. rewrite IHf.
    apply csf_com_eq_with_same_arg.
    intros i [Hi1 Hi2].
    rewrite unshift_is_valid_in_range; try lia.
    rewrite shift_is_valid_out_of_range; try lia.
    apply comvec_to_com_is_valid; try lia.
    apply IHgs.
Qed. 

(* Main theorem *)
Theorem csf_eq_com : forall n (f: csf n),
  exists c, csf_eval f = ceval c.
Proof.
  intros. exists (csf_to_com f). apply csf_to_com_is_valid.
Qed.

(** * Define conversion from Imp to CSF *)

Theorem le_sub: forall a b, 0 < a -> a - (S b) < a.
Proof. 
  intros. destruct a.
  - inversion H.
  - simpl. apply le_n_S. apply le_sub_l.
Qed.

Fixpoint skip_to_csfvec n (Hn: 0 < n) m :=
  match m with
  | O => []
  | S m' => Proj n (n - (S m')) (le_sub n m' Hn) :: (skip_to_csfvec n Hn m')
  end.
(* mapで書き換える？ *)

Fixpoint const_csf n m :=
  match m with
  | O => Comp 0 n Zero []
  | S m' => Comp 1 n Succ [const_csf n m']
  end.

Fixpoint in_range_aexp n a :=
  match a with
  | ANum m => true
  | <{ |x| }> => x <? n
  | <{ a' ++ }> => in_range_aexp n a'
  end.

Fixpoint in_range_com n c :=
  match c with
  | <{ skip }> => true
  | <{ x := a }> => in_range_aexp n a
  | <{ c1; c2 }> => in_range_com n c1 && in_range_com n c2
  end.

Definition proj_csf := const_csf.

Fixpoint aexp_to_csf n (Hn: 0 < n) a :=
  match a with
  | ANum m => const_csf n m
  | <{ |x| }> => proj_csf n x
      (* if in_range_aexp a then Proj n x Hx else const_csf n O *)
  | <{ a' ++ }> => Comp 1 n Succ [aexp_to_csf n Hn a']
  end.

Fixpoint asgn_to_csfvec n (Hn: 0 < n) m x a :=
  match m with
  | O => []
  | S m' =>
      (if ((n - m) =? x)%nat
        then aexp_to_csf n Hn a
        else Proj n (n - (S m')) (le_sub n m' Hn))
      :: (asgn_to_csfvec n Hn m' x a)
  end.

Definition compose_csfvec n (Hn: 0 < n) {m} (cv2: Vector.t (csf n) m) cv1 :=
  Vector.map (fun c => Comp n n c cv1) cv2.

Fixpoint com_to_csfvec n (Hn: 0 < n) c  :=
  match c with
  | <{ skip }> => skip_to_csfvec n Hn n
  | <{ x := a }> => asgn_to_csfvec n Hn n x a
  | <{ c1; c2 }> => compose_csfvec n Hn (com_to_csfvec n Hn c2) (com_to_csfvec n Hn c1)
  end.

Fixpoint used_max_idx_in_aexp a :=
  match a with
  | ANum _ => O
  | <{ |x| }> => x
  | <{ a' ++ }> => used_max_idx_in_aexp a'
  end.

Fixpoint used_max_idx_in_com c :=
  match c with
  | <{ skip }> => O
  | <{ x := a }> => max x (used_max_idx_in_aexp a)
  | <{ c1; c2 }> => max (used_max_idx_in_com c1) (used_max_idx_in_com c2)
  end.

Definition com_to_csf c :=
  let n' := used_max_idx_in_com c in
  let Hn := lt_0_succ n' in
  let n := S n' in
    Comp n n (Proj n 0 Hn) (com_to_csfvec n Hn c).

Fixpoint vec_to_state' {n: nat} (m: nat) (v: Vector.t nat n) : state :=
  match v with
  | [] => empty_st
  | (x :: v') => ((Id (m - n))) !-> x; (vec_to_state' m v')
  end.

Definition ceval' (c: com) {argn: nat} (args: Vector.t nat argn) : nat :=
  ((ceval_st c) (vec_to_state' argn args)) (Id 0).

Lemma used_max_idx_in_com_is_valid : forall c i st,
  used_max_idx_in_com c < i -> (ceval_st c st) (Id i) = st (Id i).
Proof.
  induction c.
  - reflexivity.
  - destruct x as [x]. simpl. intros.
    assert (i <> x) by lia. apply Nat.eqb_neq in H0.
    rewrite H0. reflexivity.
  - simpl. intros. rewrite IHc2; try lia.
    apply IHc1. lia.
Qed.

Lemma neq_lemma1: forall a b c, 0 < a -> b < c -> b + a - c < a .
Proof. lia. Qed.

Lemma fin_eq : forall {i j n} (Hi: i < n) (Hj: j < n),
  i = j -> <\ Hi /> = <\ Hj />.
Proof.
  intros. subst j. f_equal. apply proof_irrelevance.
Qed.

Lemma proj_eq : forall {i j n} (Hi: i < n) (Hj: j < n),
  i = j -> Proj n i Hi = Proj n j Hj.
Proof.
  intros. subst j. f_equal. apply proof_irrelevance.
Qed.

Lemma vec_to_state'_idx_general : forall {n} (v: Vector.t nat n) {i} m (Hi: i < n),
  n <= m -> vec_to_state' m v (Id (m - n + i)) = v [@<\ Hi />].
Proof.
  induction v as [|h n' v']; intros.
  - inversion Hi.
  - destruct i as [|i'].
    + simpl. replace (m - S n' + 0) with (m - S n') by lia.
      rewrite Nat.eqb_refl. reflexivity.
    + simpl. assert (Neq: m - S n' + S i' <> m - S n') by lia.
      apply Nat.eqb_neq in Neq. rewrite Neq.
      replace (m - S n' + S i') with (m - n' + i') by lia.
      apply IHv'. lia.
Qed.

Lemma vec_to_state'_idx : forall {n} (v: Vector.t nat n) {i} (Hi: i < n),
  vec_to_state' n v (Id i) = v [@<\ Hi />].
Proof.
  intros. rewrite <- vec_to_state'_idx_general with (m:=n); try lia.
  f_equal. f_equal. lia.
Qed. 

Lemma skip_to_csfvec_lemma_general : forall n (Hn: 0 < n) m i (Him: i < m),
  (skip_to_csfvec n Hn m) [@<\ Him />] = Proj n (i+n-m) (neq_lemma1 _ _ _ Hn Him).
Proof.
  induction m as [|m' IHm].
  - intros. inversion Him.
  - intros. cbn [skip_to_csfvec]. destruct i as [|i'].
    + simpl. apply proj_eq. reflexivity.
    + simpl. rewrite IHm. apply proj_eq. reflexivity.
Qed.

Lemma skip_to_csfvec_lemma : forall n (Hn: 0 < n) i (Hi: i < n),
  (skip_to_csfvec n Hn n) [@<\ Hi />] = Proj n i Hi.
Proof.
  intros. rewrite skip_to_csfvec_lemma_general.
  apply proj_eq. lia.
Qed.

Lemma skip_to_csfvec_is_valid : forall n (Hn: 0 < n) i (Hi: i < n) (args : Vector.t nat n),
  ceval_st <{ skip }> (vec_to_state' n args) (Id i) =
  csf_eval (skip_to_csfvec n Hn n) [@<\ Hi />] args.
Proof.
  intros. simpl.
  rewrite skip_to_csfvec_lemma. simpl.
  apply vec_to_state'_idx.
Qed.

Lemma asgn_to_csfvec_xth_general : forall n (Hn: 0 < n) m x (Hx: x - (n - m) < m) a,
  m <= n ->
  n - m <= x ->
  (asgn_to_csfvec n Hn m x a) [@<\ Hx />] = aexp_to_csf n Hn a.
Proof. 
  induction m as [|m' IHm].
  - intros. inversion Hx.
  - intros. cbn [asgn_to_csfvec].
    destruct (x - (n - S m')) as [|j'] eqn: Eqj.
    + simpl. assert (n - S m' = x) by lia.
      subst x. rewrite Nat.eqb_refl. reflexivity.
    + simpl. assert (x - (n - m') = j') by lia. subst j'.
      apply IHm; try lia.
Qed.

Lemma asgn_to_csfvec_xth : forall n (Hn: 0 < n) x (Hx: x < n) a,
  (asgn_to_csfvec n Hn n x a) [@<\ Hx />] = aexp_to_csf n Hn a.
Proof.
  intros. assert (Hx': x - (n - n) < n ) by lia.
  rewrite <- asgn_to_csfvec_xth_general with (m:=n) (x:=x) (Hx:=Hx'); try lia.
  rewrite (fin_eq Hx Hx').
  - reflexivity.
  - lia.
Qed.

Lemma asgn_to_csfvec_not_xth_general :
  forall n (Hn: 0 < n) m x a i (Hinm: i - (n - m) < m) (Hi: i < n),
    m <= n ->
    n - m <= i ->
    i <> x ->
    (asgn_to_csfvec n Hn m x a) [@<\ Hinm />] = Proj n i Hi.
Proof.
  induction m as [|m' IHm]; intros.
  - inversion Hinm.
  - cbn [asgn_to_csfvec]. destruct (i - (n - S m')) as [|j'] eqn: Eqj.
    + assert (n - S m' <> x) by lia. apply Nat.eqb_neq in H2.
      rewrite H2. simpl. apply proj_eq. lia.
    + simpl. assert (j'=(i - (n - m'))) by lia.
      subst j'. apply IHm; try lia.
Qed.

Lemma asgn_to_csfvec_not_xth : forall n (Hn: 0 < n) x a i (Hi: i < n),
  i <> x ->
  (asgn_to_csfvec n Hn n x a) [@<\ Hi />] = Proj n i Hi.
Proof.
  intros. assert (Hinm: i - (n - n) < n ) by lia.
  rewrite <- asgn_to_csfvec_not_xth_general with (Hn:=Hn) (m:=n) (x:=x) (a:=a) (Hinm:=Hinm); try lia.
  rewrite (fin_eq Hi Hinm).
  - reflexivity.
  - lia.
Qed.

Lemma aexp_to_csf_is_valid : forall n args (Hn: 0 < n) a,
  aeval (vec_to_state' n args) a = csf_eval (aexp_to_csf n Hn a) args.
Proof.
  induction a.
  - simpl. admit.
  - simpl. destruct x as [x]. 


Lemma asgn_to_csfvec_is_valid : forall n (Hn: 0 < n) i (Hi: i < n) x a (args : Vector.t nat n),
  ceval_st <{ x := a }> (vec_to_state' n args) (Id i) =
  csf_eval (asgn_to_csfvec n Hn n x a) [@<\ Hi />] args.
Proof.
  intros. destruct (i =? x) eqn: Eqix. 
  - apply Nat.eqb_eq in Eqix. subst i.
    rewrite asgn_to_csfvec_xth.
    cbn [ceval_st]. simpl. rewrite Nat.eqb_refl.
    admit.
  - rewrite asgn_to_csfvec_not_xth.
    * simpl. rewrite Eqix. apply vec_to_state'_idx.
    * intro. apply Nat.eqb_eq in H.
      rewrite H in Eqix. discriminate.
Admitted.

Lemma comp_proj_lemma : forall m n i (Hi: i < m) gs,
  csf_eval (Comp m n (Proj m i Hi) gs) = csf_eval (gs [@<\ Hi />]).
Proof.
  intros. apply functional_extensionality.
  intros. simpl. 
  generalize dependent args. generalize dependent i.
  induction gs.
  - inversion Hi.
  - intros. cbn [Vector.map]. destruct i.
    + reflexivity.
    + simpl. apply IHgs.
Qed.

Lemma compose_csfvec_lemma : forall n (Hn: 0 < n) i (Hi: i < n) c1 c2,
  (compose_csfvec n Hn (com_to_csfvec n Hn c2) (com_to_csfvec n Hn c1)) [@<\ Hi />]
  = Comp n n (com_to_csfvec n Hn c2) [@<\ Hi />] (com_to_csfvec n Hn c1).
Proof. Admitted.

Lemma csfvec_lemma : forall n args (csfs: Vector.t (csf n) n) i (Hi: i < n),
  csf_eval csfs [@<\ Hi />] args =
  vec_to_state' n (VectorDef.map (fun x : csf n => csf_eval x args) csfs) (Id i).
Proof.
  induction csfs as [|f n' csfs']; intros.
  - inversion Hi.
  - cbn [VectorDef.map vec_to_state']. rewrite sub_diag.
    destruct i as [|i'].
    + reflexivity.
    + simpl. rewrite IHcsfs'.
      apply le_S_n in Hi.
      rewrite vec_to_state'_idx with (Hi:=Hi).
      replace (S i') with (S n' - n' + i') by lia.
      rewrite vec_to_state'_idx_general with (Hi:=Hi); try lia.
Qed.

Lemma com_to_csfvec_is_valid : forall c n (Hn: 0 < n) i (Hi: i < n) (args : Vector.t nat n),
  n <= S (used_max_idx_in_com c) ->
  (ceval_st c (vec_to_state' n args)) (Id i) =
  (csf_eval ((com_to_csfvec n Hn c) [@ <\ Hi />])) args.
Proof.
  induction c; intros.
  - apply skip_to_csfvec_is_valid.
  - destruct x as [x]. cbn [com_to_csfvec]. apply asgn_to_csfvec_is_valid.
  - simpl. unfold compose_csfvec.
    rewrite Vector.nth_map with (p2:=<\Hi/>); try reflexivity.
    cbn [csf_eval]. rewrite <- IHc2. rewrite Vector.map_map.
    f_equal. apply functional_extensionality. intros j. destruct j as [j].
    destruct (j <? n) eqn: Hj.
    + apply ltb_lt in Hj.  
      rewrite IHc1 with (Hn:=Hn) (Hi:=Hj).
      * simpl. apply csfvec_lemma.
      * simpl in H. admit.
    + apply ltb_nlt in Hj.
      rewrite used_max_idx_in_com_is_valid.
      *   

  (* rewrite compose_csfvec_lemma. simpl. *)
    (* rewrite <- IHc2.  *)
Admitted.

Lemma com_to_csf_is_valid : forall c, 
  ceval' c = csf_eval (com_to_csf c).
Proof.
  intros. apply functional_extensionality.
  intros. unfold ceval'.
  cbv [com_to_csf]. rewrite comp_proj_lemma.
  apply com_to_csfvec_is_valid. lia.
Qed.
  
Theorem com_eq_csf : forall (c: com),
  exists (n: nat) (f: csf n), ceval' c = csf_eval f.
Proof.
  intros. exists _, (com_to_csf c).
  apply com_to_csf_is_valid.
Qed.

(* Lemma com_to_csf_is_valid : forall c, 
  ceval' c = csf_eval (com_to_csf c).
Proof.
  intros. apply functional_extensionality. unfold ceval'.
  intros. cbv [com_to_csf]. cbn [csf_eval].
  rewrite (Vector.eta args). cbn [com_to_csfvec].
  induction c; intros.
  - rewrite (Vector.eta args). reflexivity.


  (* intros. apply functional_extensionality. unfold ceval'.
  induction c; intros.
  - rewrite (Vector.eta args). reflexivity. *)
  - cbn [ceval_st used_max_idx_in_com]. destruct x as [x].
    cbv [com_to_csf]. cbn [used_max_idx_in_com com_to_csfvec asgn_to_csfvec].
    cbn [csf_eval]. simpl.  cbv [Vector.map].
    simpl. destruct x as [|x'].
    + simpl in args.  
    
(* Lemma com_to_csfvec_is_valid : forall c i (Hi: i <= (used_max_idx_in_com c)) (args : Vector.t nat (S (used_max_idx_in_com c))),
  (ceval_st c (vec_to_state' (used_max_idx_in_com c) args)) (Id i) =
  csf_eval (Comp (S (used_max_idx_in_com c)) (S (used_max_idx_in_com c))
  (Proj (S (used_max_idx_in_com c)) i (le_n_S _ _ Hi)) (com_to_csfvec (S (used_max_idx_in_com c)) (lt_0_succ (used_max_idx_in_com c)) c)) args. *)

(* Lemma com_to_csfvec_is_valid : forall c i (Hi: i <= (used_max_idx_in_com c)) (args : Vector.t nat (S (used_max_idx_in_com c))),
  (ceval_st c (vec_to_state' (S (used_max_idx_in_com c)) args)) (Id i) =
  (csf_eval ((com_to_csfvec (S (used_max_idx_in_com c)) (lt_0_succ (used_max_idx_in_com c)) c) [@ <\ (le_n_S _ _ Hi) />])) args.
Proof.
  intros. induction c.
  - simpl in Hi. inversion Hi. subst i.
    simpl in args. rewrite (Vector.eta args). reflexivity.
  - cbn [used_max_idx_in_com] in *. destruct x as [x].
    cbn [ceval_st com_to_csfvec asgn_to_csfvec].
    (* generalize dependent n. *)
    induction (used_max_idx_in_aexp a) eqn: Eqn.
    + rewrite (Vector.eta args). inversion Hi. subst i.
      cbn [asgn_to_csfvec vec_to_state']. simpl.
      destruct x.
      * admit.
      * reflexivity.
    + destruct x.
      * destruct i.
        { simpl. replace (n - n =? 0) with true by (rewrite sub_diag; reflexivity). 
          admit.
        }
        { simpl. simpl in IHn. admit. } 
       
      
Admitted. *)

(* Lemma used_max_idx_lemma_aexp :
  forall a, in_range_aexp (S (used_max_idx_in_aexp a)) a.
Proof.
  induction a.
  - constructor.
  - destruct x. apply IRId. simpl. lia.
  - simpl. constructor. apply IHa.
Qed.

Lemma in_range_aexp_weaken :
  forall a m n, m <= n -> in_range_aexp m a -> in_range_aexp n a.
Proof.
  intros. induction H0.
  - constructor.
  - constructor. lia.
  - constructor. assumption.
Qed.

Lemma in_range_com_weaken :
  forall c m n, m <= n -> in_range_com m c -> in_range_com n c.
Proof.
  intros. induction H0.
  - constructor.
  - constructor. apply in_range_aexp_weaken with (m:=m); assumption.
  - constructor; assumption. 
Qed.

Lemma used_max_idx_lemma :
  forall c, in_range_com (S (used_max_idx_in_com c)) c.
Proof.
  induction c.
  - simpl. constructor.
  - destruct x. simpl. apply IRAsgn.
    apply used_max_idx_lemma_aexp.
  - simpl. apply IRSeq.
    + apply in_range_com_weaken with (m:=(S (used_max_idx_in_com c1))).
      * lia. * assumption.
    + apply in_range_com_weaken with (m:=(S (used_max_idx_in_com c2))).
      * lia. * assumption.
Qed. *)

(* 
  Id 0 = | i | .. proj i n
  Id i = x; c .. c ([proj 0 n; proj 1 n; ... x; proj i n; .. proj n-1 n; ])
  Id 0 = n ++ .. succ 
  skip .. zero
  c1; c2 .. st =[ c1 ]=> st', c2 (state_to_arg st')

*) *)



(* max_used_idx で左側に出てくるのも考慮したほうがいいかも *)
(* IMP型にパラメータを持たせる *)
(* Vector がからむ処理で map 使ったりしたい *)
(* (map f v)[i] = f (v[i]) *)