Set Warnings "-notation-overridden".
From Stdlib Require Import Bool.
From Stdlib Require Import Init.Nat.
From Stdlib Require Import Arith.
From Stdlib Require Import EqNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Program.Equality.

#[local] Set Warnings "-stdlib-vector".
From Stdlib Require Fin.
From Stdlib Require Vector.
From Stdlib Require Logic.ProofIrrelevance.
From Equations Require Import Equations.

Local Notation "[ ]" := (Vector.nil _) (format "[ ]").
Local Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity).
Local Notation "[ x ; .. ; y ]" := 
    (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).

Local Notation "v [@ p ]" := (Vector.nth v p) (at level 1).
Local Notation "<\ H />" := (Fin.of_nat_lt H) (at level 1).

Inductive csf : nat -> Type :=
  | Zero : csf 0
  | Succ : csf 1
  | Proj (n i: nat) (H: i < n) : csf n
  | Comp (m n: nat) (f: csf m) (gs: Vector.t (csf n) m) : csf n
.

Definition lt01 : 0 < 1.
Proof. apply le_n. Qed.

Definition ltnSn : forall n, n < S n.
Proof. intros. apply le_n. Qed.

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
    end
.

Inductive ident : Type :=
  | Id (n: nat)
.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : ident)
  | ASucc (a1: aexp)
.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
.

Coercion AId : ident >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e
  (e custom com, format "'[hv' <{ '/  ' '[v' e ']' '/' }> ']'") : com_scope.

Notation "x" := x%nat (in custom com at level 0, x constr at level 0).

Notation "x ++"   := (ASucc x) (in custom com at level 50, right associativity).
Notation "| x |"   := (AId (Id x)) (in custom com at level 85).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).

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

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x 
  | <{a1 ++}> => S (aeval st a1)
  end.

Definition beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  end.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : ident) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com).

Notation "'skip'"  := CSkip
  (in custom com at level 0) : com_scope.
Notation "x := y"  := (CAsgn (Id x) y)
  (in custom com at level 0, x constr at level 0, y at level 85, no associativity,
    format "x  :=  y") : com_scope.
Notation "x ; y" := (CSeq x y)
  (in custom com at level 90,
    right associativity,
    format "'[v' x ; '/' y ']'") : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" := (CIf x y z)
  (in custom com at level 89, x at level 99, y at level 99, z at level 99,
    format "'[v' 'if'  x  'then' '/  ' y '/' 'else' '/  ' z '/' 'end' ']'") : com_scope.

Fixpoint app_ntimes {X: Type} (f: X -> X) (n: nat) (x: X) : X :=
  match n with
  | O => x
  | S n' => f (app_ntimes f n' x)
  end
.

Fixpoint ceval_st (c: com) (st: state) : state :=
  match c with
  | <{ skip }> => st
  | <{ x := a }> => ((Id x) !-> (aeval st a) ; st)
  | <{ c1; c2 }> => (ceval_st c2) (ceval_st c1 st)
  | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_st c1 st
          else ceval_st c2 st
  end
.

Fixpoint vec_to_state {n: nat} (m: nat) (v: Vector.t nat n) : state :=
  match n, v with
  | O, _ => empty_st
  | S n', v =>
      let x := Vector.hd v in
      let xs := Vector.tl v in
        ((Id (S(m - n))) !-> x; (vec_to_state m xs))
  end
.

Definition ceval (c: com) {argn: nat} (args: Vector.t nat argn) : nat :=
  ((ceval_st c) (vec_to_state argn args)) (Id 0).

Axiom functional_extensionality : 
  forall {X Y: Type} (f g: X -> Y), (forall args, f args = g args) -> f = g.

Fixpoint shift_com i k n : com :=
  match k with
  | O => <{ skip }>
  | S k' => <{ (i + k' + n) := |(i + k')| ;
               (shift_com i k' n) }>
  end
.

Fixpoint unshift_com i k n : com :=
  match k with
  | O => <{ skip }>
  | S k' => <{ i := |(i + n)| ;
               (unshift_com (S i) k' n) }>
  end
.

Fixpoint comvec_to_com (j: nat) {k: nat} (g_coms: Vector.t com k) : com :=
  match g_coms with
  | [] => <{ skip }>
  | (g_com :: g_coms') =>
        <{ g_com; j := |0|; (comvec_to_com (S j) g_coms') }>
  end
.

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
  end
.

Theorem lt_03: 0 < 3.
Proof. lia. Qed.

Compute (csf_to_com (Comp 3 1 (Proj 3 0 (lt_03)) (Succ :: Succ :: Succ :: []))).  

Ltac neq_rewrite n m :=
  assert (__Neq__: n <> m) by lia;
  rewrite <- Nat.eqb_neq in __Neq__;
  rewrite __Neq__;
  try reflexivity;
  clear __Neq__.

Lemma vec_to_state_shift : forall n m i (v: Vector.t nat n),
  n <= m -> (vec_to_state m v) (Id i) = (vec_to_state (S m) v) (Id (S i)).
Proof.
  intros. induction v.
  - reflexivity.
  - simpl. rewrite IHv. 
    + replace (S (m - S n)) with (m - n) by lia. reflexivity.
    + apply le_S_n. apply le_S. apply H.
Qed.

Lemma csf_eq_com_proj : forall n i H, 
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

Lemma vec_fold_max_lemma_4: forall n m (v: Vector.t nat m),
  n <= Vector.fold_left max n v.
Proof.
  induction v.
  - simpl. lia.
  - simpl. specialize (vec_fold_max_lemma_2 _ v n (max n h)) as H.
    lia.
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

Definition csf_com_eq_with_same_arg_prop n (f: csf n) :=
  forall st st', 
    (forall i, 1 <= i <= n -> st (Id i) = st' (Id i)) ->
    ceval_st (csf_to_com f) st (Id 0) = ceval_st (csf_to_com f) st' (Id 0).

Lemma comvec_does_not_change_state:
  forall n m (gs: Vector.t (csf n) m) i u st,
    Vector_Forall_csf csf_com_eq_with_same_arg_prop gs ->
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
      * inversion H0.
      * apply le_n_S. apply le_S_n in H0.
        apply vec_fold_max_lemma_1 in H0. lia.
    + apply H.
    + destruct i.
      * inversion H0.
      * apply le_n_S. apply le_S_n in H0.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
    + lia.
Qed.

Lemma csf_com_eq_with_same_arg_vec:
  forall n m (gs: Vector.t (csf n) m) i u st st',
    Vector_Forall_csf csf_com_eq_with_same_arg_prop gs ->
    (forall i, 1 <= i /\ i <= n -> st (Id i) = st' (Id i)) ->
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
      * apply H.
      * apply le_n_S. simpl in H2.
        apply vec_fold_max_lemma_3 with (j:=max n (used_state_idx h)); lia.
      * apply H.
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

Definition csf_eq_com_prop (n: nat) (f: csf n) :=
  csf_eval f = ceval (csf_to_com f).

Lemma vector_forall_lemma: forall n m (gs: Vector.t (csf n) m) P,
  (forall n f, P n f) ->
  Vector_Forall_csf P gs.
Proof.
  intros. induction gs; intros; unfold Vector_Forall_csf.
  - simpl. apply I.
  - simpl. split.
    + apply H.
    + apply IHgs.
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
      * apply vector_forall_lemma. apply csf_com_eq_with_same_arg.
      * simpl in Hu. apply le_n_S.
        apply vec_fold_max_lemma_3 with (j:=(max n (used_state_idx h))); lia.
      * apply vector_forall_lemma. apply csf_com_eq_with_same_arg.
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

Lemma comvec_to_com_is_valid: forall m n (gs: Vector.t (csf n) m) args i u ,
  1 <= i <= m ->
  Vector.fold_left max n (Vector.map used_state_idx gs) <= u ->
  Vector_Forall_csf csf_eq_com_prop gs ->
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
      * apply vector_forall_lemma. apply csf_com_eq_with_same_arg.
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
  
Theorem csf_eq_com: forall (n: nat) (f: csf n),
  csf_eq_com_prop n f.
Proof.
  intros. apply csf_ind_strong; unfold csf_eq_com_prop.
  - apply functional_extensionality. apply Vector.case0.
    reflexivity.
  - apply functional_extensionality. intros.
    rewrite (Vector.eta args). reflexivity.
  - apply csf_eq_com_proj.
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


Theorem com_eq_csf : forall (c: com),
  exists (n: nat) (f: csf n), csf_eval f = ceval c.
Proof.
Admitted.
  
(* i<n で詰まったら proof irrelevance 使ったほうが良さそう *)

(* primrec消してやってみよう *)
