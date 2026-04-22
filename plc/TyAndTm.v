Require Import core unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive ty : Type :=
  | var_ty : nat -> ty
  | TyArrow : ty -> ty -> ty
  | TyForall : ty -> ty
  | TyUnit : ty.

Lemma congr_TyArrow {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TyArrow s0 s1 = TyArrow t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TyArrow x s1) H0))
         (ap (fun x => TyArrow t0 x) H1)).
Qed.

Lemma congr_TyForall {s0 : ty} {t0 : ty} (H0 : s0 = t0) :
  TyForall s0 = TyForall t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => TyForall x) H0)).
Qed.

Lemma congr_TyUnit : TyUnit = TyUnit.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_ty_ty (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_ty (xi_ty : nat -> nat) (s : ty) {struct s} : ty :=
  match s with
  | var_ty s0 => var_ty (xi_ty s0)
  | TyArrow s0 s1 => TyArrow (ren_ty xi_ty s0) (ren_ty xi_ty s1)
  | TyForall s0 => TyForall (ren_ty (upRen_ty_ty xi_ty) s0)
  | TyUnit => TyUnit
  end.

Lemma up_ty_ty (sigma : nat -> ty) : nat -> ty.
Proof.
exact (scons (var_ty var_zero) (funcomp (ren_ty shift) sigma)).
Defined.

Fixpoint subst_ty (sigma_ty : nat -> ty) (s : ty) {struct s} : ty :=
  match s with
  | var_ty s0 => sigma_ty s0
  | TyArrow s0 s1 => TyArrow (subst_ty sigma_ty s0) (subst_ty sigma_ty s1)
  | TyForall s0 => TyForall (subst_ty (up_ty_ty sigma_ty) s0)
  | TyUnit => TyUnit
  end.

Lemma upId_ty_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_ty_ty sigma x = var_ty x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_ty (sigma_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = var_ty x) (s : ty) {struct s} :
subst_ty sigma_ty s = s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall (idSubst_ty (up_ty_ty sigma_ty) (upId_ty_ty _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma upExtRen_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x) (s : ty) {struct s} :
ren_ty xi_ty s = ren_ty zeta_ty s :=
  match s with
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
  | TyArrow s0 s1 =>
      congr_TyArrow (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (extRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_ty _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma upExt_ty_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(Eq_ty : forall x, sigma_ty x = tau_ty x) (s : ty) {struct s} :
subst_ty sigma_ty s = subst_ty tau_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (ext_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty) (upExt_ty_ty _ _ Eq_ty)
           s0)
  | TyUnit => congr_TyUnit
  end.

Lemma up_ren_ren_ty_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat)
(rho_ty : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(s : ty) {struct s} : ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty rho_ty s :=
  match s with
  | var_ty s0 => ap (var_ty) (Eq_ty s0)
  | TyArrow s0 s1 =>
      congr_TyArrow (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (compRenRen_ty (upRen_ty_ty xi_ty) (upRen_ty_ty zeta_ty)
           (upRen_ty_ty rho_ty) (up_ren_ren _ _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma up_ren_subst_ty_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty) {struct s} :
subst_ty tau_ty (ren_ty xi_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (compRenSubst_ty (upRen_ty_ty xi_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_ren_subst_ty_ty _ _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma up_subst_ren_ty_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_ty zeta_ty)) (up_ty_ty sigma) x =
  up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_ty shift (upRen_ty_ty zeta_ty)
                (funcomp shift zeta_ty) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_ty zeta_ty shift (funcomp shift zeta_ty)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_ty shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x) 
(s : ty) {struct s} :
ren_ty zeta_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (compSubstRen_ty (up_ty_ty sigma_ty) (upRen_ty_ty zeta_ty)
           (up_ty_ty theta_ty) (up_subst_ren_ty_ty _ _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma up_subst_subst_ty_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_ty tau_ty)) (up_ty_ty sigma) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_ty shift (up_ty_ty tau_ty)
                (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_ty tau_ty shift
                      (funcomp (ren_ty shift) tau_ty) (fun x => eq_refl)
                      (sigma n')))
                (ap (ren_ty shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty)
(theta_ty : nat -> ty)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(s : ty) {struct s} :
subst_ty tau_ty (subst_ty sigma_ty s) = subst_ty theta_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (compSubstSubst_ty (up_ty_ty sigma_ty) (up_ty_ty tau_ty)
           (up_ty_ty theta_ty) (up_subst_subst_ty_ty _ _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma renRen_ty (xi_ty : nat -> nat) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (ren_ty xi_ty s) = ren_ty (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_ty_pointwise (xi_ty : nat -> nat) (zeta_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_ty) (ren_ty xi_ty))
    (ren_ty (funcomp zeta_ty xi_ty)).
Proof.
exact (fun s => compRenRen_ty xi_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty (xi_ty : nat -> nat) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (ren_ty xi_ty s) = subst_ty (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty_pointwise (xi_ty : nat -> nat) (tau_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty tau_ty) (ren_ty xi_ty))
    (subst_ty (funcomp tau_ty xi_ty)).
Proof.
exact (fun s => compRenSubst_ty xi_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) (s : ty) :
  ren_ty zeta_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (ren_ty zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty_pointwise (sigma_ty : nat -> ty) (zeta_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (ren_ty zeta_ty) sigma_ty)).
Proof.
exact (fun s => compSubstRen_ty sigma_ty zeta_ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty (sigma_ty : nat -> ty) (tau_ty : nat -> ty) (s : ty) :
  subst_ty tau_ty (subst_ty sigma_ty s) =
  subst_ty (funcomp (subst_ty tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty_pointwise (sigma_ty : nat -> ty) (tau_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty tau_ty) (subst_ty sigma_ty))
    (subst_ty (funcomp (subst_ty tau_ty) sigma_ty)).
Proof.
exact (fun s => compSubstSubst_ty sigma_ty tau_ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ty_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_ty_ty xi) x = up_ty_ty sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ty shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_ty (xi_ty : nat -> nat) (sigma_ty : nat -> ty)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x) (s : ty) {struct s}
   :
ren_ty xi_ty s = subst_ty sigma_ty s :=
  match s with
  | var_ty s0 => Eq_ty s0
  | TyArrow s0 s1 =>
      congr_TyArrow (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | TyForall s0 =>
      congr_TyForall
        (rinst_inst_ty (upRen_ty_ty xi_ty) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_ty _ _ Eq_ty) s0)
  | TyUnit => congr_TyUnit
  end.

Lemma rinstInst'_ty (xi_ty : nat -> nat) (s : ty) :
  ren_ty xi_ty s = subst_ty (funcomp (var_ty) xi_ty) s.
Proof.
exact (rinst_inst_ty xi_ty _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_ty_pointwise (xi_ty : nat -> nat) :
  pointwise_relation _ eq (ren_ty xi_ty) (subst_ty (funcomp (var_ty) xi_ty)).
Proof.
exact (fun s => rinst_inst_ty xi_ty _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ty (s : ty) : subst_ty (var_ty) s = s.
Proof.
exact (idSubst_ty (var_ty) (fun n => eq_refl) s).
Qed.

Lemma instId'_ty_pointwise : pointwise_relation _ eq (subst_ty (var_ty)) id.
Proof.
exact (fun s => idSubst_ty (var_ty) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ty (s : ty) : ren_ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma rinstId'_ty_pointwise : pointwise_relation _ eq (@ren_ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma varL'_ty (sigma_ty : nat -> ty) (x : nat) :
  subst_ty sigma_ty (var_ty x) = sigma_ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ty_pointwise (sigma_ty : nat -> ty) :
  pointwise_relation _ eq (funcomp (subst_ty sigma_ty) (var_ty)) sigma_ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_ty (xi_ty : nat -> nat) (x : nat) :
  ren_ty xi_ty (var_ty x) = var_ty (xi_ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ty_pointwise (xi_ty : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty xi_ty) (var_ty))
    (funcomp (var_ty) xi_ty).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive tm : Type :=
  | TmApp : tm -> tm -> tm
  | TmTApp : tm -> ty -> tm
  | TmVal : vl -> tm
with vl : Type :=
  | var_vl : nat -> vl
  | TmAbs : ty -> tm -> vl
  | TmTAbs : tm -> vl
  | TmUnit : vl.

Lemma congr_TmApp {s0 : tm} {s1 : tm} {t0 : tm} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmApp s0 s1 = TmApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmApp x s1) H0))
         (ap (fun x => TmApp t0 x) H1)).
Qed.

Lemma congr_TmTApp {s0 : tm} {s1 : ty} {t0 : tm} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmTApp s0 s1 = TmTApp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmTApp x s1) H0))
         (ap (fun x => TmTApp t0 x) H1)).
Qed.

Lemma congr_TmVal {s0 : vl} {t0 : vl} (H0 : s0 = t0) : TmVal s0 = TmVal t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => TmVal x) H0)).
Qed.

Lemma congr_TmAbs {s0 : ty} {s1 : tm} {t0 : ty} {t1 : tm} (H0 : s0 = t0)
  (H1 : s1 = t1) : TmAbs s0 s1 = TmAbs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => TmAbs x s1) H0))
         (ap (fun x => TmAbs t0 x) H1)).
Qed.

Lemma congr_TmTAbs {s0 : tm} {t0 : tm} (H0 : s0 = t0) : TmTAbs s0 = TmTAbs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => TmTAbs x) H0)).
Qed.

Lemma congr_TmUnit : TmUnit = TmUnit.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_ty_vl (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_vl_ty (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_vl_vl (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : tm) {struct s}
   :
tm :=
  match s with
  | TmApp s0 s1 => TmApp (ren_tm xi_ty xi_vl s0) (ren_tm xi_ty xi_vl s1)
  | TmTApp s0 s1 => TmTApp (ren_tm xi_ty xi_vl s0) (ren_ty xi_ty s1)
  | TmVal s0 => TmVal (ren_vl xi_ty xi_vl s0)
  end
with ren_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : vl) {struct s} :
vl :=
  match s with
  | var_vl s0 => var_vl (xi_vl s0)
  | TmAbs s0 s1 =>
      TmAbs (ren_ty xi_ty s0)
        (ren_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl) s1)
  | TmTAbs s0 => TmTAbs (ren_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl) s0)
  | TmUnit => TmUnit
  end.

Lemma up_ty_vl (sigma : nat -> vl) : nat -> vl.
Proof.
exact (funcomp (ren_vl shift id) sigma).
Defined.

Lemma up_vl_ty (sigma : nat -> ty) : nat -> ty.
Proof.
exact (funcomp (ren_ty id) sigma).
Defined.

Lemma up_vl_vl (sigma : nat -> vl) : nat -> vl.
Proof.
exact (scons (var_vl var_zero) (funcomp (ren_vl id shift) sigma)).
Defined.

Fixpoint subst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) (s : tm)
{struct s} : tm :=
  match s with
  | TmApp s0 s1 =>
      TmApp (subst_tm sigma_ty sigma_vl s0) (subst_tm sigma_ty sigma_vl s1)
  | TmTApp s0 s1 =>
      TmTApp (subst_tm sigma_ty sigma_vl s0) (subst_ty sigma_ty s1)
  | TmVal s0 => TmVal (subst_vl sigma_ty sigma_vl s0)
  end
with subst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) (s : vl) {struct
 s} :
vl :=
  match s with
  | var_vl s0 => sigma_vl s0
  | TmAbs s0 s1 =>
      TmAbs (subst_ty sigma_ty s0)
        (subst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) s1)
  | TmTAbs s0 => TmTAbs (subst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) s0)
  | TmUnit => TmUnit
  end.

Lemma upId_ty_vl (sigma : nat -> vl) (Eq : forall x, sigma x = var_vl x) :
  forall x, up_ty_vl sigma x = var_vl x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma upId_vl_ty (sigma : nat -> ty) (Eq : forall x, sigma x = var_ty x) :
  forall x, up_vl_ty sigma x = var_ty x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upId_vl_vl (sigma : nat -> vl) (Eq : forall x, sigma x = var_vl x) :
  forall x, up_vl_vl sigma x = var_vl x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_vl id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl x) (s : tm) {struct s} :
subst_tm sigma_ty sigma_vl s = s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp (idSubst_tm sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (idSubst_ty sigma_ty Eq_ty s1)
  | TmVal s0 => congr_TmVal (idSubst_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with idSubst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = var_ty x)
(Eq_vl : forall x, sigma_vl x = var_vl x) (s : vl) {struct s} :
subst_vl sigma_ty sigma_vl s = s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (idSubst_ty sigma_ty Eq_ty s0)
        (idSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upId_vl_ty _ Eq_ty) (upId_vl_vl _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (idSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upId_ty_ty _ Eq_ty) (upId_ty_vl _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma upExtRen_ty_vl (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_vl xi x = upRen_ty_vl zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_vl_ty (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_ty xi x = upRen_vl_ty zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_vl_vl (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_vl_vl xi x = upRen_vl_vl zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : tm) {struct s} :
ren_tm xi_ty xi_vl s = ren_tm zeta_ty zeta_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp (extRen_tm xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
        (extRen_ty xi_ty zeta_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal (extRen_vl xi_ty xi_vl zeta_ty zeta_vl Eq_ty Eq_vl s0)
  end
with extRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat)
(Eq_ty : forall x, xi_ty x = zeta_ty x)
(Eq_vl : forall x, xi_vl x = zeta_vl x) (s : vl) {struct s} :
ren_vl xi_ty xi_vl s = ren_vl zeta_ty zeta_vl s :=
  match s with
  | var_vl s0 => ap (var_vl) (Eq_vl s0)
  | TmAbs s0 s1 =>
      congr_TmAbs (extRen_ty xi_ty zeta_ty Eq_ty s0)
        (extRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl)
           (upExtRen_vl_ty _ _ Eq_ty) (upExtRen_vl_vl _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (extRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
           (upExtRen_ty_ty _ _ Eq_ty) (upExtRen_ty_vl _ _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma upExt_ty_vl (sigma : nat -> vl) (tau : nat -> vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_vl sigma x = up_ty_vl tau x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma upExt_vl_ty (sigma : nat -> ty) (tau : nat -> ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_ty sigma x = up_vl_ty tau x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma upExt_vl_vl (sigma : nat -> vl) (tau : nat -> vl)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_vl_vl sigma x = up_vl_vl tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_vl id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : tm) {struct s} :
subst_tm sigma_ty sigma_vl s = subst_tm tau_ty tau_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp (ext_tm sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
        (ext_ty sigma_ty tau_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal (ext_vl sigma_ty sigma_vl tau_ty tau_vl Eq_ty Eq_vl s0)
  end
with ext_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl)
(Eq_ty : forall x, sigma_ty x = tau_ty x)
(Eq_vl : forall x, sigma_vl x = tau_vl x) (s : vl) {struct s} :
subst_vl sigma_ty sigma_vl s = subst_vl tau_ty tau_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (ext_ty sigma_ty tau_ty Eq_ty s0)
        (ext_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl) (up_vl_ty tau_ty)
           (up_vl_vl tau_vl) (upExt_vl_ty _ _ Eq_ty) (upExt_vl_vl _ _ Eq_vl)
           s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (ext_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl) (up_ty_ty tau_ty)
           (up_ty_vl tau_vl) (upExt_ty_ty _ _ Eq_ty) (upExt_ty_vl _ _ Eq_vl)
           s0)
  | TmUnit => congr_TmUnit
  end.

Lemma up_ren_ren_ty_vl (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_vl zeta) (upRen_ty_vl xi) x = upRen_ty_vl rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_vl_ty (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_ty zeta) (upRen_vl_ty xi) x = upRen_vl_ty rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_vl_vl (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_vl_vl zeta) (upRen_vl_vl xi) x = upRen_vl_vl rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (rho_ty : nat -> nat)
(rho_vl : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : tm) {struct s} :
ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) = ren_tm rho_ty rho_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s1)
  | TmTApp s0 s1 =>
      congr_TmTApp
        (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
        (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal
        (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl rho_ty rho_vl Eq_ty Eq_vl
           s0)
  end
with compRenRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (rho_ty : nat -> nat)
(rho_vl : nat -> nat) (Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x)
(Eq_vl : forall x, funcomp zeta_vl xi_vl x = rho_vl x) (s : vl) {struct s} :
ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) = ren_vl rho_ty rho_vl s :=
  match s with
  | var_vl s0 => ap (var_vl) (Eq_vl s0)
  | TmAbs s0 s1 =>
      congr_TmAbs (compRenRen_ty xi_ty zeta_ty rho_ty Eq_ty s0)
        (compRenRen_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (upRen_vl_ty rho_ty)
           (upRen_vl_vl rho_vl) Eq_ty (up_ren_ren _ _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (compRenRen_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (upRen_ty_ty rho_ty)
           (upRen_ty_vl rho_vl) (up_ren_ren _ _ _ Eq_ty) Eq_vl s0)
  | TmUnit => congr_TmUnit
  end.

Lemma up_ren_subst_ty_vl (xi : nat -> nat) (tau : nat -> vl)
  (theta : nat -> vl) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_vl tau) (upRen_ty_vl xi) x = up_ty_vl theta x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma up_ren_subst_vl_ty (xi : nat -> nat) (tau : nat -> ty)
  (theta : nat -> ty) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_vl_ty tau) (upRen_vl_ty xi) x = up_vl_ty theta x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma up_ren_subst_vl_vl (xi : nat -> nat) (tau : nat -> vl)
  (theta : nat -> vl) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_vl_vl tau) (upRen_vl_vl xi) x = up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_vl id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : tm) {struct s} :
subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) = subst_tm theta_ty theta_vl s
:=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp
        (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
        (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal
        (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl theta_ty theta_vl Eq_ty
           Eq_vl s0)
  end
with compRenSubst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x)
(Eq_vl : forall x, funcomp tau_vl xi_vl x = theta_vl x) (s : vl) {struct s} :
subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) = subst_vl theta_ty theta_vl s
:=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compRenSubst_ty xi_ty tau_ty theta_ty Eq_ty s0)
        (compRenSubst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_ren_subst_vl_ty _ _ _ Eq_ty)
           (up_ren_subst_vl_vl _ _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (compRenSubst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_ren_subst_ty_ty _ _ _ Eq_ty)
           (up_ren_subst_ty_vl _ _ _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma up_subst_ren_ty_vl (sigma : nat -> vl) (zeta_ty : nat -> nat)
  (zeta_vl : nat -> nat) (theta : nat -> vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl))
    (up_ty_vl sigma) x =
  up_ty_vl theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_vl shift id (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl)
            (funcomp shift zeta_ty) (funcomp id zeta_vl) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_vl zeta_ty zeta_vl shift id
                  (funcomp shift zeta_ty) (funcomp id zeta_vl)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_vl shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_vl_ty (sigma : nat -> ty) (zeta_ty : nat -> nat)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (ren_ty zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_vl_ty zeta_ty)) (up_vl_ty sigma) x =
  up_vl_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty id (upRen_vl_ty zeta_ty) (funcomp id zeta_ty)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_ty id (funcomp id zeta_ty)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_ren_vl_vl (sigma : nat -> vl) (zeta_ty : nat -> nat)
  (zeta_vl : nat -> nat) (theta : nat -> vl)
  (Eq : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma x = theta x) :
  forall x,
  funcomp (ren_vl (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl))
    (up_vl_vl sigma) x =
  up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_vl id shift (upRen_vl_ty zeta_ty)
                (upRen_vl_vl zeta_vl) (funcomp id zeta_ty)
                (funcomp shift zeta_vl) (fun x => eq_refl) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_vl zeta_ty zeta_vl id shift
                      (funcomp id zeta_ty) (funcomp shift zeta_vl)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_vl id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : tm) {struct s} :
ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp
        (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal
        (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstRen_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (ren_ty zeta_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (ren_vl zeta_ty zeta_vl) sigma_vl x = theta_vl x)
(s : vl) {struct s} :
ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compSubstRen_ty sigma_ty zeta_ty theta_ty Eq_ty s0)
        (compSubstRen_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (upRen_vl_ty zeta_ty) (upRen_vl_vl zeta_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_ren_vl_ty _ _ _ Eq_ty)
           (up_subst_ren_vl_vl _ _ _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (compSubstRen_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (upRen_ty_ty zeta_ty) (upRen_ty_vl zeta_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_ren_ty_ty _ _ _ Eq_ty)
           (up_subst_ren_ty_vl _ _ _ _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma up_subst_subst_ty_vl (sigma : nat -> vl) (tau_ty : nat -> ty)
  (tau_vl : nat -> vl) (theta : nat -> vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_ty_ty tau_ty) (up_ty_vl tau_vl)) (up_ty_vl sigma) x =
  up_ty_vl theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_vl shift id (up_ty_ty tau_ty) (up_ty_vl tau_vl)
            (funcomp (up_ty_ty tau_ty) shift) (funcomp (up_ty_vl tau_vl) id)
            (fun x => eq_refl) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_vl tau_ty tau_vl shift id
                  (funcomp (ren_ty shift) tau_ty)
                  (funcomp (ren_vl shift id) tau_vl) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_vl shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_vl_ty (sigma : nat -> ty) (tau_ty : nat -> ty)
  (theta : nat -> ty)
  (Eq : forall x, funcomp (subst_ty tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_vl_ty tau_ty)) (up_vl_ty sigma) x = up_vl_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty id (up_vl_ty tau_ty) (funcomp (up_vl_ty tau_ty) id)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_ty id (funcomp (ren_ty id) tau_ty)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_ty id) (Eq n)))).
Qed.

Lemma up_subst_subst_vl_vl (sigma : nat -> vl) (tau_ty : nat -> ty)
  (tau_vl : nat -> vl) (theta : nat -> vl)
  (Eq : forall x, funcomp (subst_vl tau_ty tau_vl) sigma x = theta x) :
  forall x,
  funcomp (subst_vl (up_vl_ty tau_ty) (up_vl_vl tau_vl)) (up_vl_vl sigma) x =
  up_vl_vl theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_vl id shift (up_vl_ty tau_ty) (up_vl_vl tau_vl)
                (funcomp (up_vl_ty tau_ty) id)
                (funcomp (up_vl_vl tau_vl) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_vl tau_ty tau_vl id shift
                      (funcomp (ren_ty id) tau_ty)
                      (funcomp (ren_vl id shift) tau_vl) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_vl id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : tm) {struct s} :
subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
subst_tm theta_ty theta_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp
        (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
        (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal
        (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl theta_ty theta_vl
           Eq_ty Eq_vl s0)
  end
with compSubstSubst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(tau_ty : nat -> ty) (tau_vl : nat -> vl) (theta_ty : nat -> ty)
(theta_vl : nat -> vl)
(Eq_ty : forall x, funcomp (subst_ty tau_ty) sigma_ty x = theta_ty x)
(Eq_vl : forall x, funcomp (subst_vl tau_ty tau_vl) sigma_vl x = theta_vl x)
(s : vl) {struct s} :
subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
subst_vl theta_ty theta_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (compSubstSubst_ty sigma_ty tau_ty theta_ty Eq_ty s0)
        (compSubstSubst_tm (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (up_vl_ty tau_ty) (up_vl_vl tau_vl) (up_vl_ty theta_ty)
           (up_vl_vl theta_vl) (up_subst_subst_vl_ty _ _ _ Eq_ty)
           (up_subst_subst_vl_vl _ _ _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (compSubstSubst_tm (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (up_ty_ty tau_ty) (up_ty_vl tau_vl) (up_ty_ty theta_ty)
           (up_ty_vl theta_vl) (up_subst_subst_ty_ty _ _ _ Eq_ty)
           (up_subst_subst_ty_vl _ _ _ _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma renRen_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_vl (ren_tm xi_ty xi_vl s) =
  ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_ty zeta_vl) (ren_tm xi_ty xi_vl))
    (ren_tm (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl)).
Proof.
exact (fun s =>
       compRenRen_tm xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : vl) :
  ren_vl zeta_ty zeta_vl (ren_vl xi_ty xi_vl s) =
  ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl) s.
Proof.
exact (compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_vl_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_vl zeta_ty zeta_vl) (ren_vl xi_ty xi_vl))
    (ren_vl (funcomp zeta_ty xi_ty) (funcomp zeta_vl xi_vl)).
Proof.
exact (fun s =>
       compRenRen_vl xi_ty xi_vl zeta_ty zeta_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : tm) :
  subst_tm tau_ty tau_vl (ren_tm xi_ty xi_vl s) =
  subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_tm xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_ty tau_vl) (ren_tm xi_ty xi_vl))
    (subst_tm (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl)).
Proof.
exact (fun s =>
       compRenSubst_tm xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : vl) :
  subst_vl tau_ty tau_vl (ren_vl xi_ty xi_vl s) =
  subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl) s.
Proof.
exact (compRenSubst_vl xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_vl_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  pointwise_relation _ eq
    (funcomp (subst_vl tau_ty tau_vl) (ren_vl xi_ty xi_vl))
    (subst_vl (funcomp tau_ty xi_ty) (funcomp tau_vl xi_vl)).
Proof.
exact (fun s =>
       compRenSubst_vl xi_ty xi_vl tau_ty tau_vl _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : tm) :
  ren_tm zeta_ty zeta_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_ty zeta_vl) (subst_tm sigma_ty sigma_vl))
    (subst_tm (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl)).
Proof.
exact (fun s =>
       compSubstRen_tm sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) (s : vl) :
  ren_vl zeta_ty zeta_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
    (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl) s.
Proof.
exact (compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_vl_pointwise (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (zeta_ty : nat -> nat) (zeta_vl : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_vl zeta_ty zeta_vl) (subst_vl sigma_ty sigma_vl))
    (subst_vl (funcomp (ren_ty zeta_ty) sigma_ty)
       (funcomp (ren_vl zeta_ty zeta_vl) sigma_vl)).
Proof.
exact (fun s =>
       compSubstRen_vl sigma_ty sigma_vl zeta_ty zeta_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : tm) :
  subst_tm tau_ty tau_vl (subst_tm sigma_ty sigma_vl s) =
  subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_ty tau_vl) (subst_tm sigma_ty sigma_vl))
    (subst_tm (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl)).
Proof.
exact (fun s =>
       compSubstSubst_tm sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) (s : vl) :
  subst_vl tau_ty tau_vl (subst_vl sigma_ty sigma_vl s) =
  subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
    (funcomp (subst_vl tau_ty tau_vl) sigma_vl) s.
Proof.
exact (compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_vl_pointwise (sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
  (tau_ty : nat -> ty) (tau_vl : nat -> vl) :
  pointwise_relation _ eq
    (funcomp (subst_vl tau_ty tau_vl) (subst_vl sigma_ty sigma_vl))
    (subst_vl (funcomp (subst_ty tau_ty) sigma_ty)
       (funcomp (subst_vl tau_ty tau_vl) sigma_vl)).
Proof.
exact (fun s =>
       compSubstSubst_vl sigma_ty sigma_vl tau_ty tau_vl _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ty_vl (xi : nat -> nat) (sigma : nat -> vl)
  (Eq : forall x, funcomp (var_vl) xi x = sigma x) :
  forall x, funcomp (var_vl) (upRen_ty_vl xi) x = up_ty_vl sigma x.
Proof.
exact (fun n => ap (ren_vl shift id) (Eq n)).
Qed.

Lemma rinstInst_up_vl_ty (xi : nat -> nat) (sigma : nat -> ty)
  (Eq : forall x, funcomp (var_ty) xi x = sigma x) :
  forall x, funcomp (var_ty) (upRen_vl_ty xi) x = up_vl_ty sigma x.
Proof.
exact (fun n => ap (ren_ty id) (Eq n)).
Qed.

Lemma rinstInst_up_vl_vl (xi : nat -> nat) (sigma : nat -> vl)
  (Eq : forall x, funcomp (var_vl) xi x = sigma x) :
  forall x, funcomp (var_vl) (upRen_vl_vl xi) x = up_vl_vl sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_vl id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp (var_vl) xi_vl x = sigma_vl x) (s : tm) {struct s}
   :
ren_tm xi_ty xi_vl s = subst_tm sigma_ty sigma_vl s :=
  match s with
  | TmApp s0 s1 =>
      congr_TmApp
        (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s1)
  | TmTApp s0 s1 =>
      congr_TmTApp
        (rinst_inst_tm xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
        (rinst_inst_ty xi_ty sigma_ty Eq_ty s1)
  | TmVal s0 =>
      congr_TmVal
        (rinst_inst_vl xi_ty xi_vl sigma_ty sigma_vl Eq_ty Eq_vl s0)
  end
with rinst_inst_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat)
(sigma_ty : nat -> ty) (sigma_vl : nat -> vl)
(Eq_ty : forall x, funcomp (var_ty) xi_ty x = sigma_ty x)
(Eq_vl : forall x, funcomp (var_vl) xi_vl x = sigma_vl x) (s : vl) {struct s}
   :
ren_vl xi_ty xi_vl s = subst_vl sigma_ty sigma_vl s :=
  match s with
  | var_vl s0 => Eq_vl s0
  | TmAbs s0 s1 =>
      congr_TmAbs (rinst_inst_ty xi_ty sigma_ty Eq_ty s0)
        (rinst_inst_tm (upRen_vl_ty xi_ty) (upRen_vl_vl xi_vl)
           (up_vl_ty sigma_ty) (up_vl_vl sigma_vl)
           (rinstInst_up_vl_ty _ _ Eq_ty) (rinstInst_up_vl_vl _ _ Eq_vl) s1)
  | TmTAbs s0 =>
      congr_TmTAbs
        (rinst_inst_tm (upRen_ty_ty xi_ty) (upRen_ty_vl xi_vl)
           (up_ty_ty sigma_ty) (up_ty_vl sigma_vl)
           (rinstInst_up_ty_ty _ _ Eq_ty) (rinstInst_up_ty_vl _ _ Eq_vl) s0)
  | TmUnit => congr_TmUnit
  end.

Lemma rinstInst'_tm (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : tm) :
  ren_tm xi_ty xi_vl s =
  subst_tm (funcomp (var_ty) xi_ty) (funcomp (var_vl) xi_vl) s.
Proof.
exact (rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_tm_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  pointwise_relation _ eq (ren_tm xi_ty xi_vl)
    (subst_tm (funcomp (var_ty) xi_ty) (funcomp (var_vl) xi_vl)).
Proof.
exact (fun s =>
       rinst_inst_tm xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) (s : vl) :
  ren_vl xi_ty xi_vl s =
  subst_vl (funcomp (var_ty) xi_ty) (funcomp (var_vl) xi_vl) s.
Proof.
exact (rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_vl_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  pointwise_relation _ eq (ren_vl xi_ty xi_vl)
    (subst_vl (funcomp (var_ty) xi_ty) (funcomp (var_vl) xi_vl)).
Proof.
exact (fun s =>
       rinst_inst_vl xi_ty xi_vl _ _ (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm (s : tm) : subst_tm (var_ty) (var_vl) s = s.
Proof.
exact (idSubst_tm (var_ty) (var_vl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise :
  pointwise_relation _ eq (subst_tm (var_ty) (var_vl)) id.
Proof.
exact (fun s =>
       idSubst_tm (var_ty) (var_vl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_vl (s : vl) : subst_vl (var_ty) (var_vl) s = s.
Proof.
exact (idSubst_vl (var_ty) (var_vl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_vl_pointwise :
  pointwise_relation _ eq (subst_vl (var_ty) (var_vl)) id.
Proof.
exact (fun s =>
       idSubst_vl (var_ty) (var_vl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm (s : tm) : ren_tm id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma rinstId'_tm_pointwise : pointwise_relation _ eq (@ren_tm id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma rinstId'_vl (s : vl) : ren_vl id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_vl s) (rinstInst'_vl id id s)).
Qed.

Lemma rinstId'_vl_pointwise : pointwise_relation _ eq (@ren_vl id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_vl s) (rinstInst'_vl id id s)).
Qed.

Lemma varL'_vl (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) (x : nat) :
  subst_vl sigma_ty sigma_vl (var_vl x) = sigma_vl x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_vl_pointwise (sigma_ty : nat -> ty) (sigma_vl : nat -> vl) :
  pointwise_relation _ eq (funcomp (subst_vl sigma_ty sigma_vl) (var_vl))
    sigma_vl.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_vl (xi_ty : nat -> nat) (xi_vl : nat -> nat) (x : nat) :
  ren_vl xi_ty xi_vl (var_vl x) = var_vl (xi_vl x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_vl_pointwise (xi_ty : nat -> nat) (xi_vl : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_vl xi_ty xi_vl) (var_vl))
    (funcomp (var_vl) xi_vl).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_vl X Y :=
    up_vl : X -> Y.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

#[global] Instance Subst_vl : (Subst2 _ _ _ _) := @subst_vl.

#[global] Instance Subst_tm : (Subst2 _ _ _ _) := @subst_tm.

#[global] Instance Up_vl_vl : (Up_vl _ _) := @up_vl_vl.

#[global] Instance Up_vl_ty : (Up_ty _ _) := @up_vl_ty.

#[global] Instance Up_ty_vl : (Up_vl _ _) := @up_ty_vl.

#[global] Instance Ren_vl : (Ren2 _ _ _ _) := @ren_vl.

#[global] Instance Ren_tm : (Ren2 _ _ _ _) := @ren_tm.

#[global] Instance VarInstance_vl : (Var _ _) := @var_vl.

#[global] Instance Subst_ty : (Subst1 _ _ _) := @subst_ty.

#[global] Instance Up_ty_ty : (Up_ty _ _) := @up_ty_ty.

#[global] Instance Ren_ty : (Ren1 _ _ _) := @ren_ty.

#[global]
Instance VarInstance_ty : (Var _ _) := @var_ty.

Notation "s [ sigma_ty ; sigma_vl ]" := (subst_vl sigma_ty sigma_vl s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__vl" := up_vl (only printing)  : subst_scope.

Notation "s [ sigma_ty ; sigma_vl ]" := (subst_tm sigma_ty sigma_vl s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__vl" := up_vl_vl (only printing)  : subst_scope.

Notation "↑__ty" := up_vl_ty (only printing)  : subst_scope.

Notation "↑__vl" := up_ty_vl (only printing)  : subst_scope.

Notation "s ⟨ xi_ty ; xi_vl ⟩" := (ren_vl xi_ty xi_vl s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_ty ; xi_vl ⟩" := (ren_tm xi_ty xi_vl s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_vl ( at level 1, only printing)  : subst_scope.

Notation "x '__vl'" := (@ids _ _ VarInstance_vl x)
( at level 5, format "x __vl", only printing)  : subst_scope.

Notation "x '__vl'" := (var_vl x) ( at level 5, format "x __vl")  :
subst_scope.

Notation "s [ sigma_ty ]" := (subst_ty sigma_ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ty" := up_ty (only printing)  : subst_scope.

Notation "↑__ty" := up_ty_ty (only printing)  : subst_scope.

Notation "s ⟨ xi_ty ⟩" := (ren_ty xi_ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_ty ( at level 1, only printing)  : subst_scope.

Notation "x '__ty'" := (@ids _ _ VarInstance_ty x)
( at level 5, format "x __ty", only printing)  : subst_scope.

Notation "x '__ty'" := (var_ty x) ( at level 5, format "x __ty")  :
subst_scope.

#[global]
Instance subst_vl_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => subst_vl f_ty f_vl s = subst_vl g_ty g_vl t')
         (ext_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

#[global]
Instance subst_vl_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s =>
       ext_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s).
Qed.

#[global]
Instance subst_tm_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => subst_tm f_ty f_vl s = subst_tm g_ty g_vl t')
         (ext_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s =>
       ext_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s).
Qed.

#[global]
Instance ren_vl_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => ren_vl f_ty f_vl s = ren_vl g_ty g_vl t')
         (extRen_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

#[global]
Instance ren_vl_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_vl)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s =>
       extRen_vl f_ty f_vl g_ty g_vl Eq_ty Eq_vl s).
Qed.

#[global]
Instance ren_tm_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_ty f_vl s = ren_tm g_ty g_vl t')
         (extRen_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_tm)).
Proof.
exact (fun f_ty g_ty Eq_ty f_vl g_vl Eq_vl s =>
       extRen_tm f_ty f_vl g_ty g_vl Eq_ty Eq_vl s).
Qed.

#[global]
Instance subst_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => subst_ty f_ty s = subst_ty g_ty t')
         (ext_ty f_ty g_ty Eq_ty s) t Eq_st).
Qed.

#[global]
Instance subst_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s => ext_ty f_ty g_ty Eq_ty s).
Qed.

#[global]
Instance ren_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_ty s = ren_ty g_ty t')
         (extRen_ty f_ty g_ty Eq_ty s) t Eq_st).
Qed.

#[global]
Instance ren_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_ty)).
Proof.
exact (fun f_ty g_ty Eq_ty s => extRen_ty f_ty g_ty Eq_ty s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                      Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                      VarInstance_vl, Var, ids, Ren_tm, Ren2, ren2, Ren_vl,
                      Ren2, ren2, Up_ty_vl, Up_vl, up_vl, Up_vl_ty, Up_ty,
                      up_ty, Up_vl_vl, Up_vl, up_vl, Subst_tm, Subst2,
                      subst2, Subst_vl, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ty, Var, ids,
                                            Ren_ty, Ren1, ren1, Up_ty_ty,
                                            Up_ty, up_ty, Subst_ty, Subst1,
                                            subst1, VarInstance_vl, Var, ids,
                                            Ren_tm, Ren2, ren2, Ren_vl, Ren2,
                                            ren2, Up_ty_vl, Up_vl, up_vl,
                                            Up_vl_ty, Up_ty, up_ty, Up_vl_vl,
                                            Up_vl, up_vl, Subst_tm, Subst2,
                                            subst2, Subst_vl, Subst2, subst2
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_vl_pointwise
                 | progress setoid_rewrite substSubst_vl
                 | progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_vl_pointwise
                 | progress setoid_rewrite substRen_vl
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_vl_pointwise
                 | progress setoid_rewrite renSubst_vl
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_vl_pointwise
                 | progress setoid_rewrite renRen_vl
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite substSubst_ty_pointwise
                 | progress setoid_rewrite substSubst_ty
                 | progress setoid_rewrite substRen_ty_pointwise
                 | progress setoid_rewrite substRen_ty
                 | progress setoid_rewrite renSubst_ty_pointwise
                 | progress setoid_rewrite renSubst_ty
                 | progress setoid_rewrite renRen'_ty_pointwise
                 | progress setoid_rewrite renRen_ty
                 | progress setoid_rewrite varLRen'_vl_pointwise
                 | progress setoid_rewrite varLRen'_vl
                 | progress setoid_rewrite varL'_vl_pointwise
                 | progress setoid_rewrite varL'_vl
                 | progress setoid_rewrite rinstId'_vl_pointwise
                 | progress setoid_rewrite rinstId'_vl
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_vl_pointwise
                 | progress setoid_rewrite instId'_vl
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress setoid_rewrite varLRen'_ty_pointwise
                 | progress setoid_rewrite varLRen'_ty
                 | progress setoid_rewrite varL'_ty_pointwise
                 | progress setoid_rewrite varL'_ty
                 | progress setoid_rewrite rinstId'_ty_pointwise
                 | progress setoid_rewrite rinstId'_ty
                 | progress setoid_rewrite instId'_ty_pointwise
                 | progress setoid_rewrite instId'_ty
                 | progress
                    unfold up_vl_vl, up_vl_ty, up_ty_vl, upRen_vl_vl,
                     upRen_vl_ty, upRen_ty_vl, up_ty_ty, upRen_ty_ty, up_ren
                 | progress
                    cbn[subst_vl subst_tm ren_vl ren_tm subst_ty ren_ty]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ty, Var, ids, Ren_ty, Ren1, ren1,
                  Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst1, subst1,
                  VarInstance_vl, Var, ids, Ren_tm, Ren2, ren2, Ren_vl, Ren2,
                  ren2, Up_ty_vl, Up_vl, up_vl, Up_vl_ty, Up_ty, up_ty,
                  Up_vl_vl, Up_vl, up_vl, Subst_tm, Subst2, subst2, Subst_vl,
                  Subst2, subst2 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_vl_pointwise;
                  try setoid_rewrite rinstInst'_vl;
                  try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm;
                  try setoid_rewrite rinstInst'_ty_pointwise;
                  try setoid_rewrite rinstInst'_ty.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_vl_pointwise;
                  try setoid_rewrite_left rinstInst'_vl;
                  try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm;
                  try setoid_rewrite_left rinstInst'_ty_pointwise;
                  try setoid_rewrite_left rinstInst'_ty.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_vl: rewrite.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_vl: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

#[global] Hint Opaque subst_ty: rewrite.

#[global] Hint Opaque ren_ty: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

