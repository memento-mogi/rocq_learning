ty : Type
tm : Type

TyArrow : ty -> ty -> ty
TyForall : (bind ty in ty) -> ty
TyUnit : ty

TmApp : tm -> tm -> tm
TmTApp : tm -> ty -> tm
TmAbs : ty -> (bind tm in tm) -> tm
TmTAbs : (bind ty in tm) -> tm
TmUnit : tm