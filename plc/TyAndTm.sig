ty : Type
tm : Type
vl: Type

TyArrow : ty -> ty -> ty
TyForall : (bind ty in ty) -> ty
TyUnit : ty

TmApp : tm -> tm -> tm
TmTApp : tm -> ty -> tm
TmVal : vl -> tm

TmAbs : ty -> (bind vl in tm) -> vl
TmTAbs : (bind ty in tm) -> vl
TmUnit : vl