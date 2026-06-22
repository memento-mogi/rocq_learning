Ki : Type
Ty(TyVar) : Type
Tm(TmVar) : Type

KiStar : Ki
KiArr : Ki -> Ki -> Ki

TyAbs : Ki -> (bind Ty in Ty) -> Ty
TyApp : Ty -> Ty -> Ty
TyFun : Ty -> Ty -> Ty
TyForall : Ki -> (bind Ty in Ty) -> Ty
TyUnit : Ty


TmAbs : Ty -> (bind Tm in Tm) -> Tm
TmApp : Tm -> Tm -> Tm
TmTAbs : Ki -> (bind Ty in Tm) -> Tm
TmTApp : Tm -> Ty -> Tm
TmUnit : Tm
