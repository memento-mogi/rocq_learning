From PLC Require Import PLC.

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
  | TmVar x => return t
  | <{ \x:T, t1 }> => return t
  | <{ t1 t2 }> =>
      t1' <- eval_tm t1 ;;
      t2' <- eval_tm t1 ;;
      match t1' with
      | <{ \x:T, t11' }> => return <{ [x:=t2'] t11' }>
      | _ => fail
      end
  | <{ \\X, t1 }> => return t
  | <{ t1 [T] }> =>
      t1' <- eval_tm t1 ;;
      match t1' with 
      | <{ \\X, t11' }> => return <{ [[X:=T]] t11' }>
      | _ => fail
      end
  | <{ unit }> => return t
  end
.
