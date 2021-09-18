namespace tactic.unsafe.type_context
open tactic.unsafe

meta def returnopt {α} : option α → type_context α
| (some a) := pure a
| (none) := failure

meta def is_not_unassigned_mvar : expr → type_context bool
| e@(expr.mvar _ _ _) := is_assigned e
| _ := pure tt

end tactic.unsafe.type_context