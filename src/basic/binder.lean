/- © E.W.Ayers 2019 -/
import meta.expr

def binder_info.is_explicit : binder_info → bool
| binder_info.default := tt
| _ := ff

namespace binder

meta def push_local : binder → tactic.unsafe.type_context expr
| ⟨n, bi, y⟩ := tactic.unsafe.type_context.push_local n y bi

meta def to_mvar : binder → tactic.unsafe.type_context expr
| ⟨n, bi, y⟩ := tactic.unsafe.type_context.mk_mvar n y

meta def of_mvar : expr → binder
| (expr.mvar un pn y) := ⟨pn, binder_info.default, y⟩
| _ := inhabited.default _

meta def to_dummy_mvar : binder → expr
| ⟨n, b, y⟩ := expr.mvar n n y

meta def to_pi : binder → expr → expr
| ⟨n, i, y⟩ e := expr.pi n i y e

meta def to_lam : binder → expr → expr
| ⟨n, i, y⟩ e := expr.lam n i y e

meta def mk_local : binder → tactic expr
| ⟨n, i, y⟩ := tactic.mk_local' n i y

meta def is_explicit : binder → bool
| ⟨n, i, y⟩ := i.is_explicit

meta def mk_default : _root_.name → expr → binder
| n y := ⟨n,binder_info.default,y⟩

end binder
