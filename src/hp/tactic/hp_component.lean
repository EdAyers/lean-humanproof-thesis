import .hp hp.writeup basic
universes u

open widget
open tactic.unsafe
open tactic

namespace hp

meta def rc (π α) := interaction_component hp_state π α

meta instance : has_should_update hp_state :=
{su := λ rs₁ rs₂, (rs₁.b ≠ rs₂.b)}

variables {π α : Type} [has_should_update π]

-- meta instance tc_coe_rc: has_coe (tc π α) (rc π α) :=
-- ⟨λ c, interaction_component.bind_props (λ p, do ts ← hp_state.ts <$> get, pure (ts,p)) $ interaction_component.of_component c⟩

meta def rc.to_component : rc π α → component (hp_state × π) α
| r := interaction_component.to_component r

meta instance rc_fun : has_coe_to_fun (rc π α) :=
⟨ λ c, π → hp (html α)
, λ c p, do rs ← get, pure $ html.of_component (rs, p) c.to_component
⟩

meta def rc.stateless {π α} [has_should_update π] (view : π → hp (list (html α))): rc π α :=
interaction_component.stateless (λ p, view p)

/-- An rc for rendering as a secondary tactic type.
The main example being subtasks. -/
meta def inner_component := html (hp_state)

meta inductive rc.action : Type
| new_state (rs : hp_state)
| interactive_inner_tactic (rc : inner_component)

end hp