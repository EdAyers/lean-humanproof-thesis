import .widget .interaction_monad .basic

universes u

open widget


meta def interaction_component (σ π α: Type) := (σ × π) ⇨ α

open interaction_monad
open interaction_monad.result

namespace interaction_component

variables {m : Type → Type} {τ π α β ρ σ : Type} [monad m] [monad_run (interaction_monad τ) m]

meta def of_component : component π α → interaction_component τ π α := component.map_props prod.snd

/-- Swallows errors for now. -/
meta def filter_map_action (f : π → α → m (option β)) : interaction_component τ π α → interaction_component τ π β :=
component.filter_map_action (λ ⟨t,p⟩ a, interaction_monad.run_simple (run $ f p a) t >>= λ ⟨a,_⟩, a)

meta def bind_props [inhabited ρ] (f : π → m ρ) : interaction_component τ ρ α → interaction_component τ π α :=
component.map_props (λ ⟨t,p⟩, (t,inhabited.default ρ) <| (interaction_monad.run_simple (run $ f p) t >>= λ ⟨a,t⟩, some (t,a)))

meta def map_props (f : π → ρ) : interaction_component τ ρ α → interaction_component τ π α :=
component.map_props (λ ⟨t,p⟩, (t, f p))

-- meta def lift_state (lift : Π {α}, (interaction_monad ρ α) → (interaction_monad τ α))
-- : interaction_component m π α → interaction_component m π α
-- | ⟨hp_state,σ,i,u,v⟩ := interaction_component.mk hp_state σ (λ p s, lift $ i p s) (λ p s b, lift $ u p s b) (λ p s, lift $ v p s)

variables [has_should_update τ] [has_should_update π]

meta def to_component  : interaction_component τ π α → component (τ × π) α
| i := i

-- /- Add a state loop that manages the tactic component state.-/
--   component.with_should_update (should_update)
--   $ component.with_state
--     α τ _
--   $ _
-- | (interaction_component.mk β σ i u v) :=
--   @component.mk
--     (τ × π) α β (result τ σ)
--     (λ ⟨t,p⟩ s b,
--       match s with
--       | (success s _) := let d := run $ u p s b in let x := d t in prod.mk (prod.fst <$> x) (x.get >>= prod.snd)
--       | x := prod.mk x $ none
--       end)
--     (λ ⟨t,p⟩ s,
--       match s with
--       | (success s _) :=
--         let d := run $ v p s in
--         match d t with
--         | (success h _) := h
--         | (exception msg pos s) := ["rendering tactic failed: ", show_html msg]
--         end
--       | (exception msg pos s) := ["errored: ", show_html msg]
--       end
--     )
--     (λ ⟨t1,p1⟩ ⟨t2,p2⟩, ¬(should_update p1 p2 || should_update t1 t2))

meta def run_view (view : π → (m $ list $ html α)) : π → τ →  list (html α)
| p t :=
  let x := run $ view p in
  match x t with
  | (success h _) := h
  | (exception msg pos t) := ["rendering tactic failed: ", show_html msg]
  end

/-- Keeps the monad state. -/
meta def simple_persist_monad_component_core
  (on_props_change : π → π → m unit)
  (update : π → β → m (option α))
  (view : π → m (list (html β))) : component (τ × π) α := -- [todo] idea: add an 'on error' case for when the monad fails.
  component.with_should_update should_update
  $ component.with_state
    β
    (result τ unit)
    (λ ⟨t,p⟩, result.success () t)
    (λ ⟨_,p₀⟩ ⟨_,p₁⟩ r, let x := run $ on_props_change p₀ p₁ in x r.state)
    (λ ⟨_,p⟩ r b, let x := run $ update p b, r := x r.state in (r.map (λ _, ()), option.join $ r.get))
  $ component.pure (λ ⟨r,_,p⟩,
    match r with
    | (success () t) := run_view view p t
    | (exception msg pos t) := ["monad failed: ", show_html msg]
    end
  )

meta def simple_persist_monad_component
  (init : τ) (on_props_change : π → π → m unit) (update : π → β → m (option α)) (view : π → m (list (html β))) : component π α :=
  component.map_props (λ p, (init, p))
  $ simple_persist_monad_component_core on_props_change update view

meta instance : has_coe_to_fun (interaction_component τ π α) :=
⟨ λ c, π → interaction_monad τ (html α)
, λ c p t, success (html.of_component (t,p) c.to_component) t⟩

meta def stateless (view : π → m (list (html α))): interaction_component τ π α :=
component.with_should_update should_update
$ component.pure (λ ⟨t,p⟩, run_view view p t)

end interaction_component