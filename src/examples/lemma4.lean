import analysis.analytic.basic
import hp.tactic.hp_interactive
import examples.analysis
universe u

namespace examples

variables {X Y: Type} [met_space X] [met_space Y] {A B : set X}

example {A B : set X} : is_open A → is_open B → is_open (A ∩ B)
| oa ob y ⟨ha, hb⟩ :=
  let ⟨εa, h2a, h3a⟩ := oa y ha in
  let ⟨εb, h2b, h3b⟩ := ob y hb in
  ⟨ εa ⊓ εb
  , lt_min h2a h2b
  , λ x dh,
    ⟨ h3a _ $ lt_of_lt_of_le dh $ min_le_left  _ _
    , h3b _ $ lt_of_lt_of_le dh $ min_le_right _ _
    ⟩
  ⟩


example {A B : set X} : is_open A → is_open B → is_open (A ∩ B) :=
begin
  assume: is_open A,
  assume: is_open B,
  assume y : X,
  assume: y ∈ A ∩ B,
  show ∃ (ε : ℝ), ε > 0 ∧ ∀ (x : X), (dist x y < ε) → ((A ∩ B) x),
  cases ‹y ∈ A ∩ B›,
  obtain ⟨η, η_pos, h_η⟩ : ∃ η, (η > 0) ∧ ∀ x, dist x y < η → x ∈ A,
    apply ‹is_open A›, apply ‹y ∈ A›,
  obtain ⟨θ, θ_pos, h_θ⟩ : ∃ θ, (θ > 0) ∧ ∀ x, dist x y < θ → x ∈ B,
    apply ‹is_open B›, apply ‹y ∈ B›,
  let ε := min η θ,
  have : ε > 0,
    apply lt_min ‹η > 0› ‹θ > 0›,
  use [ε, ‹ε > 0›],
  assume x : X,
  assume : dist x y < ε,
  show x ∈ A ∩ B,
  have : dist x y < η,
    calc dist x y < min η θ : ‹dist x y < ε›
              ... ≤ η       : min_le_left _ _,
  have : dist x y < θ,
    calc dist x y < min η θ : ‹dist x y < ε›
              ... ≤ θ       : min_le_right _ _,
  split,
  show x ∈ A,
    apply h_η, apply ‹dist x y < η›,
  show x ∈ B,
    apply h_θ, apply ‹dist x y < θ›,
end

end examples