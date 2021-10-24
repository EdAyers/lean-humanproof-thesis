import analysis.analytic.basic
import hp.tactic.hp_interactive
universe u

namespace examples

lemma x_sub_x_union_y {α : Type} {A B : set α} : A ⊆ A ∪ B :=
λ a h, or.inl h

lemma y_sub_x_union_y {α : Type} {A B : set α} : B ⊆ A ∪ B :=
λ a h, or.inr h



class met_space (X : Type) extends has_dist X :=
(dist_self : ∀ x, dist x x = 0)
(dist_comm : ∀ x y, dist x y = dist y x)
(dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

attribute [classnoun "metric space"] met_space

open met_space

variables {X Y: Type} [met_space X] [met_space Y] {A B : set X}

def open_ball (ε : ℝ) (x : X) := {y | dist x y < ε}

def is_open (A : set X) : Prop :=
∀ (y : X), y ∈ A → ∃ (ε : ℝ), (ε > 0) ∧ ∀ (x : X), dist x y < ε → x ∈ A

@[relational_noun_predicate "uniform limit" "uniform limits" "of"]
def is_uniform_limit (f : ℕ → X → Y) (g : X → Y) :=
∀ (ε : ℝ), ε > 0 → ∃ (N : ℕ), ∀ (x : X), ∀ (n : ℕ), (n ≥ N) → dist (f n x) (g x) < ε

@[adjective "continuous"]
def continuous (f : X → Y) :=
∀ (x : X), ∀ (ε : ℝ), (ε > 0) → ∃ (δ : ℝ), (δ > 0) ∧ ∀ (y : X), dist x y < δ → dist (f x) (f y) < ε

@[relational_noun "sequence" "sequences" "of"]
def sequence (X : Type) := ℕ → X

lemma dist_helper {ε η θ}
  {x y z : X}
  (h₁ : dist x y < η)
  (h₂ : dist y z < θ)
  (h₃ : η + θ ≤ ε)
  : dist x z < ε :=
calc _ ≤ dist x y + dist y z : dist_triangle _ _ _
   ... < η + θ               : add_lt_add h₁ h₂
   ... ≤ ε                   : h₃

example (f : sequence (X → Y)) (g : X → Y)
  (h₁ : is_uniform_limit f g)
  (h₂ : ∀ n, continuous (f n)) : continuous g :=
begin
  assume (x : X) (ε : ℝ) (ε_pos : ε > 0),
  have h₄ : ε / 3 > 0,
    show ε / 3 > 0, apply div_pos ε_pos,
    show 0 < (3 : ℝ), norm_num,
  obtain ⟨N, h₅⟩ : ∃ N, ∀ (x : X) (n : ℕ), n ≥ N → dist (f n x) (g x) < ε / 3,
    apply h₁ (ε / 3) h₄,
  obtain ⟨δ, δ_pos, h₆⟩ : ∃ δ, δ > 0 ∧ ∀ y, dist x y < δ → dist (f N x) (f N y) < ε / 3,
    apply h₂ N x (ε / 3) h₄,
  existsi δ,
  existsi δ_pos,
  assume (y : X) (h₃ : dist x y < δ),
  show dist (g x) (g y) < ε,
  apply dist_helper,
  calc dist (g x) (f N x) = dist (f N x) (g x) : by rw examples.met_space.dist_comm
                      ... < ε / 3 : by apply h₅ x N (le_refl N),
  show dist (f N x) (g y) < (ε / 3 + ε / 3),
    apply dist_helper,
  show dist (f N x) (f N y) < ε / 3,
    apply h₆ y h₃,
  show dist (f N y) (g y) < ε / 3,
    apply h₅ y N (le_refl N),
  show ε / 3 + ε / 3 ≤ ε / 3 + ε / 3,
    apply le_refl,
  show ε / 3 + (ε / 3 + ε / 3) ≤ ε,
    apply le_of_eq,
    show ε / 3 + (ε / 3 + ε / 3) = ε, by ring
end

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




end examples