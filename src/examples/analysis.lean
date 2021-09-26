import analysis.analytic.basic
import hp.tactic.hp_interactive
universe u

namespace examples

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
begin [hp]
  expand at T,
  unroll,
  trace_writeup,
  split,

end


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

example {A B : set X} : is_open A → is_open B → is_open (A ∪ B) :=
begin
  -- JCommelan's proof
  assume A_open B_open,
  assume y y_in_AB,
  wlog y_in_A : y ∈ A := y_in_AB using [A B],
  { show ∃ (ε : ℝ), (ε > 0) ∧ ∀ (x : X), dist x y < ε → x ∈ A ∪ B,
    obtain ⟨ε, ε_pos, h_ε⟩ : ∃ ε, (ε > 0) ∧ ∀ x, dist x y < ε → x ∈ A,
    by repeat { apply_assumption },
    use [ε, ε_pos],
    assume x dist_x_y_lt_ε,
    suffices x_in_A : x ∈ A, by finish,
    repeat { apply_assumption }, },
  { /- Proof obligation generated by `wlog` -/
    rw set.union_comm,
    repeat { apply_assumption }, },
end

example {A B : set X} : is_open A → is_open B → is_open (A ∪ B)
| oa ob y (or.inl h₁) := let ⟨ε, h₂, h₃⟩ := (oa y h₁) in ⟨ε, h₂, λ x h₄, or.inl $ h₃ x h₄⟩
| oa ob y (or.inr h₁) := let ⟨ε, h₂, h₃⟩ := (ob y h₁) in ⟨ε, h₂, λ x h₄, or.inr $ h₃ x h₄⟩

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

example {A B : set X} : is_open A → is_open B → is_open (A ∪ B) :=
begin
  assume A_open B_open,
  assume y : X,
  assume : y ∈ A ∪ B,
  cases ‹y ∈ A ∪ B›,
  { -- in the case that y ∈ A
    obtain ⟨ε, ε_pos, h_ε⟩ : ∃ ε, (ε > 0) ∧ ∀ x, dist x y < ε → x ∈ A,
      apply ‹is_open A›,
      apply ‹y ∈ A›,
    use [ε, ε_pos],
    assume x : X,
    assume : dist x y < ε,
    apply or.inl,
    finish,
  }, { -- in the case that y ∈ B
    obtain ⟨ε, ε_pos, h_ε⟩ : ∃ ε, (ε > 0) ∧ ∀ x, dist x y < ε → x ∈ B,
      apply ‹is_open B›,
      apply ‹y ∈ B›,
    use [ε, ε_pos],
    assume x : X,
    assume : dist x y < ε,
    apply or.inr,
    finish,
  }
end


theorem test
  {P : nat → nat → nat → Prop}
  {Q : nat → Prop}
  : (∀ x, ∃ y, ∀ z, P x y z → Q z)
    → (∀ x, ∃ y, ∀ z, P x y z → Q z) :=
begin [hp]
  unroll,
  apply H at T,
end



































/-
λ oA oB y yAB, or.rec_on yAB (λ yA, _) (λ yB, _)
λ oA oB y yAB, or.rec_on yAB (λ yA, Exists.intro _ $ and.intro _ $ λ x d, (or.inl _) ⊕ (or.inr _)⟩) (λ yB, _)
λ oA oB y yAB, or.rec_on yAB (λ yA, Exists.intro _ $ and.intro _ $ Exists.rec_on (oA y _) $ λ ε h, and.rec_on h $ λ _ h, λ x d, (or.inl (h _ _)) ⊕ (or.inr _)⟩) (λ yB, _)
So the question is; what makes the rec be added after the yA? Because we still have an mvar in the rec, which is going to use yA.
It might be the case that we haven't decided to perform cases on yAB yet... so how to make this work?
I don't think you can, which means that I am stuck with using classical.some and rewriting the pretty printer to make it work.
-/


example : is_open A → is_open B → is_open (A ∪ B) :=
λ oA oB y yAB, or.rec
  (λ yA, Exists.rec_on (oA y yA) (λ ε h, and.rec_on h (λ p h, Exists.intro ε $ and.intro p $ λ x d, or.inl $ h x d)))
  (λ yB, Exists.rec (λ ε ⟨p,h⟩, ⟨ε, p, λ x d, or.inr $ h x d⟩ ) (oB y yB))
  yAB

-- end
-- set_option pp.all true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true
example {A B : set X} : is_open A → is_open B → is_open (A ∪ B) :=
begin [hp]
  unroll,
  unroll at T₀, -- todo
  cases H₁,
  cosplit,

  expand H,
  apply H at T₀,
  apply H₂ at T₁,
  apply H₃ at T,

  trace_writeup,

  expand H₀,
  cosplit,
  apply H₀ at T₀,
  apply H₂ at T,
  apply H₄ at T,

end


end examples
/-
 at the end you should get α β > 0 and you need
 dist x y <
 -/