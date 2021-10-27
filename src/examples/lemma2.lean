import analysis.analytic.basic
import hp.tactic.hp_interactive
import examples.analysis
universe u

namespace examples

variables {X Y: Type} [met_space X] [met_space Y] {A B : set X}

-- term-mode proof
example {A B : set X} : is_open A → is_open B → is_open (A ∪ B)
| oa ob y (or.inl h₁) := let ⟨ε, h₂, h₃⟩ := (oa y h₁) in ⟨ε, h₂, λ x h₄, or.inl $ h₃ x h₄⟩
| oa ob y (or.inr h₁) := let ⟨ε, h₂, h₃⟩ := (ob y h₁) in ⟨ε, h₂, λ x h₄, or.inr $ h₃ x h₄⟩

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


-- humanproof writeup
example {A B : set X} : is_open A → is_open B → is_open (A ∪ B) :=
begin [hp]
  unroll,
  unroll at T₁,
  cases H₁,

  apply (@x_sub_x_union_y) at T₁,
  apply H at T₂,
  apply H₂ at T₃,
  apply H₃,

  apply (@y_sub_x_union_y) at T₁,

  apply H₀ at T₄,
  apply H₂ at T₅,
  apply H₄,

end

end examples