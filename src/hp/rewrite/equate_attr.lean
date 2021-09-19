import .rule_table
import algebra

namespace hp

meta def equate_user_attr : user_attribute rule_table unit :=
{ name := `equate
, descr := "add the given lemma to equate's rule-table."
, cache_cfg :=
    { mk_cache := rule_table.of_names
    , dependencies := []
    }
}

run_cmd attribute.register `hp.equate_user_attr

meta def get_equate_rule_table : tactic rule_table :=
    user_attribute.get_cache equate_user_attr

-- attribute [equate] and_comm
attribute [equate] mul_assoc
attribute [equate] mul_comm
attribute [equate] mul_left_inv
attribute [equate] mul_right_inv
attribute [equate] one_mul
attribute [equate] mul_one
attribute [equate] inv_inv
@[equate] lemma mul_inv {G:Type*} [group G] {a b : G} : (a * b) ⁻¹ = b⁻¹ * a⁻¹ := by simp
-- attribute [equate] pow_succ
-- attribute [equate] pow_zero
@[equate] lemma nat_succ_is_nat_plus_one {n} : nat.succ n = n + 1 := rfl

attribute [equate] add_assoc
attribute [equate] add_left_neg
attribute [equate] add_right_neg
attribute [equate] zero_add
attribute [equate] add_zero
attribute [equate] add_comm
attribute [equate] neg_add
attribute [equate] neg_neg

@[equate] lemma one_plus_one_is_two : 1 + 1 = 2 := rfl

attribute [equate] sub_self
attribute [equate] sub_eq_add_neg
attribute [equate] zero_sub
attribute [equate] sub_zero
attribute [equate] sub_neg_eq_add

attribute [equate] right_distrib
attribute [equate] mul_zero
attribute [equate] zero_mul
attribute [equate] neg_mul_eq_neg_mul
attribute [equate] neg_mul_eq_mul_neg
attribute [equate] neg_mul_neg
attribute [equate] neg_mul_comm
attribute [equate] mul_sub_left_distrib
attribute [equate] mul_sub_right_distrib

@[equate] lemma comp_def {α β γ : Type*} {f : α → β} {g : β → γ} {x : α} : (g ∘ f) x = g (f x) := rfl


/- Some equalities for set theory. -/
namespace set_rules
    universe u
    variables {α : Type u} {A B C : set α}
    def ext : (∀ a, a ∈ A ↔ a ∈ B) → A = B := begin intro h, funext, rw <-iff_eq_eq, apply h x end
    @[equate] def A1 : A \ B = A ∩ (Bᶜ) := begin refl end
    @[equate] def A2 : ( B ∩ C )ᶜ = Bᶜ ∪ Cᶜ := ext $ λ a, ⟨λ h, classical.by_cases (λ aB, classical.by_cases (λ aC, absurd (and.intro aB aC) h) or.inr ) or.inl,λ h, or.cases_on h (λ h ⟨ab,_⟩, absurd ab h) (λ h ⟨_,ac⟩, absurd ac h)⟩
    -- @[equate] def A3 :  - ( B ∪ C ) = - B ∩ - C := ext $ λ a, ⟨λ h, ⟨h ∘ or.inl,h ∘ or.inr⟩, λ ⟨x,y⟩ h₂, or.cases_on h₂ x y⟩
    attribute [irreducible] set.compl
    @[equate] def A4 : B ∩ C = C ∩ B := ext $ λ a, ⟨and.swap,and.swap⟩
    -- @[equate] def A5 : B ∪ C = C ∪ B := ext $ λ a, ⟨or.swap, or.swap⟩
    -- @[equate] def A6 : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := ext $ λ a, ⟨λ h, or.cases_on h (λ h, ⟨or.inl h, or.inl h⟩) (λ ⟨b,c⟩, ⟨or.inr b, or.inr c⟩),λ ⟨ab,ac⟩, or.cases_on ab or.inl $ λ b, or.cases_on ac or.inl $ λ c, or.inr ⟨b,c⟩⟩ -- [NOTE] use mathlib, don't be macochistic.
    -- @[equate] def A7 : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := ext $ λ a, ⟨λ ⟨a,bc⟩,or.cases_on bc (λ b, or.inl ⟨a,b⟩) (λ c, or.inr ⟨a,c⟩), λ h, or.cases_on h (λ ⟨a,b⟩, ⟨a,or.inl b⟩) (λ ⟨a,c⟩, ⟨a,or.inr c⟩)⟩
    -- @[equate] def A8 : (A ∩ B) ∩ C = A ∩ (B ∩ C)  := ext $ λ a, and.assoc
    -- @[equate] def A9 : (A ∪ B) ∪ C = A ∪ (B ∪ C)  := ext $ λ a, or.assoc
    -- @[equate] def A10 : A ∪ ∅ = A := ext $ λ _, or_false _
    -- @[equate] def A11 : A ∩ ∅ = ∅ := ext $ λ _, and_false _
    -- @[equate] def A12 : A ∪ set.univ = set.univ := ext $ λ _, or_true _
    -- @[equate] def A13 : A ∩ set.univ = A := ext $ λ _, and_true _
    -- @[equate] def A14 : A ∩ A = A := ext $ λ a, ⟨λ ⟨x,y⟩, x, λ x, ⟨x,x⟩⟩
    -- @[equate] def A15 : A ∪ A = A := ext $ λ a, ⟨λ xy, or.rec_on xy id id, or.inl⟩
    -- @[equate] def A16 : A \ A = ∅ := ext $ λ a, ⟨λ ⟨x,y⟩, y x, λ x, false.rec_on _ x⟩
end set_rules

end hp