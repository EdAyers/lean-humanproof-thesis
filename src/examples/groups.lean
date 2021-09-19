import group_theory.group_action group_theory.coset
import hp.tactic.hp_interactive

namespace examples

section
variables {G H I : Type} [group G] [group H] [group I]
variables {f : G → H} {g : H → I}

def is_hom (f : G → H) := ∀ (x y : G), f (x * y) = f x * f y
attribute [class] is_hom
variables [is_hom f]
lemma is_hom.one : f 1 = 1 :=
begin
  apply mul_right_eq_self.1,
  show (f 1) * (f 1) = (f 1),
  rw ←‹is_hom f›,
  simp,
end

lemma is_hom.inv (f : G → H) [is_hom f] {x} : f (x⁻¹) = (f x)⁻¹ :=
begin
  have : f x * f (x⁻¹) = f x * (f x)⁻¹,
  rw ←‹is_hom f›, simp, apply is_hom.one,
  exact mul_left_cancel this
end

example : is_hom f → is_hom g → is_hom (g ∘ f) :=
begin
  intros hf hg x y,
  simp,
  rewrite [hf,hg]
end

example : is_hom f → is_hom g → is_hom (g ∘ f) :=
begin
  -- intros, simp, rw [‹is_hom f›, ‹is_hom g›],
  assume : is_hom f,
  assume : is_hom g,
  assume (x y : G),
  calc g (f (x * y)) = g (f x * f y)         : by rewrite ‹is_hom f›
                 ... = (g (f x)) * (g (f y)) : by rewrite ‹is_hom g›,
end

-- def kernel (f : G → H) [is_hom f ] := {g : G | f g = 1}

def kernel (f : G → H) [h₁ : is_hom f] : subgroup G :=
begin
  refine {carrier := {g : G | f g = 1}, ..},
  apply is_hom.one,
    show ∀ (a b : G) (ha : f a = 1) (hb : f b = 1), f (a * b) = 1,
    intros,
    rw [‹is_hom f›, ha, hb],
    simp,
  show ∀ (a : G) (ha : f a = 1), f a⁻¹ = 1,
  intros,
  rw (is_hom.inv f),
  rw ha,
  simp
end

example (f : G → H) [h₁ : is_hom f] : subgroup.normal (kernel f) :=
begin
  split,
  show ∀ (k : G) (h₂ : k ∈ kernel f) (g : G), (f (g * k * g⁻¹) = 1),
  intros,
  have h₃ : f k = 1, from ‹k ∈ kernel f›,
  calc f (g * k * g⁻¹) = f (g * k) * f g⁻¹ : by rewrite ‹is_hom f›
                   ... = f g * f k * f g⁻¹ : by rewrite ‹is_hom f›
                   ... = f g * 1 * f g⁻¹   : by rewrite h₃
                   ... = f g * 1 * (f g)⁻¹ : by rewrite (is_hom.inv f)
                   ... = 1                 : by simp
end

end

section

variables {G : Type} [group G]

lemma test_1 (x : G) : x = x :=
begin [hp]

end

variables {H : subgroup G} {a b : G}

lemma mem_own_left_coset : a ∈ left_coset a H :=
begin [hp]

  -- show ∃ (h : G), (h ∈ H) ∧ a * h = a,
  -- use (1 : G),
  -- split,
  -- show (1 : G) ∈ H,
  --   apply subgroup.one_mem,
  -- show a * (1 : G) = a,
  --   simp
end

theorem G1 : (left_coset a H = left_coset b H) ↔ b⁻¹ * a ∈ H :=
begin
  split,
  { assume he : left_coset a H = left_coset b H,
    obtain ⟨h,hH,p⟩ : ∃ (h : G), h ∈ H ∧ b * h = a,
      have : a ∈ left_coset a H,
        apply mem_own_left_coset,
      have : a ∈ left_coset b H,
        rw he at this,
        apply this,
      apply this,
    have : b⁻¹ * a = h,
      rw ← p, simp,
    rw this,
    assumption,
  },
  { intro H1,
    apply set.eq_of_subset_of_subset,
    { rintros g ⟨h,hH,e⟩,
      refine ⟨(b⁻¹ * a) * h,_,_⟩,
      apply subgroup.mul_mem, apply H1, apply hH,
      simp at e,
      rw [mul_assoc, e], simp,
    },
    { rintros g ⟨h,hH,e⟩,
      refine ⟨_,_,_⟩,
      rotate 2,
      rw ← e,
      simp,
      apply mul_eq_of_eq_inv_mul,
      refl,
      rw [←mul_assoc],
      apply subgroup.mul_mem,
      refine (subgroup.inv_mem_iff H).1 _,
      simp, apply H1, apply hH
    }
  }
end

/- Every kernel is a normal subgroup -/

-- def kernel {H G : Type} [group H] [group G] (f : H → G) [group_hom]

-- example :

-- /- This one is too classical.

--  -/
-- -- example : (¬ disjoint (left_coset a H) (left_coset b H)) → left_coset a H = left_coset b H :=
-- -- begin
-- --   intros h₁,
-- --   refine (G1 ).2 _,
-- --   apply set.disjoint.union_left
-- -- end

end


end examples