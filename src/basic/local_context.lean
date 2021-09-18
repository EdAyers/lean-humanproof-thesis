import algebra

namespace local_context

meta def fold_decl {α :Type} (f : α → local_decl → α) : α → local_context → α
| a Γ := local_context.fold (λ a x, a <| f a <$> local_context.get_local_decl x.local_uniq_name Γ) a Γ

meta instance : has_lt local_context := ⟨λ a b, a ≤ b ∧ a ≠ b⟩

meta instance : has_bot local_context := ⟨∅⟩

meta instance uniq_name_mem : has_mem name local_context :=
⟨λ un Γ, option.is_some $ local_context.get_local un Γ⟩

meta instance unm_dec : ∀ (un : name) (Γ : local_context), decidable (un ∈ Γ) := by apply_instance

end local_context
