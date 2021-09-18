import .list_zipper

def undoable_t (σ: Type) (t : Type → Type) := state_t (list.zipper σ) t
variables {σ : Type} {t : Type → Type} [monad t] [monad_state σ t]
namespace undoable_t
section
local attribute [reducible] undoable_t
instance : monad (undoable_t σ t) := by apply_instance
instance : has_monad_lift t (undoable_t σ t) := by apply_instance
def save : undoable_t σ t unit := do
  c : σ ← monad_lift $ @get σ t _ _,
  ⟨l,r⟩ ← state_t.get,
  state_t.put ⟨c::l,[]⟩,
  pure ()
def can_undo : undoable_t σ t bool := do
  ⟨l,r⟩ ← state_t.get,
  pure $ bnot $ list.empty l
def can_redo : undoable_t σ t bool := do
  ⟨l,r⟩ ← state_t.get,
  pure $ bnot $ list.empty r
def undo : undoable_t σ t unit := do
  ⟨h::l,r⟩ ← state_t.get | pure (),
  put ⟨l,h::r⟩,
  monad_lift $ @put σ t _ _ h
def redo : undoable_t σ t unit := do
  ⟨l,h::r⟩ ← state_t.get | pure (),
  put ⟨h::l,r⟩,
  monad_lift $ @put σ t _ _ h
instance : monad_state σ (undoable_t σ t) := {lift := λ α s, do
  c : σ ← monad_lift $ @get σ t _ _,
  ⟨a,c⟩ ← pure $ state_t.run s c,
  monad_lift $ @put σ t _ _ c,
  pure a
}
instance [alternative t] : alternative (undoable_t σ t) := by apply_instance
end
end undoable_t