import .proper .hyp
namespace hp

/-- Tracking the reason why some proposition is true.
Input writeup type, shouldn't contain any writeup information and
should just track the salient parts of the derivation. -/
@[derive_prisms, derive decidable_eq, derive has_to_tactic_format]
meta inductive SourceReason
/-- "by assumption `h`" -/
| Assumption (h : (name × expr))
/-- Since x and y are prime. Use this if the source was expanded to something gnarly. -/
| Since (r : expr)
| Lemma (r : expr)
/-- Forward reasoning was used -/
| Forward (implication premiss : SourceReason)
| And (r1 r2 : SourceReason) : SourceReason
| ConjElim (conj : SourceReason) (index : nat)
/-- Don't bother writing the reason -/
| Omit
/-- "by expanding the definition of a given local" -/
| ExpandLocal (r : SourceReason) (src : hyp)
/-- "by setting x to be X and y to be Y" -/
| Setting (r : SourceReason) (setters : list (stub × expr))

meta def SourceReason.mmap_children {m} [monad m] (f : telescope → expr → m expr) (Γ : telescope) : SourceReason → m SourceReason
| (SourceReason.Assumption (n, e)) := pure SourceReason.Assumption <*> (pure prod.mk <*> pure n <*> (Γ ⍄ f $ e))
| (SourceReason.Since      h) := pure SourceReason.Since      <*> (Γ ⍄ f $ h)
| (SourceReason.Lemma      h) := pure SourceReason.Lemma      <*> (Γ ⍄ f $ h)
| (SourceReason.Forward    a b) := pure SourceReason.Forward <*> (SourceReason.mmap_children $ a) <*> (SourceReason.mmap_children $ b)
| (SourceReason.And        a b) := pure SourceReason.And <*> (SourceReason.mmap_children $ a) <*> (SourceReason.mmap_children $ b)
| (SourceReason.ConjElim   a index) := pure SourceReason.ConjElim <*> (SourceReason.mmap_children $ a) <*> pure index
| (SourceReason.Omit) := pure SourceReason.Omit
| (SourceReason.ExpandLocal r src) := pure SourceReason.ExpandLocal <*> (SourceReason.mmap_children $ r) <*> (Γ ⍄ f $ src)
| (SourceReason.Setting r setters) := pure SourceReason.Setting <*> (SourceReason.mmap_children $ r) <*> (Γ ⍄ f $ setters)

meta instance SR.asn : assignable SourceReason :=
⟨@SourceReason.mmap_children⟩

/-- A source is an expression that is salient to the proof state.
For example: assumptions, partially applied assumptions, exists elims. -/
@[derive_setters, derive decidable_eq]
meta structure source :=
(story : SourceReason := SourceReason.Omit)
(label : name)
(value : expr)
(type : expr)
(show_value : bool := ff)
(is_vuln : bool := ff)

namespace source

meta instance : has_to_tactic_format source := ⟨λ s,
  match s with
  | s := do
    l ← tactic.pp s.label,
    v ← tactic.pp s.value,
    pure $ l ++ " ← " ++ v
  end⟩

meta def of_hyp : hyp → source
| h := { story := SourceReason.Assumption (h.pretty_name, h.to_expr), label := h.pretty_name, value := h.to_expr, type := h.type }


meta instance : has_coe hyp source := ⟨of_hyp⟩

meta def to_expr : source → expr
| s := s.value

meta def to_binder : source → binder
| s := ⟨s.label, binder_info.default, s.type⟩

meta def of_expr : name → expr → tactic source
| n e := do
  y ← tactic.infer_type e,
  pure { label := n, value := e, type := y }

meta def of_exists : name → expr → tactic source
| n e := do
  y ← tactic.infer_type e,
  pure {label := n, story := SourceReason.Omit, value := e, type := y, show_value := ff}

meta def of_lemma : expr → tactic source
| e := do
  y ← tactic.infer_type e,
  f ← pure $ expr.get_app_fn e,
  pure {
    label := expr.const_name $ expr.get_app_fn e,
    story := SourceReason.Lemma f,
    type := y,
    value := e,
  }

meta def mmap_children {m} [monad m] (f : telescope → expr → m expr) : telescope → source → m source
| Γ s := do
  v ← Γ ⍄ f $ s.value,
  t ← Γ ⍄ f $ s.type,
  st ← Γ ⍄ f $ s.story,
  s ← pure {value := v, type := t, story := st, ..s},
  pure s

meta instance : assignable source := ⟨@mmap_children⟩
end source

end hp