/- Monadic widgets for transforming trees and lists. -/
import .control

variables {α β γ δ σ τ ω : Type} {m : Type → Type} [monad m]

/-- Just a simple parser for lists of things. More for abstraction than efficiency. -/
def list_parser (α : Type) (m : Type → Type) : Type → Type :=
state_t (list α) $ except_t string $ m

namespace list_parser
local attribute [reducible] list_parser
local notation `P ` := list_parser α m
instance : monad P := by apply_instance
instance : monad_except string P := by apply_instance
instance : alternative P := by apply_instance
instance : monad_state (list α) P := by apply_instance
instance : has_monad_lift_t m P := by apply_instance

def lift_m : m β → P β := @monad_lift m (P) _ _

def peek : P α := do
  (h::t) ← get | throw "expecting token but got eof",
  pure h

def take : P α := do
  (h::t) ← get | throw "expecting token but got eof",
  put (t),
  pure h

def test (f : α → option γ) : P γ := do
  a ← take,
  option.rec_on (f a) (throw "test failed") pure

def mtest [alternative m] (f : α → m γ) : P γ := do
  a ← take,
  o ← monad_lift $ ((some <$> f a) <|> pure none),
  option.rec_on o (throw "test failed") pure

def eof : P unit := do
  ([]) ← state_t.get | failure,
  pure ()

def run : P γ → list α → m (except string (γ × list α))
| x init := except_t.run $ state_t.run x $ init

/-- Zero or more occurrences of the parser pattern.
Get rid of the meta by demanding that item consumes at least one item in the list.
 -/
meta def many (item : P γ) : P (list γ) :=
(do
  p ← item,
  rest ← many,
  pure $ p :: rest
) <|> pure []

meta def one_or_more (item : P γ) : P (list γ) := do
  head ← item,
  rest ← many item,
  pure $ head :: rest

def fence (lb : P unit) (item : P γ) (rb : P unit) :=
lb *> item <* rb

meta def intersperse (item : P γ) (separator : P unit) : P (list γ) :=
(pure list.cons <*> item <*> many (separator *> item)) <|> pure []

def returnopt : option γ → P γ
| (some x) := pure x | none := failure

end list_parser
