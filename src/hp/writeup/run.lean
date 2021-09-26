import basic hp.core

namespace hp.writeup

/-! Runs are the core 'realisation' format of a writeup. -/

/-- `run` does the job of `format` but for writeup text. -/
@[derive_prisms]
meta inductive run_item
| Text (s : string) : run_item
| Math (ts : option tactic_state) (e : expr) : run_item

namespace run_item
  meta def eq : run_item → run_item → bool
  | (Text s1) (Text s2) := s1 = s2
  | (Math _ e1) (Math _ e2) := e1 = e2
  | _ _ := ff

  meta def with_ts : tactic_state → run_item → run_item
  | ts (Math _ e) := Math (some ts) e
  | _ x := x

  meta def capitalise : run_item → run_item
  | (Text s) := Text $ string.capitalize s
  | t := t

  meta def pp : run_item → tactic format
  | (Text s) := tactic.pp s
  | (Math none e) := tactic.pp e
  | (Math (some ts) e) := tactic.with_state ts $ tactic.pp e

  meta def to_string : run_item → string
  | (Text s) := s
  | (Math _ e) := e.to_string

  open widget

  meta def view : run_item → tactic (list (widget.html empty))
  | (Text x) := pure $ [h "span" [cn "f4"] [@html.of_string empty x]]
  | (Math tso x) := do
        ts ← tactic.read,
        ts ← pure $ (ts <| tso),
        tactic.with_state ts $ (do
          ppx : string ← format.to_string <$> tactic.pp x,
          ppts : string ← format.to_string <$> tactic.pp ts,
          -- x ← (interactive_expression.mk interactive_expression.type_tooltip) x,
          pure [h "span" [cn "code f4"] [
            -- widget.simple_tooltip
            ppx
            -- ppts
            ]])

  meta instance : decidable_eq run_item := λ r1 r2, unchecked_cast $ eq r1 r2

end run_item
@[reducible]
meta def run := list run_item

namespace run

open run_item

meta instance string_to_run: has_coe string run := ⟨singleton ∘ run_item.Text⟩
meta instance expr_to_run: has_coe expr run := ⟨singleton ∘ (run_item.Math none)⟩
meta instance name_to_run: has_coe name run := ⟨singleton ∘ run_item.Text ∘ name.to_string⟩
meta instance : has_append run := ⟨list.append⟩
protected meta def append : run → run → run := (++)

meta def join : list run → run := list.join

meta def capitalise : run → run
| (t :: rest) := (run_item.capitalise t) :: rest
| [] := []

/-- Intersperse with commas. -/
meta def intercomma : list run → run
| rs := join $ list.intersperse "," $ rs

open widget

meta def starts_with_punctuation : run → bool
| (Text s :: _) := list.any (string.to_list ",.") (λ c, s.starts_with $ list.as_string [c])
| _ := ff

meta def is_nil : run_item → bool
| (Text "") := tt
| _ := ff

meta def starts_with_vowel : run → bool
| (Text s :: _) :=
  band
    -- [note] there is an exception! "a uniform limit" not "an uniform limit"!
    (bnot $ s.starts_with "uniform")
    (list.any (string.to_list "AEIOUaeiou") (λ c, s.starts_with $ list.as_string [c]))
| _ := ff

meta def item.to_string  : run_item → string
| (Math _ e) := expr.to_string e
| (Text s) := s

meta def emit {m : Type → Type} {α : Type} [monad m] [monad_writer α m] (k : run_item → m α) : run → m unit
| [] := pure ()
| (Text "" :: rest) := emit rest
| (x :: Text "" :: rest) := emit $ x :: rest
| (Text "a" :: rest) := do
  -- if the next word starts with a vowel then replace with `an`.

  t ← k $ if starts_with_vowel rest then Text "an" else Text "a",
  tell t,
  k (Text " ") >>= tell,
  emit rest
| (x :: rest) := do
  k x >>= tell,
  if starts_with_punctuation rest then emit rest else do
  k (Text " ") >>= tell,
  emit rest

meta def pp : run → tactic format
| r := prod.snd <$> writer_t.run (@emit (writer_t format tactic) _ writer_t.monad_of_append _
  (λ x, monad_lift $ run_item.pp x) r)

meta def to_string : run → string
| r := prod.snd <$> @writer_t.run string id unit (@emit _ _ writer_t.monad_of_append _
  (λ x, @has_monad_lift.monad_lift id _ (writer_t.lift_of_empty) _ $ x.to_string) r)

meta instance : has_to_tactic_format run := ⟨pp⟩
meta instance : has_to_string run := ⟨run.to_string⟩

meta def view : run → tactic (list (html empty))
| r := prod.snd <$> @writer_t.run (list (html empty)) tactic unit (@emit _ _ writer_t.monad_of_append _
  (λ x, @has_monad_lift.monad_lift _ _ (writer_t.lift_of_empty) _ $ x.view) r)

meta def item.mmap_exprs {m : Type → Type} [monad m] (f : telescope → expr → m expr) : telescope → run_item → m run_item
| Γ (Text a) := pure $ Text a
| Γ (Math ts a) := pure (Math ts) <*> f [] a

meta def mmap_exprs {m : Type → Type} [monad m] (f : telescope → expr → m expr) : telescope → run → m run
| Γ r := list.mmap (item.mmap_exprs f Γ) r

meta instance : assignable run := ⟨@mmap_exprs⟩

meta def mk_conj_list (comma conj : run) : list run → run
| [] := "TRUE"
| [x] := x
| [x,y] := x ++ conj ++ y
| (h :: t) := h ++ comma ++ mk_conj_list t

meta def andify : list run → run := mk_conj_list "," "and"

meta def orify : list run → run := mk_conj_list "," "or"

meta def Math : expr → run | e := [run_item.Math none e]

meta def Text : string → run := singleton ∘ run_item.Text

meta def with_ts : tactic_state → run → run | ts := list.map $ run_item.with_ts ts

end run

end hp.writeup