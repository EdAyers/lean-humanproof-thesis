namespace interaction_monad

namespace result

  variables {σ α β : Type}

  protected meta def map (f : α → β) : interaction_monad.result σ α → interaction_monad.result σ β
  | (success b s) := success (f b) s
  | (exception m p s) := exception m p s

  meta def map_state {τ : Type} (f : σ → τ) : result σ α → result τ α
  | (success a s) := success a (f s)
  | (exception m p s) := exception m p (f s)

  meta def state : result σ α → σ
  | (success b s) := s
  | (exception m p s) := s

  meta def get : result σ α → option α
  | (success b _) := some b
  | (exception _ _ _) := none

  meta def as_success : result σ α → option (α × σ)
  | (success b s) := some (b,s)
  | _ := none

  meta def as_exception : result σ α → option (option (unit → format) × option pos × σ)
  | (success b s) := none
  | (exception m p s) := (m,p,s)

  meta def as_except : result σ α → except (option (unit → format) × option pos) α
  | (success b s) := except.ok b
  | (exception m p s) := except.error $ (m, p)

  meta instance {σ} : functor (result σ) := {map := @result.map σ}

end result

meta instance {σ} : monad_state σ (interaction_monad σ) :=
{lift := λ α s x, let ⟨a,x⟩ := s.run x in result.success a x }

meta instance {σ} : alternative (interaction_monad σ) :=
{ failure := @interaction_monad.failed _,
  orelse  := @interaction_monad_orelse _ }

meta def lift_of_lens {τ σ} (get : τ → σ) (put : σ → τ → τ)
  : Π {α}, (interaction_monad σ α) → (interaction_monad τ α)
| α s t := result.map_state (function.swap put $ t) $ s $ get t

meta def has_monad_lift_of_lens {τ σ} (get : τ → σ) (put : σ → τ → τ)
  : has_monad_lift (interaction_monad σ) (interaction_monad τ) :=
⟨λ α, lift_of_lens get put⟩

/-- Perform the given tactic but then just keep the result and throw away the state. -/
meta def hypothetically {σ α} : interaction_monad σ α → interaction_monad σ α
| t s := result.map_state (λ _, s) $ t s

meta def get_state_after {σ α}: interaction_monad σ α → interaction_monad σ σ
| t s := let s := result.state $ t s in result.success s s

meta def return_except {ε σ α} [has_to_format ε] : except ε α → interaction_monad σ α
| (except.ok a) := pure a
| (except.error e) := interaction_monad.fail e

meta def run_simple {σ α}: interaction_monad σ α → σ → option (α × σ)
| m s := result.as_success $ m s

/-- If the given tactic fails, trace the failure message. -/
meta def trace_fail {σ α} (tr : format → interaction_monad σ unit) (t : interaction_monad σ α) : (interaction_monad σ α)
| s :=
    match t s with
    |(interaction_monad.result.exception msg pos _) :=
        let msg := ("Exception: ":format) ++ (option.rec_on msg (to_fmt "silent") ($ ())) in
        ((tr msg) >> t) s
    |r := r
    end

-- meta def lift_state_except {σ} : Π {α}, interaction_monad σ α  → state_t σ (except_t (option (unit → format) × option pos) id) α
-- | m := do
--   s ← get,
--   match m s with
--   | (success b s) := put s *> pure b
--   | (exception m p s) := put s *> throw (m,p)
--   end

end interaction_monad