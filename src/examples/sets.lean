import data.set.function
import hp.tactic.hp_interactive

open set hp

variables {α β : Type} {C B A : set α} {f : α → β}

-- theorem inj_on.mono1 (h : B ⊆ A) (ht : inj_on f A) : inj_on f B :=
-- begin
--   assume x y ∈ B,
--   apply ‹inj_on f A›,
--   repeat { apply ‹B ⊆ A›, assumption }
-- end
-- -- set_option trace.type_context.is_def_eq_detail true
-- -- set_option pp.all true
-- theorem inj_on.mono2 (h : B ⊆ A) (ht : inj_on f A) : inj_on f B :=
-- begin [hp]
--   expand `ht,
--   expand `T,
--   intros,
--   apply_first `ht,
--   -- trace_writeup,
--   expand `h,
--   expand `h,

--   apply_first `h,
--   apply_first `h
-- end


-- theorem int_sdiff {A B C : set α} : (A ∪ B) \ C = (A \ C) ∪ (B \ C) :=
-- begin [hp]
-- trace_commands_at `T,
-- end
