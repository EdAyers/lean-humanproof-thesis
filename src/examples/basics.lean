import hp.tactic.hp_interactive

example {P Q: Prop} : Π (q : Q), (Q → P) → P :=
begin [hp]
  intros,
  apply H₀,
end

example {Q : Prop} {P : nat → Prop} : Π (h₀ : Q) (h₁ : Q → P 0) (h₂ : (∀ x (h : P x), P (x+1))), P 2:=
begin [hp]
  unroll,
  apply H₁, -- [todo] reads clunky. I need to improve the statement writing heuristics.
  apply H₁,
  apply H₀,
end

-- example : ∀ x:nat, (λ z, z = z) x :=
-- begin [hp]
--   equate
-- end


/- Target:

Let Q, P and R be propositions. Assume P → R, Q → R and P ∨ Q.
Since P ∨ Q, we have either P or Q.

In the case P: Since P → R we are done.

In the case Q: Since Q → R we are done.

 -/

example {Q P R : Prop} : (P → R) → (Q → R) → P ∨ Q → R :=
begin [hp]
  unroll, -- [todo] cases button on H₁
  -- idea: something should hint that applying is not the right approach here?
  cases H₁,
  apply H,
  apply H,

end

-- -- -- set_option pp.all true
-- example : ∀ x y : nat, ∃ z, y = z :=
-- begin [hp]
--   -- [todo] rogue full stop at beginning
--   unroll,

-- end


-- example {P Q : Prop} : P → Q → Q ∧ P :=
-- begin [hp]

-- end

-- example : Π {α : Type} [group α] (x y : α), x = y :=
-- begin [hp]
--   (hp.down 0 0 *> hp.intros),
--   (hp.trace_writeup),

-- end

