import algebra

instance bool.hlt : has_lt bool := ⟨λ a b, bnot $ band a $ bnot b⟩

instance bool.dlt : decidable_rel ((<) : bool → bool → Prop) := by apply_instance
infixl ` =<< `:1  := function.swap (>>=)

meta instance format.has_empty : has_emptyc format := ⟨format.nil⟩

instance string.has_empty : has_emptyc string := ⟨""⟩

def char.to_upper (c : char) : char :=
if char.is_lower c then char.of_nat (c.1 - 32) else c

def string.capitalize : string → string
| ⟨c :: tail⟩ := ⟨char.to_upper c :: tail⟩
| x := x

meta def format.nest_join_pure : string → list (format) → format
| n fs := "(" ++ n ++ (format.nest n.length $ format.join $ list.intersperse (" " ++ format.line) $ fs)++ ")"

meta def format.nest_join : string → list (tactic format) → tactic format
| n fs := do
    fs ← list.mmap id fs,
    pure $ format.nest_join_pure n fs

meta def notimpl {α} : α := undefined_core "not implemented"
meta def unreachable {α} : α := undefined_core "'unreachable' code detected"

def option.join {α} : option (option α) → option α
| (some (some a)) := some a
| x := none


def Exists.map_val {α β} (P : β → Prop) (f : α → β): (∃ (a : α), P (f a)) → ∃ (b : β), P b
| (Exists.intro a p) := Exists.intro (f a) p

def Exists.map_prop {α} {P Q : α → Prop} (f : ∀ a, P a → Q a) : (∃ a, P a) → ∃ a, Q a
| (Exists.intro a p) := Exists.intro a $ f _ p

def and.map {P Q R S : Prop} (fp : P → R) (fq : Q → S) : P ∧ Q → R ∧ S
| ⟨a,b⟩ := ⟨fp a, fq b⟩

def binder_info.to_string : binder_info → string
| binder_info.default := "default"
| binder_info.implicit := "implicit"
| binder_info.strict_implicit := "strict_implicit"
| binder_info.inst_implicit := "inst_implicit"
| binder_info.aux_decl := "aux_decl"

instance binder_info.has_to_string : has_to_string binder_info := ⟨λ x, binder_info.to_string x⟩