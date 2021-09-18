/- Some helpers for widgets . Should be moved to core? -/
open widget
namespace widget

infixr ` ⇨ `:20 := component

meta class has_show_html (π : Type) :=
(show_html {α} : π → html α)
meta def show_html {π α : Type} [has_show_html π] : π → html α := has_show_html.show_html

meta def show_expr_component : tc expr empty :=
interactive_expression.mk interactive_expression.type_tooltip
meta instance fmt_show: has_show_html format := ⟨λ α f, html.of_string $ format.to_string $ f⟩
meta instance name_show: has_show_html name := ⟨λ α, html.of_name⟩
meta instance option_show {α} [has_show_html α] : has_show_html (option α) :=
⟨λ β x, option.rec_on x (html.of_string "") (λ x, show_html x)⟩
meta instance imr_msg_show : has_show_html (option (unit → format)) :=
⟨λ α x, option.rec_on x (html.of_string "") (λ x, html.of_string $ format.to_string $ x ())⟩
-- meta instance expr_show: has_show_html expr := ⟨λ α e, html.of_component e $ component.ignore_action $ show_expr_component⟩

meta def tc.ignore_action {π α β} : tc π α → tc π β := component.ignore_action

meta instance {α} : has_coe (html α) (list (html α)) := ⟨λ x, [x]⟩

-- meta def tc.bind_props {π α β} (f: β → tactic π) : tc π α → tc β α
-- | (component.mk γ σ i u v p) := component.mk γ σ (λ ⟨ts,b⟩ o, _) _ _ _

universe u

class has_should_update (τ : Type u) := (su : τ → τ → bool)
def should_update {τ : Type u} [x: has_should_update τ] := x.su
instance su_of_deq {τ : Type u} [decidable_eq τ] : has_should_update τ := ⟨λ t1 t2, t1 ≠ t2⟩
instance su_of_pair {τ σ : Type u} [has_should_update τ] [has_should_update σ] : has_should_update (τ × σ) :=
⟨λ ⟨t1,s1⟩ ⟨t2,s2⟩, should_update t1 t2 ∨ should_update s1 s2⟩

meta def component.stateless' {π α} [has_should_update π] (view : π → list (html α)) : component π α :=
component.with_should_update (should_update)
$ component.pure view

-- meta def simple_tooltip {α: Type}  : html α → html α → html α
-- | body hoverstuff :=
--   html.of_component () $ component.mk
--     (option α)
--     bool
--     (λ _ s, ff <| s)
--     (λ p s ia, match ia with (some a) := (s, some a) | none := (¬s, none) end)
--     (λ p s, [h "span" ((if s then [attr.tooltip $ html.map_action some hoverstuff, on_mouse_leave (λ _, none)] else [on_mouse_enter (λ _, none)])) [html.map_action some body]])
--     (λ a b, ff)

end widget