/- A widget for interactive rewriting. -/
import .rule_table .equate_attr
open widget tactic widget.interactive_expression

namespace hp

meta instance ign {π α : Type} : has_coe (component π empty) (component π α) := ⟨component.ignore_action⟩
meta instance ignhtml {α : Type} : has_coe (html empty) (html α) := ⟨html.map_action (λ x, by cases x)⟩

meta def magic_rewrite_tooltip (rt : rule_table) (orig : expr) : tc subexpr rule :=
tc.stateless (λ ⟨e,ea⟩, do
    y ← infer_type e, -- show some type info too.
    rules ← prerule_table.head_rewrites_at rt.head_table orig ea {wilds := tt},
    pp_rules : list format ← list.mmap pp rules,
    y_comp ← interactive_expression.mk interactive_expression.type_tooltip $ y,
    args ← interactive_expression.implicit_arg_list interactive_expression.type_tooltip e,
    pure [h "div" [] [
        h "div" [] [y_comp],
        -- h "hr" [] [],
        -- args,
        -- h "hr" [] [],
        h "div" [] $ list.map (λ r : format, h "a" [cn "db link br3 ph3 pv1 ma1 b--none white bg-purple"] ["use ", r]) $ pp_rules
      ]]
)

meta def magic_expr_view (rt : rule_table) : tc expr empty :=
component.ignore_action $ tc.stateless (λ y, do
  c ← (interactive_expression.mk (magic_rewrite_tooltip rt y)) y,
  pure [c]
)

meta def magic_rewrite_view : tc unit empty :=
tc.stateless (λ ⟨⟩, do
  gs ← get_goals,
  rt ← get_equate_rule_table,
  hs : list (html empty) ← gs.mmap (λ g, do
    ts ← read,
    gn ← pp g,
    set_goals [g],
    lcs ← local_context,
    lchs : list (html empty) ← lcs.mmap (λ lc, do
      pn ← pure $ expr.local_pp_name lc,
      y ← infer_type lc,
      y_comp ← magic_expr_view rt y,
      pure
        $ h "tr" [key $ to_string $ expr.local_uniq_name lc] [
            h "td" [] [html.of_name pn],
            h "td" [] [html.of_string " : "],
            h "td" [] [y_comp]
        ]
    ),
    t ← target,
    t_comp : html empty ← magic_expr_view rt t,
    pure $ h "table" [key $ expr.hash g, className "font-code"] [
      h "tbody" [] $ lchs ++ [
          h "tr" [] [
            h "td" [] (∅) ,
            h "td" [] [html.of_string " ⊢ "],
            h "td" [] [t_comp]
       ]]
    ]
  ),
  pure $ h "ul" [className "list m2"]
       $ list.map (h "li" [className "lh-copy pv3 ba bl-0 bt-0 br-0 b--dotted b--black-30"])
       $ list.map (λ x, [x])
       $ hs
)

meta def magic_rewrite_widget : component tactic_state empty :=
component.map_action (λ o : empty, by cases o) $ tc.to_component magic_rewrite_view
attribute [vm_override magic_rewrite_widget] widget.tactic_state_widget

end hp