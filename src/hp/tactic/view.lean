import .hp hp.writeup basic .waterfall .hp_component .box

namespace hp.rc

open widget hp tactic tactic.unsafe

meta def action_button {α} (label : string) (a : α) (col := "blue") : html α :=
h "a" [
  widget.cn $ "bg-" ++ col,
  widget.cn "link dim ph1 pv1 mb1 dib white br-pill ph2",
  on_click $ λ _, a
] [label]

meta def SourceRow : box.zipper → hp (html action)
|z@⟨p, box.V s b⟩ := do
  box.zipper.set_ctx z,
  (cs,_) ← state_t.run get_commands z,
  cs ← pure $ cs.map (λ ⟨dn,cn,r⟩, action_button dn $ r),
  ppb ← tactic.pp b,
  pp_y ← tactic.pp s.type,
  e : html action ← monad_lift $ tc.ignore_action show_expr_component s.type,
  -- [todo] in the case of it being 'of_value' or 'of_exists' remember to include a list of dependencies or the term.
  -- just give the user some feedback on what it depends on.
  pure $ h "tr" []
      [ h "td" [cn "b pv1"] [show_html $ s.label]
      , h "td" [] [":"]
      , h "td" [] [e]
      , h "td" [] $ cs
      -- , widget.simple_tooltip (show_html s.label) (h "div" [cn "font-code"] [ppb, pp_y])
    ]
| z := failure

meta def StubRow : box.zipper → hp (html action)
| z := hp.hypothetically $ do
  set_goals [z.1.get_dummy_goal],
  zpp ← tactic.pp z,
  (cs,_) ← state_t.run get_commands z,
  cs ← pure $ cs.map (λ ⟨dn,cn,r⟩, action_button dn r),
  ⟨box.path.T s _, b⟩ ← ⍐ $ type_context.run $ box.zipper.down box.coord.T z,
  se ← pure s.to_expr,
  y ← tactic.infer_type se,
  rt ← read,
  e : html action ← monad_lift $ tc.ignore_action (magic_expr_view rt) y,
  tsp : format ← ⍐ $ tactic.read >>= tactic.pp ,
  -- hp.go a,
  ia ← tactic.is_assigned se,
  pure $ h "tr" [cn $ if ia then "green" else ""]
    [ h "td" [] [show_html s.pretty_name]
    , h "td" [] [":"]
    , h "td" [] [e]
    -- , h "td" [] [to_string $ format.to_string $ to_fmt zpp]
    , h "td" [] $ cs
    -- , widget.simple_tooltip (show_html s.pretty_name) (h "div" [cn "font-code"] [tsp])
  ]

meta mutual def TargetRows, SourceRows, Box

with TargetRows : box.zipper → hp (list (html action))
| z@⟨p, box.T _ _⟩ := do
  S ← StubRow z,
  z@⟨box.path.T s p, b⟩ ← type_context.run $ box.zipper.down box.coord.T z,
  rest ← TargetRows z,
  pure $ S :: rest
| z@⟨p, box.A _ _ _⟩ := do
  A1 ← hp.hypothetically $ (do
    z ← type_context.run $ box.zipper.down box.coord.A1 z,
    B ← Box z,
    pure $ h "tr" [cn ""] [h "td" [attr.val "colSpan" "4"] [B]]
  ),
  A2 ← hp.hypothetically $ (do
    z ← type_context.run $ box.zipper.down box.coord.A2 z,
    TargetRows z
  ),
  pure $ A1 :: A2
| z@⟨p, box.R e⟩ := pure []
| z := do
  B ← Box z,
  pure $ [h "tr" [] [h "td" [attr.val "colSpan" "4"] [B]]]

with SourceRows : box.zipper → hp (list (html action) × box.zipper)
| z@⟨p, box.I _ _⟩ := do
  z@⟨box.path.I h g p, b⟩ ← type_context.run $ box.zipper.down box.coord.I z,
  set_goals [g],
  rest ← SourceRows z,
  pure $ rest
| z@⟨p, box.V _ _⟩ := do
  S ← SourceRow z,
  z@⟨box.path.V src p, b⟩ ← type_context.run $ box.zipper.down box.coord.V z,
  (rest, z) ← SourceRows z,
  pure $ (S :: rest, z)
| z := pure ([], z)

with Box  : box.zipper → hp ((html action))
| z@⟨p, box.O []⟩ := pure $ html.of_string "IMPOSSIBLE"
| z@⟨p, box.R e⟩ := do
  ee : html action ← monad_lift $ tc.ignore_action show_expr_component e,
  pure $ ee
| z@⟨p, box.O [b]⟩ := Box ⟨p,b⟩
| z@⟨p, box.O bs⟩ := do
  Bs ← list.mmap (λ t, do
    z ← hp.hypothetically $ monad_lift $ type_context.run $ t,
    B ← Box z,
    pure B
  ) $ box.zipper.down_O z,
  Bs ← pure $ Bs.intersperse (h "div" [cn "ma1"] ["⋁"]),
  pure $ h "div" [cn "flex items-center"] Bs
| z := do
  set_goals [z.1.get_dummy_goal],
  (Vs, z) ← SourceRows z,
  rule ← pure $ if Vs.empty then [] else [h "tr" [] [h "td" [attr.val "colSpan" "4", cn "bt mv3"] []]],
  trs ← TargetRows z,
  pure $ h "table" [cn "ba b--blue pa1"] [
    h "tbody" []
      ([]
      ++ Vs
      ++ rule
      ++ trs
      )
  ]

meta inductive app_action
| new_state (undoable : bool) : rc.action → app_action
| undo : app_action
| redo : app_action

@[derive decidable_eq]
meta structure undo_state (α : Type) :=
(undos : list α)
(redos : list α)

namespace undo_state
  variables {α : Type}
  meta def init : undo_state α := ⟨[], []⟩
  meta instance : has_emptyc (undo_state α) := ⟨init⟩
  meta def save : α → undo_state α → undo_state α
  | a ⟨l, r⟩ := ⟨a::l, []⟩
  meta def undo : undo_state α → option (α × undo_state α)
  | ⟨x::y::l, r⟩   := some (y, ⟨y::l, x::r⟩)
  | _ := none
  meta def has_undo : undo_state α → bool
  | u := option.is_some $ undo u
  meta def current : undo_state α → option (α)
  | ⟨x::_,_⟩ := some x
  | _ := none
  meta def redo : undo_state α → option (α × undo_state α)
  | ⟨l, x::r⟩ := some (x, ⟨x::l,r⟩)
  | _ := none
  meta def has_redo : undo_state α → bool
  | u := option.is_some $ redo u
end undo_state

@[derive_setters]
meta structure app_state : Type :=
(debug : html empty)
(status : result unit hp_state)
(undos : undo_state hp_state)
(inner_tactic : option (inner_component) := none)

open interaction_monad.result

namespace app_state

meta def get : app_state → option hp_state
| R := R.status.get

meta def init : hp_state → app_state
| rs := { debug := html.of_string "debug_view"
        , status := result.success rs ()
        , undos := undo_state.save rs $ ∅ }

meta def update_err : option (unit → format) → option pos → app_state → app_state
| msg p R := with_status (exception msg p ()) R

meta def update : hp_state → app_state → app_state
| rs R@{status := success _ _, ..} := R.with_status $ success rs ()
| _ R@{status := exception msg p rs, ..} := R.with_status $ exception msg p rs

meta def save : hp_state → app_state → app_state
| rs R :=
  match R.status with
  | (success _ ()) := modify_undos (undo_state.save rs) $ R.with_status $ success rs ()
  | (exception _ _ _) := update rs R
  end

end app_state

meta def app_show : hp (html rc.action) := do
  rs ← get,
  lc ← ⍐ $ tactic.local_context >>= tactic.pp,
  set_goals [rs.result],
  z ← ⍐ $ type_context.run $ box.zipper.zip rs.b,
  z.set_ctx,
  x ← Box $ z,
  cs ← pure rs.writeup,
  wu ← hp.writeup.write rs.dont_instantiate cs.reverse,
  pure $ h "div" []
      [
        h "div" [cn "font-code"] [x]
      -- , h "div" [cn "red"] [lc]
      -- , h "ul" [cn "font-code"] (list.map (λ t, h "li" [] [to_string t]) $ list.reverse $ rs.trace)
      , wu
    ]

meta instance has_should_update : has_should_update hp_state :=
{su := λ a b, tt} -- [todo]

meta def hp_state.show_comp : component hp_state _ :=
component.stateless' (λ rs,
  let R := run app_show in
  match R rs with
  | (success r s) := [r]
  | (exception msg _ s) := [show_html msg]
  end
)

meta instance : has_show_html hp_state :=
{show_html := λ α r, html.of_component r $ component.ignore_action $ hp_state.show_comp }

meta def app_state.run (undoable : bool) : rc.action → app_state → app_state
| (action.interactive_inner_tactic c) R := {inner_tactic := some c, ..R}
| (action.new_state rs2) R :=
  let rsf := rs2 in
  app_state.with_inner_tactic none $ (if undoable then app_state.save rsf else app_state.update rsf) $ R
  -- | (exception msg p (rs)) :=
  -- hp_state.update_err (some $ λ _,
  --   (format.nil <| ((λ x : unit → format, x() ++ format.line) <$> msg))
  --   ++ format.line ++
  --   (list.foldl (++) format.nil $ list.intersperse format.line $ list.reverse $ rs.trace)) p R
  -- end
-- | r x := x

meta def app_state.of_option : option hp_state → app_state → app_state
| none Rs := app_state.update_err (some (λ _, to_fmt "error")) none Rs
| (some rs) Rs := app_state.update rs Rs

meta def app_state.undo : app_state → app_state
| Rs := Rs <| (do
  ⟨rs, u⟩ ← undo_state.undo Rs.undos,
  pure { status := success rs (), undos := u, ..Rs})

meta def app_state.redo : app_state → app_state
| Rs := Rs <| (do
  (rs, u) ← undo_state.redo Rs.undos,
  pure { status := success rs (), undos := u, ..Rs})

open app_state app_action

meta def app_init : hp_state → option (app_state) → app_state
| rs none := app_state.init rs
| ts (some rs) := rs

meta def app_update : hp_state → app_state → app_action → app_state × option string
| ts Rs (new_state uu r) := (run uu r Rs, none)
| ts Rs (undo) := (undo Rs, none)
| ts Rs (redo) := (redo Rs, none)

meta def app_view : hp_state → app_state → list (html (app_action))
| r R :=
  let header :=
    h "div" [] [
      -- h "div" [cn "ma1 pa1 ba b--red"] [
      --   show_html $ (to_fmt <$> box.zipper.get_adr <$>  (hp_state.zipper <$> hp_state.get R))
      -- ],
      h "button" [cn "ma1", on_click $ λ _, app_action.undo] ["undo"],
      h "button" [cn "ma1", on_click $ λ _, app_action.undo] ["redo"],
      to_string $ R.undos.undos.length
    ] in
  let body : list (html (app_action)) :=
    match R.status, R.inner_tactic with
    | ( success rs _ ), none :=
      let r := run app_show in
      match r rs with
      | (success v _) :=
        -- if u.undos.length > 1 then h "div" [] ["hello world"] else
        html.map_action (app_action.new_state tt) $ v
      | (exception msg p rs) := [ h "div" [] ["View error occurred: ", show_html msg] ]
      end
    | (success rs _), (some c) :=
      let r := run $ pure prod.mk <*> app_show <*> pure c in
      match r rs with
      | (success (v, cc) _) :=
        [ html.map_action (app_action.new_state tt) $ v
        , html.map_action (app_action.new_state tt ∘ action.new_state) $ cc
        /- aesthetic [todo]: the inner tactic should replace the goal that the inner tactic is being invoked on.
        This requires rejigging how these work somewhat.

        The basic idea with 'inner tactics' is that you should be able to enter special 'reasoning modes'
        and these should correspond to special blocks within the generated lean proof.

         -/
        ]
      | (exception msg p rs) := [ h "div" [] ["View error occurred: " , show_html msg] ]
      end
    | (exception msg pos _), _ := [ h "div" [] ["Error occurred:", show_html msg] ]
    end in
  [header] ++ body

meta def app : component hp_state string :=
component.with_should_update (λ a b, ff)
$ component.stateful (app_action) (app_state)
 app_init
 app_update
 app_view

end hp.rc