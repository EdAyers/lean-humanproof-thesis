import .rule

open tactic expr

namespace hp

/-- A lemma of the form `∀ (..ps) x y (..qs), inner_rel x y → outer_rel (F[X]) (F[Y])` for some expression path `F`.
The idea here is to generalise congruence and monotonicity lemmas. -/
meta structure congruence :=
(pf : name) -- takes the form `∀ (..ps) x y (..qs), inner_rel x y → outer_rel (F[X]) (F[Y])
            -- from which the following members can be computed.
(path : expr.zipper.path)
(outer_rel : rel_inst)
(inner_rel : rel_inst)
(key : name) -- head symbol of F.

namespace congruence

meta def of_pf : name → tactic congruence
| pf := do
  e ← resolve_name pf >>= pure ∘ pexpr.mk_explicit >>= to_expr,
  y ← infer_type e,
  ⟨⟨_,_,i_p⟩ :: ctx, o_p⟩ ← pure $ telescope.of_pis y,
  key ← pure $ expr_table.get_key o_p,
  ⟨i_rel, (expr.var i_lhs), (expr.var i_rhs)⟩ ← tactic.relation_lhs_rhs i_p,
  ⟨o_rel, o_lhs, o_rhs⟩ ← tactic.relation_lhs_rhs o_p,
  i_dir ← pure $ to_bool $ i_lhs < i_rhs,
  ⟨o_lhs_z, o_rhs_z, o_dir ⟩ ← (do
      [o_lhs_z] ← pure $ zipper.find_var (zipper.zip o_lhs) i_lhs,
      [o_rhs_z] ← pure $ zipper.find_var (zipper.zip o_rhs) i_rhs,
      pure (o_lhs_z, o_rhs_z, ff)
  ) <|> (do
      [o_lhs_z] ← pure $ zipper.find_var (zipper.zip o_lhs) i_rhs,
      [o_rhs_z] ← pure $ zipper.find_var (zipper.zip o_rhs) i_lhs,
      pure (o_lhs_z, o_rhs_z, tt)
  ) <|> fail "given declaration is not a congruence / monotonicity lemma",
  guard (o_lhs_z.get_path = o_rhs_z.get_path),
  pure $ {
    pf := pf,
    path := o_lhs_z.get_path,
    outer_rel := ⟨o_rel, o_dir⟩,
    inner_rel := ⟨i_rel, i_dir⟩,
    key := key
    }

end congruence

end hp