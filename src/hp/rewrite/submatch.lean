
import .prerule
open tactic expr

namespace hp

/-- Submatches represent fragments of the LHS to match against some given term. -/
meta structure submatch :=
(pf : name) -- the original rule proof
(params : telescope) -- locals, including some typeclasses etc.
(lhs : zipper)
(rhs : expr) -- just to make pping easier
(rel : rel_inst)
(key : name) -- the head symbol

namespace submatch

    /-- `run e s` attempts to unify `e` with `s.lhs` and then returns a rule for this.
        So for example:
        ```
        run `(y + z) `(A + [B + C] =  (A + B) + C) ↝ A + (y + z) = (A + y) +  z
        ```

     -/
    meta def run : expr → submatch → tactic (address × rule)
    | e sm := do
        ms ← sm.params.to_metas,
        lhs ←pure $ sm.lhs.instantiate_vars ms,
        unify e lhs.cursor transparency.none,
        close_obvs_goals ms,
        let mmapper := (λ (p : expr × binder), do -- [todo] make DRY with rule.lean.subcompose.
            ⟨m, ⟨pp_n, bi, _⟩⟩ ← pure p,
            ia ← tactic.is_assigned m <|> pure ff,
            if ia then pure m else do
            is_term m >>= guardb, -- if this fails then it means we couldn't match up a type or kill an assumption.
            y ← infer_type m,
            -- trace_m "submatch.mmapper: " $ y,
            loc' ← tactic.mk_local' pp_n bi y,
            unsafe_assign m loc',
            pure loc'
        ),
        ls ← list.reverse <$> (list.mmap mmapper $ list.reverse $ list.zip ms sm.params),
        ms ← ms.mmap instantiate_mvars,
        -- trace_m "submatch.run: " $ sm.lhs,
        -- trace_m "submatch.run: " $  ms,
        -- trace_fail $ unify ls ms,
        pf ← trace_fail $ tactic.mk_app sm.pf ms.reverse,
        pf ← instantiate_mvars pf,
        pf ← pure $ ls.foldl (λ pf l, if expr.is_local_constant l then expr.bind_lambda pf l else pf) pf,
        r ← rule.of_proof pf,
        r ← pure $ if sm.rel.dir then r.flip else r,
        pure (sm.lhs.get_address, r)

    meta instance : has_to_tactic_format (submatch) := ⟨λ sm, do
        lhs ← tactic.pp sm.lhs,
        pure $ "{" ++ lhs ++ " }"
    ⟩

    meta def create : prerule → tactic (list submatch) | pr := do
        -- locals ← pr.params.to_locals,
        -- body ← pure $ expr.instantiate_vars pr.body locals,
        (r,lhs,rhs) ← tactic.relation_lhs_rhs pr.body,
        (lhs, rhs) ← pure $ if pr.reverse then (rhs, lhs) else (lhs, rhs),
        results ← traverse_proper (λ acc z, (do
                guard (not z.cursor.is_var),
                key ← pure $ expr_table.get_key z.cursor,
                -- trace_m "subtask.create: " $ (z),
                pure $ list.cons { submatch
                       . lhs := z
                       , pf := pr.pf
                       , params := pr.ctxt
                       , rhs := rhs
                       , rel := ⟨r,pr.reverse⟩
                       , key := key
                       }
                     acc
                ) <|> pure acc
        ) [] lhs,
        pure results
    meta def get_key : submatch → name := submatch.key
    meta instance submatch.has_lt : has_lt submatch := ⟨λ x y, (x.pf,x.lhs.get_path.to_address) < (y.pf,y.lhs.get_path.to_address)⟩
    meta instance submatch.dec_lt : decidable_rel ((<) : submatch → submatch → Prop) := by apply_instance

end submatch

meta def submatch_table := tabledict name submatch

namespace submatch_table

local attribute [reducible] submatch_table
meta instance : has_union submatch_table := by apply_instance
meta instance : has_emptyc submatch_table := by apply_instance

/--`submatch e rt` finds rules `r` in `rt` such that the rhs of `r` contains `e`. -/
meta def run (rt : submatch_table) : expr → tactic (list (address × rule)) | e := do
    let key := expr_table.get_key e,
    let submatches := rt.get key,
    -- trace_m "submatch: " $ (key, submatches),
    list.achoose (hp.submatch.run e) submatches.to_list
    -- tactic.trace_m "submatch: " $ submatches,
    -- if   (key = `rule_table.app)
    -- then list.mchoose (hp.submatch.run_app e) submatches
    -- else list.mchoose (hp.submatch.run e) submatches

meta def insert (rt : submatch_table) : prerule → tactic submatch_table
| pr := do
  submatches ← submatch.create pr,
  rt ← pure $ submatches.foldl (λ acc x, tabledict.insert x.get_key x acc) rt,
  pure rt

end submatch_table


end hp