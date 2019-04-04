open tactic

meta def tactic.unwrap_neg_helper : expr → tactic unit
| `(-%%e) := do
  h ← tactic.to_expr ``(neg_eq_neg_one_mul %%e),
  try (rewrite_target h),
  tactic.unwrap_neg_helper e
| `(%%e + %%e') :=
  tactic.unwrap_neg_helper e >>
  tactic.unwrap_neg_helper e'
| `(%%e * %%e') :=
  tactic.unwrap_neg_helper e >>
  tactic.unwrap_neg_helper e'
| t := return () --tactic.trace t

meta def tactic.unwrap_neg : tactic unit :=
do t ← target,
   match t with
   | `(%%a = %%_) := do tactic.unwrap_neg_helper a,
                        t ← target,
                        match t with
                        | `(%%_ = %%b) := tactic.unwrap_neg_helper b
                        | _ := fail "???"
                        end
    | _ := tactic.fail (to_string t ++ " is not an equality")
   end

meta def tactic.all_but_front (t : tactic unit) : tactic unit :=
do gs ← get_goals,
   match gs with
   | []           := skip
   | (g :: rs) := do
    set_goals rs,
    all_goals t,
    gs' ← get_goals,
    set_goals (g :: gs')
   end

meta def tactic.one_sum_gt : tactic unit :=
do t ← target,
   match t with
   | `(%%x > 0) := do
    ty ← infer_type x,
    match x with
    | `(%%y + 1) := do
       `[apply @gt_trans %%ty _ _ %%y _],
       `[apply lt_add_of_pos_right, exact zero_lt_one],
       tactic.one_sum_gt  
    | _ := `[exact zero_lt_one]
    end
   | _ := trace t >> fail "one_sum_gt: goal was not of the form 1 + 1 + 1 + ... + 1 > 0"
   end