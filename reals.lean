import .macros .algebra

open classical

constant real : Type
notation `ℝ` := real

constant real_field : discrete_linear_ordered_field ℝ
noncomputable instance
  : discrete_linear_ordered_field real := real_field
noncomputable instance : decidable_linear_ordered_comm_group real :=
  { decidable_le := λ x y, prop_decidable _,
  ..real_field }

def upper_bound {F} [linear_order F] (S : set F)
  : F → Prop
  := λ B, ∀ x ∈ S, x ≤ B

def least_upper_bound {F} [decidable_linear_ordered_comm_group F] (S : set F)
  : F → Prop
  := λ B, upper_bound S B ∧ (∀ C, upper_bound S C → B ≤ C)

axiom real.complete
  : ∀ S : set ℝ, (∃ B, upper_bound S B) → (∃ B, least_upper_bound S B)

lemma eight_pos : (8:ℝ) > 0 := by {
  rw (_ : (8 : ℝ) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1),
  tactic.swap, dsimp [bit0], ac_refl,
  tactic.one_sum_gt
}

lemma lt_of_sq_lt : ∀ x y : ℝ, 0 < y → x * x < y * y → x < y :=
begin
  intros x y hy h,
  by_cases hx : x > 0, tactic.swap, { exact lt_of_le_of_lt (le_of_not_gt hx) hy },
  have : y*y - x*x > 0, apply sub_pos_of_lt h,
  apply lt_of_sub_pos, rw difference_of_squares at this,
  apply pos_of_mul_pos_right this, apply le_of_lt,
  apply add_pos hy hx
end

lemma real.exists_squareroot : ∀ x : ℝ, x ≥ 0 → ∃ y, y ≥ 0 ∧ y * y = x :=
begin
  intros x hx,
  by_cases x = 0, existsi (0 : ℝ), subst h, exact and.intro hx (mul_zero 0),
  have : x > 0 := lt_of_le_of_ne hx (ne.symm h), clear h hx, rename this hx,
  cases real.complete { y | y*y ≤ x } ⟨x+1, _⟩ with y hy,
  have hy' : y > 0,
  { by_cases 1 ≤ x,
    { apply lt_of_lt_of_le zero_lt_one, apply hy.left,
      suffices : 1 * 1 ≤ x, exact this, rw one_mul, exact h },
    { have : x ≤ 1, apply le_of_not_ge h,
      apply lt_of_lt_of_le hx, apply hy.left,
      suffices : x*x ≤ x*1, rw mul_one at this, exact this,
      apply mul_le_mul_of_nonneg_left this (le_of_lt hx) } },
  existsi y,
  { have h2 : 0 < 2*y, { rw [(_ : (2 : ℝ) = 1 + 1), right_distrib, one_mul], apply add_pos hy' hy', refl },
    have h3 : 0 < 4*y, { rw [(_ : (4:ℝ) = 2 + 2), right_distrib], apply add_pos h2 h2, refl },
    cases lt_trichotomy (y*y) x,
    exfalso,
    let ε := min ((x-y*y)/(8*y)) (2*y),
    have h1 : 2 * y + ε ≤ 4*y, 
    { rw (_ : 4*y = 2*y + 2*y),
      apply add_le_add (le_refl (2*y)) (min_le_right _ _), 
      transitivity (2 + 2) * y, refl, apply right_distrib },
    have h4 : 0 < ε,
    { apply lt_min, apply lt_div_of_mul_lt,
      apply mul_pos eight_pos hy', rw zero_mul,
      apply sub_pos_of_lt h, exact h2 },
    have : ε * (2 * y + ε) < x - y*y,
    { apply @lt_of_le_of_lt _ _ _ (ε * (4*y)),
      apply mul_le_mul_of_nonneg_left h1,
      exact le_of_lt h4, 
      apply @lt_of_le_of_lt _ _ _ (((x - y * y) / (8 * y)) * (4*y)),
      apply mul_le_mul_of_nonneg_right, apply min_le_left,
      exact le_of_lt h3, 
      rw [div_eq_mul_one_div, mul_assoc, mul_comm _ (4*y), ← div_eq_mul_one_div],
      rw (_ : 8 * y = (4  * y) * 2),
      rw ← field.div_div_eq_div_mul, rw div_self,
      rw ← mul_one (x - y * y), rw mul_assoc,
      apply mul_lt_mul_of_pos_left,
      { rw one_mul, apply div_lt_of_mul_lt_of_pos,
        apply add_pos zero_lt_one zero_lt_one, rw one_mul,
        apply lt_add_of_pos_right _ zero_lt_one, },
      apply sub_pos_of_lt h, 
      apply ne.symm (ne_of_lt h3),
      apply ne.symm (ne_of_lt h3),
      refine ne_of_gt _, apply add_pos zero_lt_one zero_lt_one,
      rw [mul_comm _ (2 : ℝ), ← mul_assoc], congr,
      simp [bit0], rw [right_distrib, one_mul], ac_refl },
    { rw left_distrib at this, 
      have := add_lt_of_lt_sub_left this,
      rw (_ : (2 : ℝ) = 1 + 1) at this, 
      rw [right_distrib, one_mul, left_distrib] at this,
      rw (_ : y * y + (ε * y + ε * y + ε * ε) = (y + ε)*(y + ε)) at this,
      apply not_lt_of_ge (hy.left (y + ε) (le_of_lt this)),
      apply lt_add_of_pos_right, assumption,
      rw FOIL, ac_refl, refl },
    cases h, { constructor, exact le_of_lt hy', assumption },
    exfalso,
    let ε := (y*y-x)/(2*y),
    have h4 : ε > 0,
    { apply lt_div_of_mul_lt, rw (_ : 2 = 1 + (1:ℝ)),
      rw [right_distrib, one_mul], apply add_pos hy' hy', refl,
      rw zero_mul, apply sub_pos_of_lt h },
    have : ε * (2 * y - ε) < y*y - x,
    { apply @lt_of_lt_of_le _ _ _ (ε * (2*y)) _,
      apply mul_lt_mul_of_pos_left, apply sub_lt_self, exact h4, exact h4,
      dsimp [ε], rw [div_eq_mul_one_div, mul_assoc, mul_comm _ (2*y), ← div_eq_mul_one_div], 
      rw div_self, rw mul_one, apply ne.symm (ne_of_lt h2) },
    { rw mul_sub at this,
      have := add_lt_of_lt_sub_left this,
      rw add_sub at this,
      have := lt_add_of_sub_left_lt this,
      have := lt_sub_right_of_add_lt this,
      rw (_ : ε * ε + y*y - ε * (2 * y) = (y - ε)*(y-ε)) at this,
      have : upper_bound {y : ℝ | y * y ≤ x} (y - ε),
      { intros y' h', apply le_of_lt, apply lt_of_sq_lt,
        apply sub_pos_of_lt, dsimp [ε],
        apply div_lt_of_mul_lt_of_pos h2,
        rw (_ : y * (2*y) = y*y+y*y),
        apply lt_add_of_pos_of_lt, apply mul_pos hy' hy',
        rw ← sub_eq_add_neg, apply sub_lt_self _ hx,
        rw  (_ : (2 : ℝ) =  1 + 1), rw [right_distrib, left_distrib],
        rw one_mul, refl, apply lt_of_le_of_lt h' this },
      apply not_lt_of_ge (hy.right _ this),
      apply sub_lt_self _ h4, rw FOIL_neg_square,
      rw ← neg_add, rw add_right_comm, rw add_comm, congr,
      rw mul_comm, rw mul_assoc, rw (_ : (2 : ℝ) =  1 + 1),
      rw right_distrib, rw one_mul, refl } },
  intros y hy, 
  by_cases y ≤ 1,
  { rw ← zero_add y, apply add_le_add (le_of_lt hx) h },
  { transitivity (y*y), have : 1 ≤ y := le_of_not_le h,
    apply @le_mul_of_ge_one_right _ _ y y (le_trans zero_le_one this) this,
    transitivity x, assumption, apply le_add_of_nonneg_right zero_le_one }
end

noncomputable
def sqrt (x : ℝ) : ℝ := 
  if h : 0 ≤ x
  then some $ real.exists_squareroot x h
  else 0
notation `√` := sqrt
lemma sqrt_sq {x : ℝ} (h : 0 ≤ x) : √x * √x = x :=
  by { dsimp [sqrt], rw dif_pos h, exact (and.right $ some_spec $ real.exists_squareroot x h), }
lemma sqrt_nonneg (x : ℝ) : √x ≥ 0 :=
by { dsimp [sqrt], by_cases h : 0 ≤ x,
     rw dif_pos h, have := some_spec (real.exists_squareroot x h), cases this, assumption,
     rw dif_neg h, apply le_refl }  

lemma eq_of_nonneg_and_sq_eq : ∀ {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y), x*x = y*y → x = y :=
begin
  intros x y hx hy h, generalize h' : x*x = u, rw h' at h,
  have h1 : (min x y) * (min x y) = u, { min_tac x y },
  have h2 : (max x y) * (max x y) = u, { min_tac x y },
  have h3 : (min x y) * (min x y) ≤ (min x y) * (max x y),
  { apply mul_le_mul_of_nonneg_left; min_tac x y },
  have h4 : (min x y) * (max x y) ≤ (max x y) * (max x y),
  { apply mul_le_mul_of_nonneg_right; min_tac x y },
  rw h1 at h3, rw h2 at h4,
  have : (min x y) * (max x y) = u := le_antisymm h4 h3,
  rw (_ : (min x y) * (max x y) = x * y) at this,
  rw h at this, 
  by_cases h : y = 0,
  { subst h, rw [h, mul_zero] at h', apply eq_zero_of_sqr_eq_zero h' },
  rw [← eq_div_iff_mul_eq _ _ h, mul_div_cancel _ h] at this,
  exact this,
  by_cases x ≤ y; unfold max min; simp [*, if_pos, if_neg], rw mul_comm,
end

lemma sqrt_unique : ∀ {x y} (hx : 0 ≤ x) (hy : 0 ≤ y), y*y = x → y = √x :=
by { intros, apply eq_of_nonneg_and_sq_eq, assumption, apply sqrt_nonneg,
     transitivity x, assumption, symmetry, apply sqrt_sq hx, }

lemma abs_eq_sq_sqrt : ∀ x, abs x = √ (x*x) :=
begin
  intro x, apply sqrt_unique (mul_self_nonneg x) (abs_nonneg x),
  dsimp [abs], min_tac x (-x)
end

lemma eq_of_sqrt_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : √x = √y) : x = y :=
by rw [← sqrt_sq hx, ← sqrt_sq hy, h]

lemma le_zero_of_sqrt_eq_zero : ∀ {x}, √x = 0 → x ≤ 0 :=
begin
  intros, cases le_or_gt 0 x,
  { rw (_ : x = 0), transitivity √x * √x,
    symmetry, apply sqrt_sq h, rw a, apply zero_mul },
  apply le_of_lt h
end

lemma eq_one_of_sqrt_eq_one : ∀ {x}, √x = 1 → x = 1 :=
begin
  intros x h, have hx : 0 ≤ x, { by_contradiction, dsimp [sqrt] at h, rw dif_neg at h, exact zero_ne_one h, assumption },
  rw (_ : 1 = √1) at h, apply eq_of_sqrt_eq hx zero_le_one h,
  apply sqrt_unique zero_le_one zero_le_one (one_mul 1)
end

lemma sqrt_pos_of_pos {x : ℝ} : x > 0 → √ x > 0 :=
begin
  intro hx, apply lt_of_le_of_ne, apply sqrt_nonneg,
  intro h, refine not_lt_of_ge _ hx, apply le_zero_of_sqrt_eq_zero,
  symmetry, assumption
end

lemma inv_sqrt : ∀ {x}, x > 0 → (√x)⁻¹ = √(x⁻¹) :=
begin
  intros x hx, have : 0 < √ x := sqrt_pos_of_pos hx,
  apply sqrt_unique,
  repeat { rw inv_eq_one_div, apply div_nonneg_of_nonneg_of_pos, exact zero_le_one, assumption },
  transitivity (√x * √x)⁻¹, rw inv_eq_one_div, rw inv_eq_one_div,
  rw eq_div_iff_mul_eq _ _ (ne.symm $ ne_of_lt $ mul_pos this this),
  rw [mul_assoc, mul_left_comm _ (√ x) _, ← mul_assoc],
  rw mul_comm (1 / √ x) (√ x), rw ← div_eq_mul_one_div,
  rw div_self (ne.symm $ ne_of_lt this), apply mul_one,
  rw sqrt_sq (le_of_lt hx),
end

lemma sqrt_monotone : ∀ {x y}, x ≤ y → √ x ≤ √ y :=
begin
  intros x y hxy, by_cases 0 < x,
  { by_cases x = y, rw h, apply le_of_lt,
    have : 0 < y, refine lt_of_lt_of_le _ hxy, assumption,
    apply lt_of_sq_lt (√ x) (√ y) (sqrt_pos_of_pos this) _,
    rw [sqrt_sq, sqrt_sq], apply lt_of_le_of_ne; assumption,
    all_goals { apply le_of_lt, assumption } },
  { rw (_ : √ x = 0), apply sqrt_nonneg,
    by_cases x = 0, { rw h, symmetry, apply sqrt_unique, refl, refl, apply zero_mul },
    simp [sqrt], rw dif_neg, intro h, cases lt_or_eq_of_le h, trivial, have := eq.symm h_1, trivial }
end

lemma eq_of_really_close : ∀ {x y : ℝ}, (∀ ε, ε > 0 → abs (x - y) < ε) → x = y :=
begin
  suffices : ∀ x y : ℝ, x < y → ∃ ε, ε > 0 ∧ abs (x - y) ≥ ε,
  { intros x y h, cases (lt_trichotomy x y),
    { exfalso, cases this x y h_1 with ε, cases h_2,
      exact not_lt_of_ge h_2_right (h ε h_2_left) },
    cases h_1, assumption,
    { exfalso, cases this y x h_1 with ε, cases h_2,
      rw abs_sub at h_2_right, exact not_lt_of_ge h_2_right (h ε h_2_left) } },
  intros x y hxy, rw abs_sub, have : y - x > 0 := sub_pos_of_lt hxy,
  existsi (y - x), constructor, assumption, 
  rw abs_of_nonneg (le_of_lt this), apply le_refl
end

lemma real.triangle_inequality : ∀ (x y : ℝ), abs (x + y) ≤ abs x + abs y :=
begin
  intros,
  have h1 : x + y ≤ abs x + abs y,
  { apply add_le_add; apply le_abs_self },
  have h2 : -x + -y ≤ abs (-x) + abs (-y),
  { apply add_le_add; apply le_abs_self },
  rw [← neg_add, abs_neg, abs_neg] at h2,
  apply max_le; assumption,
end

lemma real.triangle_inequality' : ∀ (x y z : ℝ), abs (x - y) ≤ abs (x - z) + abs (z - y) :=
begin
  intros, rw (_ : x - y = (x - z) + (z - y)),
  apply real.triangle_inequality,
  rw [← add_sub_assoc, sub_add_cancel]
end

lemma real.lt_of_lt_triangle_lt (x y z ε : ℝ) :
  abs (x - z) < ε/2 → abs (y - z) < ε/2 → abs (x - y) < ε :=
by { intros h h', rw abs_sub at h', apply lt_of_le_of_lt (real.triangle_inequality' x y z),
     rw [← add_self_div_two ε, ← div_add_div_same], exact add_lt_add h h' }

noncomputable def sgn (x : ℝ) : ℝ := if x = 0 then 0 else if x > 0 then 1 else -1

lemma abs_div_self_eq_sgn (x : ℝ) : abs x / x = sgn x :=
begin
  dsimp [sgn],
  by_cases x = 0, { subst h, rw div_zero, rw if_pos rfl, },
  by_cases x > 0,
  { rw abs_of_nonneg, rw div_self, rw if_neg, rw if_pos,
    assumption', apply le_of_lt, assumption },
  { rw abs_of_neg, rw neg_div, rw div_self,
    rw [if_neg, if_neg], assumption',
    apply lt_of_not_ge, intro h, cases (lt_or_eq_of_le h),
    trivial, have := eq.symm h_1, trivial, }
end

lemma sgn_mul_abs_eq_self (x : ℝ) : sgn x * abs x = x :=
begin
  dsimp [sgn],
  by_cases x = 0, { subst h, rw abs_zero, rw mul_zero },
  by_cases x > 0,
  { rw abs_of_nonneg, rw if_neg, rw if_pos, apply one_mul,
    assumption', apply le_of_lt, assumption },
  { rw abs_of_neg, rw [if_neg, if_neg], assumption',
    rw mul_neg_eq_neg_mul_symm, rw neg_mul_eq_neg_mul_symm,
    rw neg_neg, rw one_mul,
    apply lt_of_not_ge, intro h, cases (lt_or_eq_of_le h),
    trivial, have := eq.symm h_1, trivial, }
end

lemma abs_mul_abs_eq_self_mul_self (x : ℝ) : abs x * abs x = x * x :=
by dsimp [abs]; min_tac x (-x)