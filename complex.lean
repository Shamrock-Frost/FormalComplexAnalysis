import .reals
open classical

structure complex :=
(Re : real) (Im : real)

def pure_real (z : complex) := z.Im = 0
def pure_imaginary (z : complex) := z.Re = 0

notation `ℂ` := complex
open complex

@[reducible] noncomputable
def complex.zero : complex := ⟨0,0⟩

@[reducible] noncomputable
def complex.one : complex := ⟨1,0⟩

@[reducible] noncomputable
def complex.add : complex → complex → complex
| ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩

@[reducible] noncomputable
def complex.neg : complex → complex
| ⟨a, b⟩ := ⟨-a, -b⟩

@[reducible] noncomputable
def complex.mul : complex → complex → complex
| ⟨a, b⟩ ⟨c, d⟩ := ⟨a*c - b*d, a * d + b * c⟩

@[reducible] noncomputable
def complex.scalar_mul (k : real) : complex → complex
| ⟨x, y⟩ := ⟨k*x, k*y⟩

@[reducible] noncomputable
def complex.conj : complex → complex
| ⟨x, y⟩ := ⟨x, -y⟩

@[reducible] noncomputable
def complex.norm_squared : complex → real
| ⟨x, y⟩ := x*x + y*y

lemma complex.norm_squared_nonneg : ∀ z : ℂ, z.norm_squared ≥ 0 
| ⟨x, y⟩ := add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)

@[reducible] noncomputable
def complex.norm (z : complex) := √(complex.norm_squared z)

lemma complex.norm_nonneg : ∀ z : ℂ, z.norm ≥ 0 :=
λ z, sqrt_nonneg z.norm_squared

lemma squared_norm_eq_norm_squared : ∀ z : ℂ, z.norm * z.norm = z.norm_squared :=
λ z, sqrt_sq z.norm_squared_nonneg

noncomputable
def complex.inv (z : complex) : complex :=
  complex.scalar_mul (1/(complex.norm_squared z)) (complex.conj z)

@[reducible] noncomputable
def i : ℂ := ⟨0, 1⟩

noncomputable instance : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩

lemma coe_pure_real : ∀ x : ℝ, pure_real x := λ x, rfl

meta def simple_complex_eq := do
  names ← tactic.intros,
  monad.mapm' tactic.cases names,
  `[simp [1, 0, (+), (*)]],
  `[simp [complex.zero, complex.one, complex.add, complex.mul]]

lemma complex.mul_comm : ∀ z w, complex.mul z w = complex.mul w z :=
  by { intros z w, cases z, cases w, simp [complex.mul], 
       constructor,
       { rw mul_comm, apply congr_arg, rw mul_comm },
       { rw add_comm, apply congr; rw mul_comm } }

lemma norm_squared_eq_mul_conj
  : ∀ z, complex.mul z (complex.conj z) = ⟨complex.norm_squared z, 0⟩
  := by { intros, cases z, simp [complex.conj, complex.norm_squared, complex.mul],
          rw [mul_comm, add_neg_self] }

lemma norm_squared_eq_mul_conj'
  : ∀ z, complex.norm_squared z = Re (complex.mul z (complex.conj z))
  := by intros; rw norm_squared_eq_mul_conj

lemma mul_conj_is_pure_real
  : ∀ z, pure_real (complex.mul z (complex.conj z))
  := by intros; rw norm_squared_eq_mul_conj; simp [pure_real]

lemma scalar_mul_comm_mul
  : ∀ w z k, complex.scalar_mul k (complex.mul w z) = complex.mul w (complex.scalar_mul k z)
  := by { intros, cases z, cases w, 
          simp [complex.scalar_mul, complex.mul],
          constructor; rw left_distrib; apply congr,
          { apply congr_arg, ac_refl },
          { rw ← neg_mul_eq_mul_neg, ac_refl },
          { apply congr_arg, ac_refl },
          { ac_refl } }

lemma conj_of_conj : ∀ z, complex.conj (complex.conj z) = z :=
  by intros; cases z; simp [complex.conj]

lemma norm_squared_eq_norm_squared_of_conj : ∀ z, complex.norm_squared z = complex.norm_squared (complex.conj z) := by {
  intros,
  suffices : complex.mk (complex.norm_squared z) 0 = ⟨complex.norm_squared (complex.conj z), 0⟩,
  { have := congr_arg Re this,
    simp at this, assumption },
  rw [← norm_squared_eq_mul_conj, ← norm_squared_eq_mul_conj, conj_of_conj],
  rw complex.mul_comm }

lemma norm_squared_zero_implies_zero 
  : ∀ z, complex.norm_squared z = 0 → z = complex.zero
  := by {
    intros z h, 
    cases z,
    dunfold complex.norm_squared at h,
    suffices : z_Re*z_Re = 0 ∧ z_Im*z_Im = 0,
    { unfold complex.zero,
      cases this,
      suffices : z_Re = 0 ∧ z_Im = 0,
      { rw [this.left, this.right] },
      by_contra, rw decidable.not_and_iff_or_not at a,
      cases a;
      apply division_ring.mul_ne_zero a a; assumption },
    by_contradiction,
    rw decidable.not_and_iff_or_not at a,
    have hnonneg1 : 0 ≤ z_Re * z_Re, { apply mul_self_nonneg },
    have hnonneg2 : 0 ≤ z_Im * z_Im, { apply mul_self_nonneg },
    have : 0 < z_Re * z_Re ∨ 0 < z_Im * z_Im,
    { cases a,
      { apply or.inl,
        apply lt_of_le_of_ne,
        exact hnonneg1,
        intro, apply a, symmetry, assumption },
      { apply or.inr,
        apply lt_of_le_of_ne,
        exact hnonneg2,
        intro, apply a, symmetry, assumption } },
    suffices : 0 < z_Re * z_Re + z_Im * z_Im,
    { have := or.inl this,
      rw ← ne_iff_lt_or_gt at this,
      apply this, symmetry, assumption },
    cases this,
    { rw add_comm,
      apply add_pos_of_nonneg_of_pos; assumption },
    { apply add_pos_of_nonneg_of_pos; assumption } }

lemma complex.mul_inv_cancel
  : ∀ z, z ≠ complex.zero → complex.mul z (complex.inv z) = complex.one
  := by {
    intros z h, 
    unfold complex.inv,
    rw ← scalar_mul_comm_mul,
    rw norm_squared_eq_mul_conj,
    unfold complex.scalar_mul,
    rw mul_zero,
    have : complex.norm_squared z ≠ 0,
    { by_contra, apply h, apply norm_squared_zero_implies_zero,
      by_contra, exact a a_1 },
    rw one_div_mul_cancel this }

lemma complex.inv_mul_cancel
  : ∀ z, z ≠ complex.zero → complex.mul (complex.inv z) z = complex.one
  := by intros z h; rw complex.mul_comm; apply complex.mul_inv_cancel z h

lemma complex.left_distrib
: ∀ v w z, complex.mul v (complex.add w z)
           = complex.add (complex.mul v w) (complex.mul v z)
  := by { intros, cases v, cases w, cases z,
          simp [complex.mul, complex.add],
          constructor,
          { rw left_distrib, simp,
            apply congr_arg, apply congr_arg,
            rw left_distrib, rw neg_add },
          { rw left_distrib, simp,
            apply congr_arg, apply congr_arg,
            rw left_distrib } }

noncomputable instance : discrete_field ℂ :=
  { zero := complex.zero
  , one := complex.one
  , add := complex.add
  , mul := complex.mul
  , neg := complex.neg
  , inv := complex.inv
  , add_zero := by simple_complex_eq
  , zero_add := by simple_complex_eq
  , one_mul := by simple_complex_eq
  , mul_one := by simple_complex_eq
  , add_assoc := by simple_complex_eq
  , add_comm := by simple_complex_eq
  , mul_assoc := by { simple_complex_eq, constructor,
                      { rw left_distrib a_Re, rw right_distrib _ _ c_Re,
                        rw right_distrib, rw left_distrib, rw neg_add, rw neg_add,
                        repeat { rw mul_assoc },
                        generalize h1 : -(a_Re * (b_Im * c_Im)) = x, 
                        rw (_ : a_Re * -(b_Im * c_Im) = x),
                        generalize : -(a_Im * (b_Re * c_Im)) = y, 
                        generalize : a_Re * (b_Re * c_Re) = z,
                        generalize h2 : -(a_Im * b_Im) * c_Re = w,
                        rw (_ : -(a_Im * (b_Im * c_Re)) = w),
                        ac_refl,
                        { rw ← h2,
                          rw neg_eq_neg_one_mul,
                          rw neg_eq_neg_one_mul (a_Im * _),
                          ac_refl },
                        { rw ← h1,
                          rw neg_eq_neg_one_mul,
                          rw neg_eq_neg_one_mul (a_Re * _),
                          ac_refl }, },
                      { rw neg_mul_eq_mul_neg, rw neg_mul_eq_neg_mul,
                        rw left_distrib a_Im, rw right_distrib _ _ c_Im,
                        rw add_comm (b_Re * c_Im) (b_Im * c_Re), 
                        rw left_distrib a_Re, rw right_distrib _ _ c_Re,
                        rw ← add_assoc, rw ← add_assoc,
                        simp,
                        apply congr, { apply congr_arg, rw mul_assoc },
                        apply congr, { apply congr_arg, rw mul_assoc },
                        apply congr, { apply congr_arg, rw mul_assoc },
                        apply congr_arg, rw mul_assoc } }
  , mul_comm := complex.mul_comm
  , zero_ne_one := by { intro h, apply real_field.zero_ne_one, simp [0, 1], simp [0, 1] at h,
                        rw (_ : real_field.zero = Re complex.zero),
                        rw (_ : real_field.one = Re complex.one),
                        rw h, refl, refl }
  , add_left_neg := by simple_complex_eq
  , mul_inv_cancel := complex.mul_inv_cancel
  , inv_mul_cancel := complex.inv_mul_cancel
  , left_distrib := complex.left_distrib
  , right_distrib := by { intros, simp [(*)],
                          rw complex.mul_comm _ c,
                          rw complex.mul_comm a c,
                          rw complex.mul_comm b c,
                          apply complex.left_distrib }
  , inv_zero := by { dsimp [complex.zero, complex.inv, complex.norm_squared],
                     rw [mul_zero, add_zero, div_zero, complex.conj],
                     dsimp [complex.scalar_mul], congr, rw mul_zero, rw zero_mul }
  , has_decidable_eq := by {
      intros x y, cases x, cases y,
      rw (_ : ({complex .  Re := x_Re, Im := x_Im} = {Re := y_Re, Im := y_Im})
            = (x_Re = y_Re ∧ x_Im = y_Im)),
      apply_instance, apply propext, constructor; intro h,
      { cases h, constructor; refl },
      { cases h, cases h_left, cases h_right, refl } } }

noncomputable
instance : decidable_eq ℂ :=
  by { intros x y, cases x, cases y,
       rw (_ : ({complex .  Re := x_Re, Im := x_Im} = {Re := y_Re, Im := y_Im})
             = (x_Re = y_Re ∧ x_Im = y_Im)),
       apply_instance, apply propext, constructor; intro h,
       { cases h, constructor; refl },
       { cases h, cases h_left, cases h_right, refl } }

notation `|`z`|` := complex.norm z

lemma norm_zero_implies_zero  : ∀ z, |z| = 0 → z = 0 :=
by { intros z h, rw (_ : 0 = √0) at h, apply norm_squared_zero_implies_zero,
     apply eq_of_sqrt_eq, apply complex.norm_squared_nonneg, refl, exact h,
     apply sqrt_unique, refl, refl, rw mul_zero }

lemma norm_of_pure_real : ∀ z, pure_real z → |z| = abs (Re z) :=
begin
  intros z hz, rw abs_eq_sq_sqrt, dsimp [complex.norm],
  rw (_ : complex.norm_squared z = z.Re * z.Re),
  cases z, dsimp [complex.norm_squared], rw (_ : z_Im = 0),
  rw [mul_zero, add_zero], exact hz,
end

lemma norm_of_zero : |0| = 0 :=
  eq.symm $ sqrt_unique (complex.norm_squared_nonneg 0) (le_refl 0)
          $ by { rw mul_zero, rw (_ : (0 : ℂ) = ⟨0, 0⟩), dsimp [complex.norm_squared], simp, refl }

lemma norm_of_one : |1| = 1 :=
  eq.symm $ sqrt_unique (complex.norm_squared_nonneg 1) zero_le_one
          $ by { rw mul_one, rw (_ : (1 : ℂ) = ⟨1, 0⟩), dsimp [complex.norm_squared], simp, refl }

@[simp]
lemma complex.unfold_add : ∀ a b c d,
  complex.mk a b + complex.mk c d = complex.mk (a + c) (b + d) := by intros; refl
@[simp]
lemma complex.unfold_neg : ∀ a b,
  -complex.mk a b = complex.mk (-a) (-b) := by intros; refl
@[simp]
lemma complex.unfold_mul : ∀ a b c d,
  complex.mk a b * complex.mk c d = complex.mk (a*c - b*d) (a * d + b * c) := by intros; refl
@[simp]
lemma complex.unfold_inv : ∀ a b,
  (complex.mk a b)⁻¹ = complex.mk (a/(a*a + b*b)) (-b/(a*a + b*b)) :=
  by { intros, generalize h : complex.mk a b = z,
       transitivity complex.scalar_mul (1/(complex.norm_squared z)) (complex.conj z), refl, 
       subst h, dsimp [complex.norm_squared, complex.scalar_mul],
       rw [mul_comm _ a, ← div_eq_mul_one_div], rw [mul_comm _ (-b), ← div_eq_mul_one_div] }
      
@[simp]
lemma complex.unfold_conj : ∀ a b,
  complex.conj (complex.mk a b) = complex.mk a (-b) := by intros; refl

lemma norm_conj : ∀ z : ℂ, |z| = |z.conj| :=
by intro z; dsimp [complex.norm]; rw norm_squared_eq_norm_squared_of_conj

lemma norm_sub : ∀ z w : ℂ, |z - w| = |w - z| :=
by { intros, dsimp [complex.norm], rw (_ : complex.norm_squared (z + -w) = complex.norm_squared (w + -z)),
     cases z, cases w, simp, dsimp [complex.norm_squared], apply congr,
     { apply congr_arg, transitivity -(z_Re + -w_Re) * -(z_Re + -w_Re),
       rw neg_eq_neg_one_mul (z_Re + -w_Re), rw ← mul_assoc, rw mul_right_comm (-1 : ℝ),
       rw [square_neg_one, one_mul], rw [neg_add, neg_neg, add_comm] },
     { transitivity -(z_Im + -w_Im) * -(z_Im + -w_Im),
       rw neg_eq_neg_one_mul (z_Im + -w_Im), rw ← mul_assoc, rw mul_right_comm (-1 : ℝ),
       rw [square_neg_one, one_mul], rw [neg_add, neg_neg, add_comm] } }

lemma norm_neg : ∀ z, |(-z)| = |z| :=
by intro; rw [← zero_sub, norm_sub, sub_zero]

lemma complex.norm_pos : ∀ z : ℂ, z ≠ 0 → z.norm > 0 :=
begin
  intros, apply lt_of_le_of_ne,
  apply complex.norm_nonneg, apply ne.symm,
  apply mt (norm_zero_implies_zero z), assumption
end

lemma norm_squared_of_scale : ∀ x z, complex.norm_squared (complex.scalar_mul x z) = (x*x) * z.norm_squared :=
by { intros, cases z, simp [complex.scalar_mul, complex.norm_squared],
     rw left_distrib, ac_refl, }

lemma Re_additive : ∀ z w, Re (z + w) = Re z + Re w :=
by intros; cases z; cases w; simp

lemma Im_additive : ∀ z w, Im (z + w) = Im z + Im w :=
by intros; cases z; cases w; simp

lemma mul_pure_real : ∀ z w : ℂ, pure_real z → z * w = complex.scalar_mul z.Re w :=
by intros; cases z; cases w; simp [pure_real] at a; rw a; simp [complex.scalar_mul]

lemma scale_pure_real : ∀ x (z : ℂ), pure_real z → pure_real (complex.scalar_mul x z)
                      ∧ Re (complex.scalar_mul x z) = x * Re z :=
by intros; cases z; simp [pure_real] at a; rw a; simp [complex.scalar_mul, pure_real]

lemma Re_of_scale : ∀ x (z : ℂ), Re (complex.scalar_mul x z) = x * Re z :=
by intros; cases z; simp

lemma Im_of_scale : ∀ x (z : ℂ), Im (complex.scalar_mul x z) = x * Im z :=
by intros; cases z; simp

lemma Re_conj : ∀ z, Re z = Re z.conj := by intro; cases z; refl

lemma Re_neg : ∀ z, Re (-z) = -Re z :=
by intros; cases z; simp

lemma Re_sub : ∀ z w, Re (z - w) = Re z - Re w :=
by intros; cases z; cases w; simp

lemma Im_neg : ∀ z, Im (-z) = -Im z :=
by intros; cases z; simp

lemma conj_add : ∀ z w, complex.conj (z + w) = complex.conj z + complex.conj w :=
by intros; cases z; cases w; simp [complex.conj]

lemma conj_mul : ∀ z w, complex.conj (z * w) = complex.conj z * complex.conj w :=
by intros; cases z; cases w; simp [complex.conj]

lemma conj_neg : ∀ z, complex.conj (-z) = - complex.conj z :=
by intros; cases z; simp

lemma conj_sub : ∀ z w, complex.conj (z - w) = complex.conj z - complex.conj w :=
by intros; cases z; cases w; simp

lemma norm_mul : ∀ z w, |z*w| = |z|*|w| :=
begin
  intros, symmetry, apply sqrt_unique,
  apply complex.norm_squared_nonneg,
  apply mul_nonneg; apply complex.norm_nonneg, 
  rw [mul_left_comm, mul_assoc, ← mul_assoc],
  rw [squared_norm_eq_norm_squared, squared_norm_eq_norm_squared],
  rw [norm_squared_eq_mul_conj' (z*w)],
  transitivity ((z * w) * (complex.conj (z * w))).Re,
  { rw [conj_mul,mul_left_comm, mul_assoc, ← mul_assoc, mul_comm _ z],
    rw norm_squared_eq_mul_conj', rw norm_squared_eq_mul_conj',
    rw [mul_pure_real, Re_of_scale], congr,
    apply mul_conj_is_pure_real },
  refl
end

lemma norm_squared_eq_mul_conj''
  : ∀ (z : ℂ), complex.norm_squared z = (z * (complex.conj z)).Re
  := norm_squared_eq_mul_conj'

lemma norm_inv : ∀ z, z ≠ 0 → |z⁻¹| = |z|⁻¹ :=
begin
  intros, have : z.norm_squared > 0,
  { apply lt_of_le_of_ne, apply complex.norm_squared_nonneg,
    apply ne.symm, apply mt (norm_squared_zero_implies_zero z), assumption },
  cases z, simp [complex.inv],
  simp [complex.norm, complex.norm_squared],
  rw ← field.div_mul_eq_mul_div_comm,
  rw inv_sqrt, congr, 
  rw inv_eq_one_div,
  rw div_eq_mul_one_div,
  rw div_eq_mul_one_div, 
  rw div_eq_mul_one_div (-z_Im),
  rw mul_right_comm,
  rw ← mul_assoc, rw ← right_distrib,
  suffices : (z_Re * (1 / (z_Re * z_Re + z_Im * z_Im)) * z_Re + -z_Im * (1 / (z_Re * z_Re + z_Im * z_Im)) * -z_Im) = 1,
  { rw this, rw one_mul },
  rw mul_right_comm, rw mul_right_comm (-z_Im),
  rw ← right_distrib,
  rw [mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm, neg_neg],
  rw ← div_eq_mul_one_div, rw div_self,
  all_goals { dsimp [complex.norm_squared] at this, try { apply ne_of_gt }, assumption }
end

lemma norm_div : ∀ z w, w ≠ 0 → |z/w| = |z|/|w| :=
begin
  intros, rw div_eq_mul_one_div, rw norm_mul, congr,
  rw [← norm_inv, inv_eq_one_div], assumption
end

lemma abs_Re_le_norm : ∀ z, abs (Re z) ≤ |z| :=
begin
  intro z, rw abs_eq_sq_sqrt, dsimp [complex.norm],
  apply sqrt_monotone, cases z, dsimp [ complex.norm_squared], 
  apply le_add_of_nonneg_right, apply mul_self_nonneg
end

lemma abs_Im_le_norm : ∀ z, abs (Im z) ≤ |z| :=
begin
  intro z, rw abs_eq_sq_sqrt, dsimp [complex.norm],
  apply sqrt_monotone, cases z, dsimp [complex.norm_squared], 
  apply le_add_of_nonneg_left, apply mul_self_nonneg
end

lemma complex.eq_of_really_close : ∀ {z w : ℂ}, (∀ ε, ε > 0 → |z - w| < ε) → z = w :=
begin
  intros z w h, suffices : Re z = Re w ∧ Im z = Im w, { cases z, cases w, simp at this, rw [this.left, this.right] },
  constructor,
  { apply eq_of_really_close, intros ε hε, specialize h ε hε,
    rw [sub_eq_add_neg, ← Re_neg, ← Re_additive, ← sub_eq_add_neg],
    apply lt_of_le_of_lt, apply abs_Re_le_norm, assumption },
  { apply eq_of_really_close, intros ε hε, specialize h ε hε,
    rw [sub_eq_add_neg, ← Im_neg, ← Im_additive, ← sub_eq_add_neg],
    apply lt_of_le_of_lt, apply abs_Im_le_norm, assumption }
end

lemma norm_squared_sum : ∀ z w, complex.norm_squared (z + w) = complex.norm_squared z + 2*(Re (z * w.conj)) + complex.norm_squared w :=
begin
  intros, rw norm_squared_eq_mul_conj'',
  rw norm_squared_eq_mul_conj'', rw norm_squared_eq_mul_conj'',
  rw [conj_add, left_distrib, right_distrib, right_distrib],
  rw [add_assoc, ← add_assoc (w * _)], rw ← add_assoc,
  rw [Re_additive, Re_additive], congr, rw two_mul,
  cases z, cases w, simp, ac_refl,
end

lemma complex.triangle_inequality : ∀ (x y : ℂ), |x + y| ≤ |x| + |y| :=
begin
  intros, apply nonneg_le_nonneg_of_squares_le,
  apply add_nonneg; apply complex.norm_nonneg,
  rw [squared_norm_eq_norm_squared, norm_squared_sum],
  rw FOIL, rw [squared_norm_eq_norm_squared, squared_norm_eq_norm_squared],
  rw add_assoc _ ( |x| * |y| ), rw mul_comm ( |y| ), rw ← two_mul,
  apply add_le_add_right, apply add_le_add_left,
  apply mul_le_mul_of_nonneg_left _,
  { apply le_trans, apply zero_le_one, apply le_add_of_nonneg_right zero_le_one },
  rw [norm_conj y, ← norm_mul], transitivity, apply le_abs_self,
  apply abs_Re_le_norm
end

lemma complex.triangle_inequality' : ∀ (x y z : ℂ), |x - y| ≤ |x - z| + |z - y| :=
begin
  intros, rw (_ : x - y = (x - z) + (z - y)),
  apply complex.triangle_inequality,
  rw [← add_sub_assoc, sub_add_cancel]
end

lemma complex.lt_of_lt_triangle_lt (x y z : ℂ) (ε : ℝ) :
  |x - z| < ε/2 → |y - z| < ε/2 → |x - y| < ε :=
by { intros h h', rw norm_sub at h', apply lt_of_le_of_lt (complex.triangle_inequality' x y z),
     rw [← add_self_div_two ε, ← div_add_div_same], exact add_lt_add h h' }

lemma complex.squared_dist (z w : ℂ)
  : |z - w|*|z - w| = z.norm_squared - 2 * Re (z*w.conj) + w.norm_squared :=
begin
  intros, rw squared_norm_eq_norm_squared,
  rw [norm_squared_eq_mul_conj', norm_squared_eq_mul_conj'],
  rw [two_mul], transitivity
    (complex.mul z (complex.conj z)).Re - ((z * complex.conj w).Re + (complex.conj z * w).Re) +
      (complex.mul w (complex.conj w)).Re,
  { rw [sub_eq_add_neg (Re _), neg_add, ← Re_neg, ← Re_neg],
    rw [← Re_additive, ← Re_additive, ← Re_additive],
   apply congr, refl, 
   transitivity (z + -w) * complex.conj (z + -w),
   { rw sub_eq_add_neg, refl },
     transitivity z * (complex.conj z) + (-(z * complex.conj w) + -(complex.conj z * w)) + w * (complex.conj w),
     { rw [conj_add, conj_neg, FOIL], 
       rw ← add_assoc, apply congr,
       { congr, rw neg_mul_eq_mul_neg, rw mul_comm, rw neg_mul_eq_mul_neg },
       { apply neg_mul_neg, } },
     refl },
  rw [← norm_squared_eq_mul_conj', ← norm_squared_eq_mul_conj'],
  apply congr_fun, apply congr_arg, apply congr_arg, apply congr_arg,
  rw Re_conj, rw [conj_mul, conj_of_conj]
end

lemma distrib_scalar_mul_over_add_complex : ∀ r z w,
  complex.scalar_mul r (z + w) = complex.scalar_mul r z + complex.scalar_mul r w :=
by { intros, cases z, cases w, simp [complex.scalar_mul],
     constructor; apply left_distrib, }

lemma distrib_complex_over_scalar_mul_add_real : ∀ x y z,
  complex.scalar_mul (x + y) z = complex.scalar_mul x z + complex.scalar_mul y z :=
by { intros, cases z, simp [complex.scalar_mul],
     constructor; apply right_distrib }

lemma scalar_mul_comm_mul'
  : ∀ w z k, complex.scalar_mul k (w * z) = w * (complex.scalar_mul k z)
  := scalar_mul_comm_mul

lemma norm_squared_div_self
  : ∀ z, complex.scalar_mul (complex.norm_squared z) (1/z) = complex.conj z :=
begin
  intro z, by_cases complex.norm_squared z = 0, 
  { rw norm_squared_zero_implies_zero _ h,
    dsimp [complex.norm_squared], rw [zero_mul, zero_add],
    generalize : 1/complex.zero = w, cases w,
    simp [complex.scalar_mul] },
  cases z, simp [complex.norm_squared, complex.scalar_mul],
  rw mul_div_cancel', rw mul_div_cancel', constructor; refl,
  exact h, exact h
end