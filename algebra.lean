lemma {u} FOIL {R : Type u} [ring R] : ∀ a b c d : R, (a + b) * (c + d) = a*c + a*d + b*c + b*d :=
by { intros, rw [left_distrib, right_distrib, right_distrib], ac_refl }

lemma {u} FOIL_neg_square {R : Type u} [comm_ring R] : ∀ a b : R, (a - b) * (a - b) = a*a + (-(a*b)+ -(a*b)) + b*b :=
by { intros, rw sub_eq_add_neg, rw FOIL,
     rw neg_mul_neg, repeat { rw add_assoc }, congr,
     rw neg_mul_eq_mul_neg, rw [mul_comm a b, neg_mul_eq_neg_mul] }

lemma {u} FOIL_sub {R : Type u} [ring R] : ∀ a b c d : R, (a - b) * (c - d) = a*c - a*d - b*c + b*d :=
by { intros, repeat { rw sub_eq_add_neg }, rw FOIL, rw neg_mul_eq_mul_neg, rw neg_mul_eq_neg_mul,
     apply congr_arg, rw [← neg_mul_eq_mul_neg, ← neg_mul_eq_neg_mul, neg_neg] }

lemma difference_of_squares {R} [comm_ring R] : ∀ x y : R, x * x - y*y = (x - y)*(x + y) :=
begin
  intros, rw sub_eq_add_neg, rw sub_eq_add_neg,
  rw FOIL, rw add_assoc (x*x), rw mul_comm (-y) x, 
  rw ← neg_mul_eq_mul_neg, rw ← sub_eq_add_neg (x*y),
  rw sub_self, rw add_zero, congr, rw neg_mul_eq_mul_neg,
  rw mul_comm
end

lemma div_of_div_eq_self {F} [field F] : ∀ x y : F, x ≠ 0 → y ≠ 0 → x/(x/y) = y :=
begin
  intros, rw div_eq_mul_one_div x y,
  rw field.div_mul_eq_div_mul_one_div _ a,
  rw div_self a, rw one_mul,
  rw [one_div_eq_inv, one_div_eq_inv],
  rw division_ring.inv_inv a_1,
  apply one_div_ne_zero a_1,
end

lemma square_neg_one {R} [ring R] : (-1)*(-1) = (1 : R) :=
begin
  apply eq_of_sub_eq_zero, rw sub_eq_add_neg, 
  transitivity (-1)*(-1) + (-1)*(1:R), rw mul_one,
  rw ← left_distrib, rw neg_add_self, rw mul_zero
end

lemma weird_analysis_trick {R} [ring R] 
  : ∀ a b c d : R, a * c = (a - b) * (c - d) + a * d + b * c - b * d :=
begin
  intros, rw [sub_eq_add_neg a, sub_eq_add_neg c],
  rw FOIL, rw [← neg_mul_eq_neg_mul b (-d), mul_neg_eq_neg_mul_symm b d, neg_neg],
  rw add_right_comm _ (b*d), rw add_right_comm _ (b*d), rw add_sub_assoc,
  rw [sub_self, add_zero], rw add_right_comm _ (-b*c),
  rw [← neg_mul_eq_neg_mul, add_assoc, neg_add_self, add_zero],
  rw [add_assoc, mul_neg_eq_neg_mul_symm, neg_add_self, add_zero]
end

lemma eq_zero_of_sqr_eq_zero {F} [division_ring F] [decidable_eq F]
  : ∀ {x : F}, x * x = 0 → x = 0 :=
begin
  intros x h, by_contra h', refine (_ : x * x ≠ 0) h,
  apply division_ring.mul_ne_zero h' h'
end

lemma classical.l_or_r_eq_zero_of_mul_eq_zero {F} [division_ring F]
  : ∀ {x y : F}, x * y = 0 → x = 0 ∨ y = 0 :=
begin
  intros x y h, apply classical.by_contradiction,
  rw @decidable.not_or_iff_and_not _ _ (classical.prop_decidable _) (classical.prop_decidable _),
  intro h', apply division_ring.mul_ne_zero h'.left h'.right, assumption
end

lemma eq_sub_implies_sub_zero {G} [add_comm_group G]
  : ∀ x y : G, x = x - y → y = 0 :=
begin
  intros,
  transitivity x - (x - y), { rw sub_sub_self x y },
  rw ← a, apply sub_self
end