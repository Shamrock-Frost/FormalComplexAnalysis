variables {α : Type _} {β : Type _} {γ : Type _}

def fun.im (f : α → β) (A : set α) := { b : β | ∃ a, a ∈ A ∧ b = f a }
def fun.pre_im (f : α → β) (B : set β) := { a : α | f a ∈ B }

def fun.pre_im_of_inv_eq_im (f : α → β) (g : β → α) (B : set β)
  (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) 
  : fun.pre_im f B = fun.im g B :=
begin
  dsimp [fun.pre_im, fun.im], funext, apply propext,
  suffices : B (f a) ↔ ∃ b : β, b ∈ B ∧ a = g b, exact this,
  constructor; intro h,
  { existsi f a, constructor, assumption, symmetry, apply hgf },
  { cases h with b h, cases h with hB h, rw h, rw hfg, assumption }
end

def im_of_comp : ∀ (f : α → β) (g : β → γ) (A : set α),
  fun.im (g ∘ f) A = fun.im g (fun.im f A) :=
begin
  intros, funext, apply propext, constructor; intro h,
  { cases h with a h, existsi f a, constructor,
    existsi a, constructor, exact h.left, refl, exact h.right },
  { cases h with fa h, cases h with hfa hb,
    cases hfa with a ha, cases ha with ha hfa,
    existsi a, constructor, assumption,
    dsimp [(∘)], rw ← hfa, assumption }
end

def eq_symm_iff (a b : α) : a = b ↔ b = a :=
⟨eq.symm, eq.symm⟩

lemma classical.dne : ∀ P, ¬ ¬ P ↔ P :=
begin
  intro P, constructor; intro h,
  { cases (classical.em P), assumption, trivial },
  exact (λ nh, absurd h nh),
end