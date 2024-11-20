import Mathlib.Data.Real.Sqrt

@[ext] structure Point := (x : ℝ) (y : ℝ)

noncomputable def Distance (A : Point) (B : Point) := Real.sqrt ((A.x - B.x) ^ 2 + (A.y - B.y) ^ 2)

structure Metric_Space (α : Type) (d : α → α → ℝ) :=
  d_nonneg : ∀ A B : α, d A B ≥ 0
  a_eq_b_iff : ∀ A B : α, A = B ↔ d A B = 0
  symm : ∀ A B : α, d A B = d B A
  tri_ineq : ∀ A B C : α, d A C ≤ d A B + d B C

/- Discrete metric omitted as d(A, B) = 0 if A = B seems undecidable on an arbitrary type. -/

instance Real_Line : Metric_Space ℝ (λ A B : ℝ => abs (A - B)) := {
  d_nonneg := λ A B => abs_nonneg (A - B) 
  a_eq_b_iff := λ _ _ => ⟨λ h1 => by simp [h1], λ h1 => sub_eq_zero.mp (abs_eq_zero.mp h1)⟩
  symm := λ A B => abs_sub_comm A B 
  tri_ineq := λ A B C => abs_sub_le A B C
}

example : Metric_Space ℝ (λ A B : ℝ => abs (A - B) ^ 2) → False := by
  intro h1
  have : abs (0 - 2) ^ 2 ≤ abs (0 - 1) ^ 2 + abs (1 - 2) ^ 2 := h1.tri_ineq 0 1 2
  simp [pow_two] at this
  linarith

instance Manhattan_Metric_Space : Metric_Space Point (λ A B : Point => abs (A.x - B.x) + abs (A.y - B.y)) := {
  d_nonneg := λ A B => add_nonneg (abs_nonneg (A.x - B.x)) (abs_nonneg (A.y - B.y))
  a_eq_b_iff := by
    intro A B
    constructor
    intro h1
    rw [h1]
    simp
    intro h1
    have : abs (A.x - B.x) = 0 ∧ abs (A.y - B.y) = 0 := (add_eq_zero_iff' (abs_nonneg (A.x - B.x)) (abs_nonneg (A.y - B.y))).mp h1
    exact Point.ext A B (sub_eq_zero.mp (abs_eq_zero.mp this.left)) (sub_eq_zero.mp (abs_eq_zero.mp this.right))
  symm := λ A B => by rw [abs_sub_comm A.x B.x, abs_sub_comm A.y B.y]
  tri_ineq := by
    intro A B C
    rw [add_assoc, add_comm (abs (A.y - B.y)), add_assoc, ←add_assoc (abs (A.x - B.x))]
    exact add_le_add (abs_sub_le A.x B.x C.x) (by rw [add_comm]; exact abs_sub_le A.y B.y C.y)
} 

noncomputable instance Euclidean_Metric_Space : Metric_Space Point Distance := {
  d_nonneg := λ _ _ => Real.sqrt_nonneg _
  a_eq_b_iff := by 
    intro A B
    constructor
    intro h1
    rw [h1, Distance, sub_self, sub_self, zero_pow (by simp), add_zero, Real.sqrt_zero]
    intro h1
    have : (A.x - B.x) ^ 2 + (A.y - B.y) ^ 2 = 0 := (Real.sqrt_eq_zero (add_nonneg (sq_nonneg (A.x - B.x)) (sq_nonneg (A.y - B.y)))).mp h1
    ext
    have : (A.x - B.x) ^ 2 = 0 := ((add_eq_zero_iff' (sq_nonneg (A.x - B.x)) (sq_nonneg (A.y - B.y))).mp this).left
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
    have : (A.y - B.y) ^ 2 = 0 := ((add_eq_zero_iff' (sq_nonneg (A.x - B.x)) (sq_nonneg (A.y - B.y))).mp this).right
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
  symm := λ _ _ => by rw [Distance, Distance]; ring_nf
  tri_ineq := by 
    intro A B C
    rw [Distance, Distance, Distance]
    let x1 := A.x - B.x
    let x2 := B.x - C.x
    let y1 := A.y - B.y
    let y2 := B.y - C.y
    have h1 : A.x - B.x = x1 := by simp
    have h2 : B.x - C.x = x2 := by simp
    have h3 : A.y - B.y = y1 := by simp
    have h4 : B.y - C.y = y2 := by simp
    have h5 : A.x - C.x = x1 + x2 := by simp
    have h6 : A.y - C.y = y1 + y2 := by simp
    rw [h1, h2, h3, h4, h5, h6]
    have : Real.sqrt ((x1 + x2) ^ 2 + (y1 + y2) ^ 2) ≤ Real.sqrt (x1 ^ 2 + y1 ^ 2) + Real.sqrt (x2 ^ 2 + y2 ^ 2) ↔ 0 ≤ (x1 * y2 - x2 * y1) ^ 2 := by
        constructor
        intro _
        exact sq_nonneg (x1 * y2 - x2 * y1)
        intro h7
        rw [sub_sq] at h7
        have : 2 * (x1 * y2) * (x2 * y1) ≤ (x1 * y2) ^ 2 + (x2 * y1) ^ 2 := by linarith
        have : (x1 * x2) ^ 2 + (y1 * y2) ^ 2 + 2 * (x1 * y2) * (x2 * y1) ≤ (x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2) := by linarith
        have : Real.sqrt ((x1 * x2) ^ 2 + (y1 * y2) ^ 2 + 2 * (x1 * y2) * (x2 * y1)) ≤ Real.sqrt ((x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2)):= Real.sqrt_le_sqrt this
        have thing : 2 * x1 * x2 * y2 * y1 = 2 * (x1 * x2) * (y2 * y1) := by linarith
        rw [add_assoc, add_comm ((y1 * y2) ^ 2), ←add_assoc, mul_assoc, mul_assoc, ←mul_assoc y2, mul_comm y2, ←mul_assoc, mul_assoc x2, ←mul_assoc, ←mul_assoc, thing, mul_comm y2, ←add_sq, Real.sqrt_mul (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sqrt_sq_eq_abs] at this
        rw [mul_self_le_mul_self_iff (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), ←pow_two, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), ←pow_two, add_sq (Real.sqrt (x1 ^ 2 + y1 ^ 2)), Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)), add_sq, add_sq]
        apply le_add_of_sub_left_le
        have helpful_thing : ∀ a b c : ℝ, a + b + c - a = b + c := λ _ _ _ => by linarith
        rw [sub_add_eq_sub_sub, add_sub_add_comm, helpful_thing, helpful_thing]
        apply sub_left_le_of_le_add
        apply sub_le_iff_le_add.mp
        have helpful_thing2 : ∀ a b c d : ℝ, a + b + (c + d) - (b + d) = a + c := λ _ _ _ _ => by linarith
        rw [helpful_thing2]
        have : 2 * abs (x1 * x2 + y1 * y2) ≤ 2 * Real.sqrt (x1 ^ 2 + y1 ^ 2) * Real.sqrt (x2 ^ 2 + y2 ^ 2) := by linarith
        have : 2 * x1 * x2 + 2 * y1 * y2 ≤ 2 * abs (x1 * x2 + y1 * y2) := by 
          rw [mul_assoc, mul_assoc, ←mul_add];
          have : x1 * x2 + y1 * y2 ≤ abs (x1 * x2 + y1 * y2) := le_abs_self _
          linarith
        linarith
    rw [this]
    exact sq_nonneg (x1 * y2 - x2 * y1)
}

noncomputable instance Maximum_Metric_Space : Metric_Space Point (λ A B : Point => max (abs (A.x - B.x)) (abs (A.y - B.y))) := {
  d_nonneg := by 
    intro A B
    cases (max_choice (abs (A.x - B.x)) (abs (A.y - B.y))) with
    | inl h1 =>
      rw [h1]
      exact abs_nonneg (A.x - B.x)
    | inr h1 =>
      rw [h1]
      exact abs_nonneg (A.y - B.y)
  a_eq_b_iff := by
    intro A B
    cases (max_choice (abs (A.x - B.x)) (abs (A.y - B.y))) with
    | inl h1 =>
      constructor
      intro h2
      rw [h1, h2, sub_self, abs_zero]
      intro h2
      rw [h1, abs_eq_zero, sub_eq_zero] at h2
      rw [h2, sub_self, abs_zero] at h1
      cases (le_iff_lt_or_eq.mp (max_eq_left_iff.mp h1)) with
      | inl h3 => exact absurd (abs_nonneg (A.y - B.y)) (not_le_of_gt h3)
      | inr h3 => rw [abs_eq_zero, sub_eq_zero] at h3; exact Point.ext A B h2 h3
    | inr h1 =>
      constructor
      intro h2
      rw [h2, sub_self, sub_self, abs_zero, max_self]
      intro h2
      rw [h1, abs_eq_zero, sub_eq_zero] at h2
      rw [h2, sub_self, abs_zero] at h1
      cases (le_iff_lt_or_eq.mp (max_eq_right_iff.mp h1)) with
      | inl h3 => exact absurd (abs_nonneg (A.x - B.x)) (not_le_of_gt h3)
      | inr h3 => rw [abs_eq_zero, sub_eq_zero] at h3; exact Point.ext A B h3 h2
  symm := λ A _ => by rw [abs_sub_comm, abs_sub_comm A.y]
  tri_ineq := by
    intro A B C
    let x1 := A.x - B.x
    let x2 := B.x - C.x
    let y1 := A.y - B.y
    let y2 := B.y - C.y
    have h1 : A.x - B.x = x1 := by simp
    have h2 : B.x - C.x = x2 := by simp
    have h3 : A.y - B.y = y1 := by simp
    have h4 : B.y - C.y = y2 := by simp
    have h5 : A.x - C.x = x1 + x2 := by simp
    have h6 : A.y - C.y = y1 + y2 := by simp
    rw [h1, h2, h3, h4, h5, h6]
    cases (max_choice (abs (x1 + x2)) (abs (y1 + y2))) with
    | inl h7 =>
      rw [h7]
      exact le_trans (abs_add x1 x2) (add_le_add (le_max_left (abs x1) (abs y1)) (le_max_left (abs x2) (abs y2)))
    | inr h7 =>
      rw [h7]
      exact le_trans (abs_add y1 y2) (add_le_add (le_max_right (abs x1) (abs y1)) (le_max_right (abs x2) (abs y2)))
}

example {A B P Q : α} {X : Metric_Space α d} : d A B + d P Q ≤ d A P + d A Q + d B P + d P Q := add_le_add (by rw [X.symm B P, add_assoc, add_comm (d A Q), ←add_assoc]; exact le_trans (X.tri_ineq A P B) (le_add_of_nonneg_right (X.d_nonneg A Q))) (by rfl)

/- Using a different, easier to work with definition of 'Bijection' than the one given in a text. -/
def Bijection (f : α → β) := (∀ (a b : α), f a = f b → a = b) ∧ (∀ (b : β), ∃ (a : α), f a = b)

def Distance_Preserving (X : Metric_Space α dx) (_ : Metric_Space β dy) (f : α → β) := ∀ A B : α, dy (f A) (f B) = dx A B

structure Isometry (X : Metric_Space α dx) (Y : Metric_Space β dy) (f : α → β) :=
  (Bijective : Bijection f)
  (Distance_Preserving : Distance_Preserving X Y f)

def Motion (X : Metric_Space α d) (f : α → α) := Isometry X X f

example {A B : α} {h : A ≠ B} : Distance_Preserving (X : Metric_Space α dx) (Y : Metric_Space β dy) f → f A ≠ f B := by
  intro h1 h2
  have h3 : dy (f A) (f B) = dx A B := h1 A B
  rw [h2] at h3
  have : dy (f B) (f B) = 0 := by rw [←Y.a_eq_b_iff]
  rw [this] at h3
  have : A = B := by rw [X.a_eq_b_iff]; symm; exact h3
  contradiction

example {x : ℝ} : Motion Real_Line f → f x = f 0 + x ∨ f x = f 0 - x := by
  intro h1
  have : abs (f x - f 0) = abs (x - 0) := h1.Distance_Preserving x 0
  rw [sub_zero, abs_eq_abs] at this
  cases this with
  | inl h2 => left; linarith
  | inr h2 => right; linarith

/-instance : Isometry Manhattan_Metric_Space Maximum_Metric_Space (λ A : Point => Point.mk (A.x + A.y) (A.x - A.y)) :=
  Bijective := by 
    apply And.intro
    simp
    intro a b h1 h2
    ext
    linarith
    linarith
    intro b
    simp
    use (Point.mk (b.y - b.x) (b.y - b.x))
    ext
    simp
  Distance_Preserving := by
    intro A B
    simp
    cases (max_choice (abs (A.x + A.y - (B.x + B.y))) (abs (A.x - A.y - (B.x - B.y)))) with
    | inl h1 =>
      rw [h1, sub_add_eq_sub_sub, ]
     sorry-/

lemma bla (h : a = b) : a * c = b * c := by
