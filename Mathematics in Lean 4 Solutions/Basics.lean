import Mathlib.Data.Real.Basic

namespace Basics21

example (a b c : ℝ) : (c * b) * a = b * (a * c) := by
  rw [mul_comm c b, mul_assoc b c a, mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc a b c, mul_comm a b, mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm, mul_comm a, mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b, h, ←mul_assoc a e]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self];

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add, ←add_assoc]

example (a b c d : ℝ) : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * (c + d) + b * (c + d)       := by rw [add_mul]
                    _ = a * c + a * d + b * (c + d)     := by rw [mul_add]
                    _ = a * c + a * d + (b * c + b * d) := by rw [mul_add]
                    _ = a * c + a * d + b * c + b * d   := by rw [←add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two, pow_two, mul_sub, add_mul, add_mul, mul_comm b a, ←sub_sub, ←add_sub, sub_self, add_zero];

end Basics21

namespace Basics22

variable {R : Type} [Ring R]

theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c ) : b = c := by
  rw [←add_neg_cancel_left a b, ←add_neg_cancel_left a c, add_comm, add_assoc, add_comm b a, h, add_comm a (-a + c), add_assoc, add_comm a c];

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [←add_neg_cancel_left b a, add_comm, add_assoc, h]; nth_rewrite 2 [←add_neg_cancel_left b c]; rw [add_comm b (-b + c), add_assoc]

lemma zero_mul_add_zero_mul {a : R} : 0 * a + 0 * a = 0 * a + 0 := by rw [←add_mul, add_zero, add_zero]

theorem zero_mul (a : R) : 0 * a = 0 := by
  rw [add_left_cancel zero_mul_add_zero_mul]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [←add_right_neg a] at h; rw [add_left_cancel h]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [←add_left_neg b] at h; rw [add_right_cancel h]

theorem neg_neg (a : R) : -(-a) = a := by
  apply neg_eq_of_add_eq_zero; rw [add_left_neg]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg];

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [←one_add_one_eq_two, add_mul, one_mul]

variable {G : Type} [Group G]

lemma a_mul_b_eq_1_inv_b {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [← mul_one a⁻¹, ←h, ←mul_assoc, mul_left_inv, one_mul]

lemma inv_inv (a : G) : a⁻¹⁻¹ = a := by
  rw [a_mul_b_eq_1_inv_b (mul_left_inv a)];

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  nth_rewrite 1 [←inv_inv a]; rw [mul_left_inv]

theorem mul_one (a : G) : a * 1 = a := by
  rw [←mul_left_inv a, ←mul_assoc, mul_right_inv, one_mul]

lemma mul_mul_inv (a b : G) : a = a * (b * b⁻¹) := by
  rw [mul_right_inv, mul_one]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [mul_mul_inv (a * b)⁻¹ a]; nth_rewrite 2 [mul_mul_inv a b]; rw [←mul_assoc a b b⁻¹, mul_assoc, ←mul_assoc, mul_left_inv, one_mul]

end Basics22

namespace Basics23

variable (a b c d e : ℝ)

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  have h₄ : a < c := by apply lt_of_le_of_lt; exact h₀; exact h₁;
  have h₅ : c < e := by apply lt_of_le_of_lt; exact h₂; exact h₃;
  apply lt_trans; exact h₄; exact h₅

/- Not yet possible in mathlib4.

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := sorry

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := sorry 

example (h : a ≤ b) : c - exp b ≤ c - exp a := sorry -/
  
example : abs (a * b) ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h1 : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by {
    have h1 : (a - b) ^ 2 ≥ 0 := pow_two_nonneg (a - b)
    rw [sub_sq' a b] at h1
    have h2 : a ^ 2 + b ^ 2 ≥ 2 * a * b := le_of_sub_nonneg h1
    have h3 : (a ^ 2 + b ^ 2) / 2 ≥ (2 * a * b) / 2 := div_le_div_of_le (show 0 ≤ 2 by linarith) h2
    rw [mul_assoc] at h3
    rwa [mul_div_cancel_left (a * b) (by linarith)] at h3
  }
  have h2 : -(a * b) ≤ (a ^ 2 + b ^ 2) / 2 := by {
    have h1 : (a + b) ^ 2 ≥ 0 := pow_two_nonneg (a + b)
    rw [add_sq' a b] at h1
    rw [←sub_neg_eq_add] at h1
    have h2 : a ^ 2 + b ^ 2 ≥ -(2 * a * b) := le_of_sub_nonneg h1
    have h3 : (a ^ 2 + b ^ 2) / 2 ≥ -(2 * a * b) / 2 := div_le_div_of_le (show 0 ≤ 2 by linarith) (show -(2 * a * b) ≤ a ^ 2 + b ^ 2 from h2)
    rw [mul_assoc] at h3
    rw [neg_div] at h3
    rwa [mul_div_cancel_left (a * b) (show 2 ≠ 0 by linarith)] at h3
  }
  exact abs_le'.mpr (And.intro h1 h2)

end Basics23

namespace Basics24

variable (a b x y z w : ℝ)

example : max a b = max b a := by
  apply le_antisymm
  apply max_le
  apply le_max_right
  apply le_max_left
  apply max_le
  apply le_max_right
  apply le_max_left

example : min (min a b) c = min a (min b c) := by
  cases em (a ≤ b) with
  | inl h1 => {
    rw [min_eq_left h1];
    cases em (a ≤ c) with
    | inl h2 => {
      rw [min_eq_left h2]
      cases em (b ≤ c) with
      | inl h3 => rw [min_eq_left h3, min_eq_left h1]
      | inr h3 => simp at h3; rw [min_eq_right_of_lt h3, min_eq_left h2]
    }
    | inr h2 => {
      rw [not_le] at h2
      cases em (b ≤ c) with
      | inl h3 => rw [min_eq_left h3, min_eq_left h1, min_eq_left (le_trans h1 h3)]
      | inr h3 => rw [not_le] at h3; rw [min_eq_right_of_lt h3]
    }
  }
  | inr h1 => {
    rw [not_le] at h1
    rw [min_eq_right_of_lt h1]
    cases em (b ≤ c) with
    | inl h2 => rw [min_eq_left h2, min_eq_right_of_lt h1]
    | inr h2 => rw [not_le] at h2; rw [min_eq_right_of_lt h2, min_eq_right_of_lt (lt_trans h2 h1)]
  }

example : min a b + c = min (a + c) (b + c) := by
  cases em (a ≤ b) with
  | inl h1 => rw [min_eq_left h1, min_eq_left (add_le_add_right h1 c)]
  | inr h1 => {
    rw [not_le] at h1
    rw [min_eq_right_of_lt h1, min_eq_right_of_lt (add_lt_add_right h1 c)]
  }

example : abs a - abs b ≤ abs (a - b) := by
  have h1 : abs a = abs (a - b + b) := congrArg abs (eq_add_of_sub_eq rfl)
  have h2 : abs (a - b + b) ≤ abs (a - b) + abs (b) := abs_add (a - b) b
  rw [←h1] at h2 
  have h4 : abs a - abs b ≤ abs (a - b) + abs b - abs b := tsub_le_tsub_right h2 (abs b)
  rwa [add_sub_cancel] at h4

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by 
  apply dvd_add
  apply dvd_add
  apply dvd_mul_of_dvd_right
  apply dvd_mul_right
  apply dvd_mul_right
  apply dvd_mul_of_dvd_left
  exact h

variable (m n : ℕ)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat {
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
  }

end Basics24

namespace Basics25

variable {α : Type} [Lattice α]
variable (a b c x y z : α)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat {
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  }

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  apply le_trans inf_le_left inf_le_left
  apply le_inf
  apply le_trans inf_le_left inf_le_right
  apply inf_le_right
  apply le_inf
  apply le_inf
  apply inf_le_left
  apply le_trans inf_le_right inf_le_left
  apply le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat {
    apply sup_le
    apply le_sup_right
    apply le_sup_left
  }

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  apply le_trans le_sup_left le_sup_right
  apply le_trans le_sup_right le_sup_right
  apply sup_le
  apply le_trans le_sup_left le_sup_left
  apply sup_le
  apply le_trans le_sup_right le_sup_left
  apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  rfl
  apply le_sup_left

theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm
  apply sup_le
  rfl
  apply inf_le_left
  apply le_sup_left

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  apply le_inf
  apply sup_le_sup
  rfl
  apply inf_le_left
  apply sup_le_sup
  rfl
  apply inf_le_right
  rw [h]
  apply sup_le
  rw [inf_comm, absorb1]
  apply le_sup_left
  rw [inf_comm, h]
  apply sup_le_sup
  apply inf_le_right
  rw [inf_comm]

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  apply le_antisymm
  rw [h]
  apply le_inf
  have h1 : (a ⊓ b) ⊔ a = a := by apply le_antisymm; apply sup_le; apply inf_le_left; rfl; apply le_sup_right
  rw [h1]
  apply inf_le_left
  have h1 : a ⊓ b ⊔ c = (c ⊔ a) ⊓ (c ⊔ b) := by rw [sup_comm, h]
  rw [h1]
  apply inf_le_inf
  apply le_sup_right
  rw [sup_comm]
  apply sup_le
  apply inf_le_inf
  rfl
  apply le_sup_left
  apply inf_le_inf
  rfl
  apply le_sup_right

variable {R : Type} [OrderedRing R]
variable (a b c : R)

example : a ≤ b → 0 ≤ b - a := by
  intro h
  apply le_of_add_le_add_right
  rwa [zero_add, sub_add, sub_self, sub_zero]

example : 0 ≤ b - a → a ≤ b := by
  intro h1
  have h2 : 0 + a ≤ b - a + a := by apply add_le_add_right; exact h1
  rwa [zero_add, sub_add, sub_self, sub_zero] at h2

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h2 : 0 ≤ b - a := sub_nonneg_of_le h
  have h3 : 0 ≤ (b - a)* c := Left.mul_nonneg h2 h'
  have h4 : 0 ≤ b * c - a * c := by rwa [sub_mul] at h3
  have h5 : a * c ≤ b * c := le_of_sub_nonneg h4
  exact h5

/- Not yet possible in mathlib4.

variable {X : Type} [MetricSpace X]
variable (x y z : X)

example (x y : X) : 0 ≤ dist x y := sorry -/
