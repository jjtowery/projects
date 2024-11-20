import Mathlib.Data.Real.Basic

namespace AbstractAlgebra61

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_comm (a b : point) : add a b = add b a := by
  rw [add, add]
  ext
  dsimp
  repeat apply add_comm

theorem add_x (a b : point) : (a.add b).x = a.x + b.x := rfl

protected theorem add_assoc (a b c : point) : (a.add b).add c = a.add (b.add c) := by
  simp [add]
  exact ⟨by rw [add_assoc], by rw [add_assoc], by rw [add_assoc]⟩

def smul (r : ℝ) (a : point) : point := ⟨a.x * r, a.y * r, a.z * r⟩ 

theorem smul_distrib (r : ℝ) (a b : point) : (smul r a).add (smul r b) = smul r (a.add b) := by
  simp [add, smul]
  exact ⟨by rw [←right_distrib], by rw [←right_distrib], by rw [←right_distrib]⟩

structure standard_two_simplex :=
  (x : ℝ)
  (y : ℝ)
  (z : ℝ)
  (x_nonneg : 0 ≤ x)
  (y_nonneg : 0 ≤ y)
  (z_nonneg : 0 ≤ z)
  (sum_eq   : x + y + z = 1)

def weighted_average (lambda : ℝ) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1) (a b : standard_two_simplex) : standard_two_simplex := { 
  x        := lambda * a.x + (1 - lambda) * b.x
  y        := lambda * a.y + (1 - lambda) * b.y
  z        := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (sub_nonneg.mpr lambda_le) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (sub_nonneg.mpr lambda_le) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (sub_nonneg.mpr lambda_le) b.z_nonneg)
  sum_eq   := by 
    have h1 : lambda * a.x + (1 - lambda) * b.x + (lambda * a.y + (1 - lambda) * b.y) + (lambda * a.z + (1 - lambda) * b.z) = lambda * (a.x + a.y + a.z) + (1 - lambda) * (b.x + b.y + b.z) := by linarith
    rw [h1, a.sum_eq, b.sum_eq]
    linarith
}

end point

end AbstractAlgebra61

namespace AbstractAlgebra62

structure add_group₁ (α : Type) :=
  (add : α → α → α)
  (zero : α)
  (neg : α → α)
  (add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
  (add_zero : ∀ x : α, add x zero = x)
  (zero_add : ∀ x : α, add zero x = x)
  (add_left_neg : ∀ x : α, add (neg x) x = zero)

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : point) : point := ⟨-a.x, -a.y, -a.z⟩

def zero : point := ⟨0, 0, 0⟩

def add_group_point : add_group₁ point := {
  add          := add
  zero         := zero
  neg          := neg
  add_assoc    := by intro x y z; simp [add]; exact ⟨by rw [add_assoc], by rw [add_assoc], by rw [add_assoc]⟩
  add_zero     := by intro x; simp [add, zero]
  zero_add     := by intro x; simp [add, zero]
  add_left_neg := by intro x; simp [add, neg, zero]
}

end point

class add_group₂ (α : Type) := 
  (add : α → α → α)
  (zero : α) 
  (neg : α → α)
  (add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
  (add_zero : ∀ x : α, add x zero = x)
  (zero_add : ∀ x : α, add zero x = x)
  (add_left_neg : ∀ x : α, add (neg x) x = zero)

instance has_add_add_group₂ {α : Type} [add_group₂ α] : Add α := ⟨add_group₂.add⟩

instance has_zero_add_group₂ {α : Type} [add_group₂ α] : Zero α := ⟨add_group₂.zero⟩

instance has_neg_add_group₂ {α : Type} [add_group₂ α] : Neg α := ⟨add_group₂.neg⟩

instance : add_group₂ point := {
  add          := point.add
  zero         := point.zero
  neg          := point.neg
  add_assoc    := by intro x y z; simp [point.add]; exact ⟨by rw [add_assoc], by rw [add_assoc], by rw [add_assoc]⟩
  add_zero     := by intro x; simp [point.add, point.zero]
  zero_add     := by intro x; simp [point.add, point.zero]
  add_left_neg := by intro x; simp [point.add, point.zero, point.neg]
}

end AbstractAlgebra62

namespace AbstractAlgebra63

@[ext] structure gaussint := (re : ℤ) (im : ℤ)

instance : Zero gaussint := ⟨0, 0⟩
instance : One gaussint := ⟨1, 0⟩
instance : Add gaussint := ⟨λ x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg gaussint := ⟨λ x => ⟨-x.re, -x.im⟩⟩
instance : Mul gaussint := ⟨λ x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : gaussint) = ⟨0, 0⟩ := rfl
theorem one_def : (1 : gaussint) = ⟨1, 0⟩ := rfl
theorem add_def (x y : gaussint) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
theorem neg_def (x : gaussint) : -x = ⟨-x.re, -x.im⟩ := rfl
theorem mul_def (x y : gaussint) : x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ := rfl

@[simp] theorem zero_re : (0 : gaussint).re = 0 := rfl
@[simp] theorem zero_im : (0 : gaussint).im = 0 := rfl
@[simp] theorem one_re : (1 : gaussint).re = 1 := rfl
@[simp] theorem one_im : (1 : gaussint).im = 0 := rfl
@[simp] theorem add_re (x y : gaussint) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : gaussint) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : gaussint) : (-x).re = - x.re := rfl
@[simp] theorem neg_im (x : gaussint) : (-x).im = - x.im := rfl
@[simp] theorem mul_re (x y : gaussint) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : gaussint) : (x * y).im = x.re * y.im + x.im * y.re := rfl

instance : CommRing gaussint := {
  zero := 0
  one := 1
  add := λ x y => x + y
  neg := λ x => -x
  mul := λ x y => x * y
  add_assoc := by intros; ext; simp; ring; simp; ring
  zero_add := by intros; ext; simp; simp
  add_zero := by intros; ext; simp; simp
  add_left_neg := by intros; ext; simp; simp
  add_comm := by intros; ext; simp; ring; simp; ring
  mul_assoc := by intros; ext; simp; ring; simp; ring
  one_mul := by intros; ext; simp; simp
  mul_one := by intros; ext; simp; simp
  left_distrib := by intros; ext; simp; ring; simp; ring
  right_distrib := by intros; ext; simp; ring; simp; ring
  mul_comm := by intros; ext; simp; ring; simp; ring
  zero_mul := by intros; ext; simp; simp
  mul_zero := by intros; ext; simp; simp
}

instance : Nontrivial gaussint := by
  use 0
  use 1
  simp
  rw [gaussint.ext_iff]
  simp

theorem sq_add_sq_eq_zero {α : Type} [LinearOrderedRing α] (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  intro h1
  have h2 : x ^ 2 = - y ^ 2 := by 
    have : x ^ 2 + y ^ 2 - y ^ 2 = 0 - y ^ 2 := congrFun (congrArg HSub.hSub h1) (y ^ 2)
    rwa [add_sub_assoc, sub_self, add_zero, zero_sub] at this
  have h3 : -y ^ 2 ≤ 0 := by simp; exact pow_two_nonneg y
  cases (eq_or_lt_of_le (pow_two_nonneg x)) with
  | inl h4 => cases (eq_or_lt_of_le h3) with
    | inl h5 => exact ⟨sq_eq_zero_iff.mp (id (Eq.symm h4)), sq_eq_zero_iff.mp (zero_eq_neg.mp (id (Eq.symm h5)))⟩
    | inr h5 => exact ⟨sq_eq_zero_iff.mp (id (Eq.symm h4)), by simp_all⟩
  | inr h4 => cases (eq_or_lt_of_le h3) with
    | inl h5 => exact ⟨by rw [h2] at h4; rw [h5] at h4; exact absurd (Eq.not_lt rfl) (not_not_intro h4), by simp_all⟩
    | inr h5 => exact ⟨by rw [←h2] at h5; exact absurd (Eq.not_lt rfl) (not_not_intro (lt_trans h4 h5)), by rw [←h2] at h5; exact absurd (Eq.not_lt rfl) (not_not_intro (lt_trans h4 h5))⟩
  intro h1
  rw [h1.left, h1.right]
  simp

def norm (x : gaussint) := x.re ^ 2 + x.im ^ 2

@[simp] theorem norm_nonneg (x : gaussint) : 0 ≤ norm x := le_add_of_le_of_nonneg (pow_two_nonneg x.re) (pow_two_nonneg x.im)

theorem norm_eq_zero (x : gaussint) : norm x = 0 ↔ x = 0 := by
  constructor
  intro h1
  rw [norm, sq_add_sq_eq_zero] at h1
  exact Iff.mpr (gaussint.ext_iff x 0) h1
  intro h1
  rw [h1]
  simp

theorem norm_pos (x : gaussint) : 0 < norm x ↔ x ≠ 0 := by
  constructor
  intro h1 h2
  rw [h2] at h1
  contradiction
  intro h1
  rw [norm]
  cases (eq_or_lt_of_le (pow_two_nonneg x.re)) with
  | inl h2 => cases (eq_or_lt_of_le (pow_two_nonneg x.im)) with
    | inl h3 => exact absurd (gaussint.ext x 0 (sq_eq_zero_iff.mp (id (Eq.symm h2))) (sq_eq_zero_iff.mp (id (Eq.symm h3)))) h1
    | inr h3 => rw [←h2]; simpa
  | inr h2 => cases (eq_or_lt_of_le (pow_two_nonneg x.im)) with
    | inl h3 => rw [←h3]; simpa
    | inr h3 => exact lt_add_of_pos_of_lt' h2 h3

theorem norm_mul (x y : gaussint) : norm (x * y) = norm x * norm y := by
  simp [norm]
  ring

end AbstractAlgebra63
