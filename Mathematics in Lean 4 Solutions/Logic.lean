import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch

namespace Logic31

lemma my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    abs (x * y) = abs x * abs y := by apply abs_mul
              _ ≤ abs x * ε     := by apply mul_le_mul; rfl; exact le_of_lt ylt; apply abs_nonneg; apply abs_nonneg
              _ < 1 * ε         := by rw [mul_lt_mul_right]; apply lt_of_lt_of_le; exact xlt; exact ele1; exact epos
              _ = ε             := by apply one_mul

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

theorem fn_lb_add (hfa : fn_lb f a) (hgb : fn_lb g b) : fn_lb (λ x => f x + g x) (a + b) := by
  intro x
  simp
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : fn_lb f 0) (nng : fn_lb g 0) : fn_lb (λ x => f x * g x) 0 := by
  intro x
  simp
  apply mul_nonneg
  apply nnf
  apply nng

theorem fn_ub_mul (hfa : fn_ub f a) (hfb : fn_ub g b) (nng : fn_lb g 0) (nna : 0 ≤ a) : fn_ub (λ x => f x * g x) (a * b) := by
  intro x
  simp
  apply mul_le_mul
  apply hfa
  apply hfb
  apply nng
  exact nna

example {c : ℝ} {f : ℝ → ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone (λ x => c * f x) := by
  intro a b h1
  simp
  exact mul_le_mul_of_nonneg_left (mf h1) nnc

example {f : ℝ → ℝ} {g : ℝ → ℝ} (mf : Monotone f) (mg : Monotone g) : Monotone (λ x => f (g x)) := by
  intro a b h1
  simp
  exact mf (mg h1)

def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x => f x * g x) := by
  intro x
  simp
  calc
    f x * g x = (-f x) * (-g x)           := by rw [neg_mul_neg]
            _ = (- -f (-x)) * (- -g (-x)) := by rw [fn_odd] at of; rw [fn_odd] at og; rw [of, og]
            _ = f (-x) * g (-x)           := by rw [neg_neg, neg_neg]

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x => f x * g x) := by
  intro x
  simp
  calc
    f x * g x = f (-x) * (- g (-x)) := by rw [fn_odd] at og; rw [fn_even] at ef; rw [og, ef]
            _ = - (f (-x) * g (-x)) := mul_neg (f (-x)) (g (-x))

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x => f (g x)) := by
  intro x
  simp
  calc
    f (g x) = f (- g (-x))   := by rw [fn_odd] at og; rw [og]
          _ = f (- - g (-x)) := by rw [fn_even] at ef; rw [ef]
          _ = f (g (-x))     := by rw [neg_neg]

variable {α : Type} (r s t : Set α)

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h1 h2 a h3
  exact h2 (h1 h3)

variable {α : Type} [PartialOrder α]
variable (s : Set α) (a b : α)

def set_ub (s : Set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b := by
  intro c h1 
  exact le_trans (h c h1) h'

example {c : ℝ} (h : c ≠ 0) : Function.Injective (λ x => c * x) := by
  intro a b h1
  rw [mul_eq_mul_left_iff] at h1
  cases h1
  assumption
  contradiction

variable {α : Type} {β : Type} {γ : Type}
variable {g : β → γ} {f : α → β}

example (injg : Function.Injective g) (injf : Function.Injective f) : Function.Injective (λ x => g (f x)) := by
  intro a b h1
  simp at h1
  exact injf (injg h1)

end Logic31

namespace Logic32

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable (f g : ℝ → ℝ)

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) : fn_has_lb (λ x => f x + g x) := by
  cases lbf with
  | intro a h1 => cases lbg with
    | intro b h2 => use a + b; apply Logic31.fn_lb_add h1 h2

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0) : fn_has_ub (λ x => c * f x) := by
  cases ubf with
  | intro a h1 => 
  use c * a
  intro b
  apply mul_le_mul_of_nonneg_left
  apply h1
  exact h

example {a b c : ℝ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) := by
  cases divab with
  | intro d h1 => cases divac with
    | intro e h2 => 
    rw [h1, h2]
    use (d + e)
    rw [mul_add]

example {c : ℝ} (h : c ≠ 0) : Function.Surjective (λ x => c * x) := by
  intro b
  use b / c
  simp
  exact mul_div_cancel' b h

variable {α : Type} {β : Type} {γ : Type}
variable {g : β → γ} {f : α → β}

example (surjg : Function.Surjective g) (surjf : Function.Surjective f) : Function.Surjective (λ x => g (f x)) := by
  intro b
  simp
  cases surjg b with
  | intro a h1 => cases surjf a with
    | intro c h2 => use c; rw [h2, h1]

end Logic32

namespace Logic33

example (h : ∀ a, ∃ x, f x < a) : ¬ Logic32.fn_has_lb f := by
  intro h1
  cases h1 with
  | intro a h1 => cases h a with
    | intro b h2 => rw [←not_le] at h2; exact absurd (h1 b) h2

example : ¬ Logic32.fn_has_ub (λ x => x) := by
  intro h1
  cases h1 with
  | intro a h1 => 
  rw [Logic32.fn_ub] at h1 
  have h2 : a + 1 ≤ a := h1 (a + 1)
  have h3 : a < a + 1 := lt_add_one a
  rw [←not_le] at h3
  exact absurd h2 h3

example {a b : ℝ} {f : ℝ → ℝ} (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h1
  exact absurd h' (not_lt_of_ge (h h1))

example {f : ℝ → ℝ} (h : a ≤ b) (h' : f b < f a) : ¬ Monotone f := by
  intro h1
  exact absurd h' (not_lt_of_ge (h1 h))

example : ¬ ∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := λ _ : ℝ => (0 : ℝ)
  have monof : Monotone f := by intro a b _; exact refl (f b)
  have h' : f 1 ≤ f 0 := le_refl _
  have h1 : 1 ≤ 0 := h monof h' 
  exact absurd h1 (by simp)

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h1
  have h2 : x < x / 2 := h (x / 2) (half_pos h1)
  have h3 : x / 2 ≤ x := div_le_self (le_of_lt h1) one_le_two
  exact absurd (not_le_of_gt h2) (by intro a; contradiction)

variable {α : Type} (P : α → Prop) (Q : Prop)

theorem neg_ex_forall_neg (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := by
  intro a h1
  exact absurd (Exists.intro a h1) h

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x := by
  intro h1
  cases h1 with
  | intro a h1 => exact absurd h1 (h a)

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x := by
  intro h1
  cases h with
  | intro a h2 => exact absurd (h1 a) h2

open Classical

example (h : ¬ ¬ Q) : Q := by
  apply Classical.by_contradiction
  intro h1
  exact absurd h1 h

example (h : Q) : ¬ ¬ Q := by
  intro h1
  exact absurd h h1

example (h : ¬ Logic32.fn_has_ub f) : ∀ a, ∃ x, f x > a := by
  intro a
  apply Classical.by_contradiction
  intro h1
  have h2 : ∀ x, ¬ f x > a := by apply neg_ex_forall_neg; exact h1
  have h3 : ∀ x, f x ≤ a := λ x => le_of_not_lt (h2 x)
  have h4 : Logic32.fn_has_ub f := Exists.intro a h3
  exact absurd h4 h

example {f : ℝ → ℝ} (h : ¬ Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg at h
  exact h


end Logic33

namespace Logic34

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n ) : m ∣ n ∧ ¬ n ∣ m := by
  cases h with
  | intro h1 h2 =>
    have h3 : ¬ n ∣ m := by
      intro h3
      cases h1 with
      | intro a h4 => cases h3 with
        | intro b h5 =>
          rw [h4] at h5
          have h6 : m / m = (m * a * b) / m := congrArg₂ HDiv.hDiv h5 rfl
          have h7 : m ≠ 0 := by 
            intro h7
            rw [h7, zero_mul] at h4
            have h8 : m = n := by rw [h4, h7]
            exact absurd h8 h2
          have h8 : 0 < m := by
            apply Nat.pos_of_ne_zero
            exact h7
          have h9 : 1 = (m * a * b) / m := by 
            rwa [Nat.div_self] at h6
            exact h8
          have h10 : 1 = a * b := by 
            rwa [mul_assoc, Nat.mul_div_cancel_left] at h9
            exact h8
          rw [eq_comm, Nat.mul_eq_one_iff] at h10
          cases h10 with
          | intro h10 h11 =>
            rw [h10, mul_one, eq_comm] at h4
            exact absurd h4 h2
    exact And.intro h1 h3 

example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  apply Iff.intro
  intro h1
  cases h1 with
  | intro h1 h2 =>
    have h3 : x ≠ y := by
      exact LT.lt.ne (lt_of_not_le h2)
    exact And.intro h1 h3
  intro h1
  cases h1 with
  | intro h1 h2 =>
    have h3 : ¬ y ≤ x := by
      simp
      exact Ne.lt_of_le h2 h1
    exact And.intro h1 h3

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have h' : x ^ 2 = 0 := by
    rw [add_eq_zero_iff'] at h
    exact h.1
    apply pow_two_nonneg
    apply pow_two_nonneg
  rw [pow_two, mul_eq_zero] at h'
  cases h'
  assumption
  assumption

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  apply Iff.intro
  intro h1
  apply And.intro
  exact aux h1
  rw [add_comm] at h1
  exact aux h1
  intro h1
  cases h1 with
  | intro h1 h2 => rw [h1, h2, zero_pow, add_zero]; simp

theorem not_monotone_iff {f : ℝ → ℝ} : ¬ Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  apply Iff.intro
  intro h1
  exact h1
  intro h1
  exact h1

example : ¬ Monotone (λ x : ℝ => -x) := by
  rw [not_monotone_iff]
  use 1
  use 2
  apply And.intro
  linarith
  linarith

variable {α : Type} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  apply Iff.intro
  intro h1
  exact And.intro (le_of_lt h1) (LT.lt.ne h1)
  intro h1
  cases h1 with
  | intro h1 h2 =>
    rw [le_iff_eq_or_lt] at h1
    apply Or.elim h1
    intro h3
    contradiction
    intro h3
    exact h3

variable {α : Type} [Preorder α]
variable (a b c : α)

example : ¬ a < a := by
  rw [lt_iff_le_not_le]
  push_neg
  intro h1
  exact h1

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  intro h1
  intro h2
  cases h1 with
  | intro h3 h4 =>
    cases h2 with
    | intro h5 h6 =>
      apply And.intro
      apply le_trans h3 h5
      intro h7
      have h8 : b ≤ a := le_trans h5 h7
      contradiction
end Logic34

namespace Logic35

theorem le_abs_self (x : ℝ) : x ≤ abs x := by
  rw [le_iff_lt_or_eq]
  cases (le_or_gt 0 x) with
  | inl h1 => right; rw [eq_comm]; exact abs_of_nonneg h1
  | inr h1 => left; rw [abs_of_neg, lt_neg_self_iff]; exact h1; exact h1

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x := by
  rw [le_iff_lt_or_eq]
  cases (lt_or_ge 0 x) with
    | inl h1 => left; rw [abs_of_nonneg, neg_lt_self_iff]; exact h1; rw [le_iff_lt_or_eq]; left; exact h1
    | inr h1 => right; simp at h1; rw [le_iff_lt_or_eq] at h1; cases h1 with
      | inl h1 => rw [abs_of_neg]; exact h1
      | inr h1 => rw [h1]; rw [neg_zero, abs_zero]

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y := by
  cases (le_or_gt x 0) with
  | inl h1 => cases (le_or_gt y 0) with
    | inl h2 =>
      have h3 : x + y ≤ 0 := by linarith
      rw [le_iff_lt_or_eq] at h3 
      cases h3 with
      | inl h3 =>
        have h4 : abs (x + y) = abs x + abs y := calc
          abs (x + y) = -(x + y)      := by exact abs_of_neg h3  
                    _ = - x - y       := by linarith
                    _ = abs x - y     := by rw [le_iff_lt_or_eq] at h1; cases h1 with
                      | inl h4 => simp; rw [eq_comm]; apply abs_of_neg h4
                      | inr h4 => simp; rw [h4, neg_zero, abs_zero];
                    _ = abs x + abs y := by rw [le_iff_lt_or_eq] at h2; cases h2 with
                      | inl h4 => rw [abs_of_neg h4]; linarith
                      | inr h4 => rw [h4, sub_zero, abs_zero, add_zero]
        rw [le_iff_lt_or_eq]
        right
        exact h4
      | inr h3 =>
        have h4 : x = 0 := by linarith
        have h5 : y = 0 := by linarith
        rw [h3, h4, h5, abs_zero, add_zero]
        apply le_refl
    | inr h2 =>
      cases (le_or_gt (x + y) 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [le_iff_lt_or_eq] at h1; cases h1 with
          | inl h4 => rw [abs_of_neg h3, abs_of_neg h4, abs_of_nonneg (by linarith)]; linarith
          | inr h4 => rw [h4, zero_add, abs_zero, zero_add]
        | inr h3 =>
          rw [h3, abs_zero]
          rw [le_iff_lt_or_eq] at h1; cases h1 with
          | inl h4 => rw [abs_of_neg h4, abs_of_nonneg (by linarith)]; linarith
          | inr h4 => rw [h4, abs_zero, zero_add, abs_of_nonneg (by linarith)]; linarith
      | inr h3 => rw [abs_of_nonneg (by linarith)]; rw [le_iff_lt_or_eq] at h1; cases h1 with
        | inl h4 => rw [abs_of_neg h4, abs_of_nonneg (by linarith)]; linarith
        | inr h4 => rw [h4, zero_add, abs_zero, zero_add, abs_of_nonneg (by linarith)]
  | inr h1 => cases (le_or_gt y 0) with
    | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
      | inl h2 => cases (le_or_gt (x + y) 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg h3, abs_of_nonneg (by linarith), abs_of_neg h2]; linarith
          | inr h3 => rw [h3, abs_zero, abs_of_nonneg (by linarith), abs_of_neg h2]; linarith
        | inr h3 => rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg h2]; linarith
      | inr h2 => rw [h2, add_zero, abs_zero, add_zero]
    | inr h2 => rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y := by
  apply Iff.intro
  intro h1
  cases (le_or_gt x 0) with
    | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
      | inl h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg h3] at h1; right; exact h1
          | inr h3 => rw [h3]; left; exact h2
        | inr h3 => rw [abs_of_nonneg (by linarith)] at h1; left; exact h1
      | inr h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [h2]; right; linarith
          | inr h3 => rw [h3, abs_zero] at h1; exact absurd h2 (LT.lt.ne h1)
        | inr h3 => rw [abs_of_nonneg (by linarith)] at h1; left; exact h1
    | inr h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [abs_of_neg h3] at h1; right; exact h1
        | inr h3 => rw [h3, abs_zero] at h1; exact absurd h1 (asymm_of LT.lt h2)
      | inr h3 => rw [abs_of_nonneg (by linarith)] at h1; left; exact h1
  intro h1
  cases h1 with
  | inl h1 => cases (le_or_gt x 0) with
    | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
      | inl h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg h3]; exact Trans.simple h2 (lt_neg_of_lt_neg h3)
          | inr h3 => rw [h3, abs_zero]; exact h2
        | inr h3 => rw [abs_of_nonneg (by linarith)]; exact h1;
      | inr h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg (by linarith)]; linarith
          | inr h3 => rw [h2, h3] at h1; contradiction
        | inr h3 => rw [abs_of_nonneg (by linarith)]; exact h1
    | inr h2 => cases (le_or_gt y 0) with
      | inr h3 => rw [abs_of_nonneg (by linarith)]; exact h1
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inr h3 => rw [h3] at h1; rw [h3, abs_zero]; exact h1
        | inl h3 => rw [abs_of_nonneg (by linarith)]; exact h1
  | inr h1 => cases (le_or_gt x 0) with
    | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
      | inl h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg h3]; exact h1
          | inr h3 => rw [h3, abs_zero]; exact h2
        | inr h3 => rw [abs_of_nonneg (by linarith)]; exact Trans.simple h2 h3
      | inr h2 => cases (le_or_gt y 0) with
        | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
          | inl h3 => rw [abs_of_neg h3]; exact h1
          | inr h3 => rw [h2, h3, neg_zero] at h1; contradiction
        | inr h3 => rw [abs_of_nonneg (by linarith), h2]; exact h3
    | inr h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [abs_of_neg h3]; exact h1
        | inr h3 => rw [h3, abs_zero]; rwa [h3, neg_zero] at h1
      | inr h3 => have h4 : -y < 0 := neg_lt_of_neg_lt h3; have h5 : x < 0 := Trans.simple h1 h4; rw [abs_of_nonneg (by linarith)]; exact Trans.simple h5 h3
    
theorem abs_lt : abs x < y ↔ - y < x ∧ x < y := by
  apply Iff.intro
  intro h1
  cases (le_or_gt x 0) with
  | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
    | inl h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [abs_of_neg h2] at h1; linarith
        | inr h3 => rw [abs_of_neg h2] at h1; linarith
      | inr h3 => 
        rw [abs_of_neg h2] at h1
        have h4 : -y < x := by linarith
        have h5 : x < y := by linarith
        exact And.intro h4 h5
    | inr h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [h2, abs_zero] at h1; linarith
        | inr h3 => rw [h2, h3, abs_zero] at h1; linarith
      | inr h3 => 
        rw [h2]
        have h4 : -y < 0 := by linarith
        have h5 : 0 < y := by linarith
        exact And.intro h4 h5
  | inr h2 => cases (le_or_gt y 0) with
    | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
      | inl h3 => rw [abs_of_nonneg (by linarith)] at h1; linarith
      | inr h3 => rw [abs_of_nonneg (by linarith)] at h1; linarith
    | inr h3 => 
      rw [abs_of_nonneg (by linarith)] at h1
      have h4 : -y < x := by linarith
      exact And.intro h4 h1
  intro h1
  cases (le_or_gt x 0) with
  | inl h2 => rw [le_iff_lt_or_eq] at h2; cases h2 with
    | inl h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [abs_of_neg h2]; linarith
        | inr h3 => rw [abs_of_neg h2]; linarith
      | inr h3 => rw [abs_of_neg h2]; linarith
    | inr h2 => cases (le_or_gt y 0) with
      | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
        | inl h3 => rw [h2, abs_zero]; linarith
        | inr h3 => rw [h2, h3, abs_zero]; linarith
      | inr h3 => rw [h2, abs_zero]; exact h3
  | inr h2 => cases (le_or_gt y 0) with
    | inl h3 => rw [le_iff_lt_or_eq] at h3; cases h3 with
      | inl h3 => rw [abs_of_nonneg (by linarith)]; linarith
      | inr h3 => rw [abs_of_nonneg (by linarith)]; linarith
    | inr h3 => rw [abs_of_nonneg (by linarith)]; linarith

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, c, d⟩; apply add_nonneg (pow_two_nonneg a) (pow_two_nonneg b); simp [*]; apply add_nonneg (by apply add_nonneg (pow_two_nonneg a) (pow_two_nonneg b)) (by linarith)

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  cases (lt_trichotomy x 0) with
  | inl h1 =>
    right
    simp at *
    cases h with
    | inl h2 => linarith
    | inr h2 => exact h2
  | inr h1 => 
    cases h1 with 
    | inl h1 => rw [h1] at h; linarith 
    | inr h1 =>
      left
      simp at *
      cases h with
      | inl h2 => exact h2
      | inr h2 => linarith
 
example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [←sub_eq_zero, sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inl h1 => right; linarith
  | inr h1 => left; linarith

variable {R : Type} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [←sub_eq_zero, ←one_pow 2, sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inl h1 => right; rwa [←sub_eq_zero, sub_neg_eq_add]
  | inr h1 => left; rwa [←sub_eq_zero]

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  rw [←sub_eq_zero, sq_sub_sq, mul_eq_zero] at h
  cases h with
  | inl h1 => right; rwa [←sub_eq_zero, sub_neg_eq_add]
  | inr h1 => left; rwa [←sub_eq_zero]

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q := by
  apply Iff.intro
  intro h1
  cases Classical.em P with
  | inl h2 => right; exact h1 h2
  | inr h2 => left; exact h2
  intro h1
  cases h1 with
  | inl h1 => intro h2; exact absurd h2 h1
  | inr h1 => intro _; exact h1

end Logic35

namespace Logic36

def converges_to (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ _ : ℕ => a) a := by
  intro ε εpos
  use 0
  intro n _
  dsimp
  rw [sub_self, abs_zero]
  apply εpos

theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ} (cs : converges_to s a) (ct : converges_to t b) : converges_to (λ n => s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := half_pos εpos
  cases cs (ε / 2) ε2pos with
  | intro Ns hs => cases ct (ε / 2) ε2pos with
    | intro Nt ht =>
      use max Ns Nt
      intro c h1
      have h2 : abs (s c - a) < ε / 2 := hs c (le_of_max_le_left h1)
      have h3 : abs (t c - b) < ε / 2 := ht c (le_of_max_le_right h1)
      have h4 : abs (s c + t c - (a + b)) = abs ((s c - a) + (t c - b)) := by congr; linarith
      rw [h4]
      have h5 : ε / 2 + ε / 2 = ε := by norm_num
      have h6 : abs (s c - a) + abs (t c - b) < ε / 2 + ε / 2 := by linarith
      rw [h5] at h6
      exact LE.le.trans_lt (abs_add (s c - a) (t c - b)) h6

theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : converges_to s a) : converges_to (λ n => c * s n) (c * a) := by
  by_cases h : c = 0
  convert converges_to_const 0
  rw [h, zero_mul]
  rw [h, zero_mul]
  have acpos : 0 < abs c := abs_pos.mpr h
  intro ε h1
  simp
  cases cs (ε / abs c) (div_pos h1 acpos) with
  | intro b h3 =>
    use b
    intro d h4
    have h5 : abs (c * s d - c * a) = abs c * abs (s d - a) := by rw [←abs_mul, mul_sub]
    rw [h5]
    have h6 : abs c * abs (s d - a) < abs c * (ε / abs c) := StrictOrderedRing.toStrictOrderedSemiring.proof_2 (abs (s d - a)) (ε / abs c) (abs c) (h3 d h4) acpos
    have h7 : abs c * abs (s d - a) < ε := by {
      rwa [mul_div_cancel_of_imp'] at h6
      intro h7
      have h8 : c = 0 := by linarith
      contradiction
    }
    exact h7

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ} (cs : converges_to s a) : ∃ N b, ∀ n, N ≤ n → abs (s n) < b := by
  cases cs 1 zero_lt_one with
  | intro N h =>
    use N
    use abs a + 1
    intro b h1
    have h2 : abs (s b - a) < 1 := h b h1
    calc
      abs (s b) = abs (s b - a + a)     := by simp
              _ ≤ abs (s b - a) + abs a := abs_add (s b - a) a
              _ < abs a + 1             := by linarith

lemma aux {s t : ℕ → ℝ} {a : ℝ} (cs : converges_to s a) (ct : converges_to t 0) : converges_to (λ n => s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  cases ct _ pos₀ with
    | intro N₁ h₁ =>
      use max N₀ N₁
      intro n h1
      have h2 : abs (t n - 0) < ε / B := h₁ n (le_of_max_le_right h1)
      rw [sub_zero] at h2
      rw [sub_zero, abs_mul]
      calc
        abs (s n) * abs (t n) < B * (ε / B) := by exact mul_lt_mul' (le_of_lt (h₀ n (le_of_max_le_left h1))) h2 (abs_nonneg (t n)) Bpos
                            _ = ε           := by apply mul_div_cancel'; exact LT.lt.ne' Bpos

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ} (sa : converges_to s a) (sb : converges_to s b) : a = b := by
  apply Classical.by_contradiction
  intro abne
  have : abs (a - b) > 0 := by rw [gt_iff_lt, abs_pos]; exact sub_ne_zero_of_ne abne
  let ε := abs (a - b) / 2
  have εpos : ε > 0 := by change abs (a - b) / 2 > 0; exact half_pos this
  cases sa ε εpos with
    | intro Na hNa =>
      cases sb ε εpos with
        | intro Nb hNb =>
          let N := max Na Nb
          have absa : abs (s N - a) < ε := hNa N (le_max_left Na Nb)
          have absb : abs (s N - b) < ε := hNb N (le_max_right Na Nb)
          have : abs (a - b) < abs (a - b) := calc
            abs (a - b) = abs (-(s N - a) + (s N - b))     := by congr; linarith
                      _ ≤ abs (-(s N - a)) + abs (s N - b) := abs_add (-(s N - a)) (s N - b)
                      _ = abs (s N - a) + abs (s N - b)    := by rw [abs_neg]
                      _ < ε + ε                            := by linarith
                      _ = abs (a - b)                      := by simp
          exact lt_irrefl _ this

end Logic36
