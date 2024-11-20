import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.WLOG

namespace SetsandFunctions41

variable {α : Type}
variable (s t u : Set α)

open Set

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  intro a h1
  cases h1 with
  | inl h1 => exact mem_inter h1.left (mem_union_left u h1.right)
  | inr h1 => exact mem_inter h1.left (mem_union_right t h1.right)

example : s \ (t ∪ u) ⊆ s \ (t \ u) := by
  intro a h1
  cases h1 with
  | intro left right => exact And.intro left (by simp; intro h1; exact absurd (mem_union_left u h1) right)

example : s ∩ t = t ∩ s := Subset.antisymm (by intro a h1; cases h1 with | intro left right => exact mem_inter right left) (by intro a h1; cases h1 with | intro left right => exact mem_inter right left)

example : s ∩ (s ∪ t) = s := by
  ext
  simp
  intro h1
  exact Or.inl h1

example : s ∪ (s ∩ t) = s := by
  ext
  simp
  intro h1 _
  exact h1

example : (s \ t) ∪ t = s ∪ t := by
  ext
  simp

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := by
  ext 
  simp
  apply Iff.intro
  intro h1
  cases h1 with
  | inl h1 => exact And.intro (Or.inl h1.left) (λ _ => h1.right)
  | inr h1 => exact And.intro (Or.inr h1.left) (λ h2 => absurd h2 h1.right)
  intro h1
  cases h1.left with
  | inl h2 => exact Or.inl (And.intro h2 (h1.right h2))
  | inr h2 => exact Or.inr (And.intro h2 (λ h3 => absurd h2 (h1.right h3)))

example : {n | Nat.Prime n} ∩ {n | n > 2} ⊆ {n | ¬ Even n} := by 
  intro n h1 h2
  simp at *
  have h3 : Odd n := Nat.Prime.odd_of_ne_two h1.left (by linarith)
  exact absurd h2 (by rwa [←Nat.odd_iff_not_even])

variable (s t : Set ℕ)

example {ssubt : s ⊆ t} (h₀ : ∀ x ∈ t, ¬ Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬ Even x ∧ Prime x := by
  intro x h1
  exact And.intro (h₀ x (ssubt h1)) (h₁ x (ssubt h1))

example {ssubt : s ⊆ t} (h : ∃ x ∈ s, ¬ Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  cases h with
  | intro w h =>
    use w
    exact And.intro (ssubt h.left) h.right.right

variable {α I : Type}
variable (A B : I → Set α)
variable (s : Set α)

open Classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) := by
  ext x
  simp
  apply Iff.intro
  intro h1 i
  cases h1 with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl (h i)
  intro a
  by_cases xs : x ∈ s
  exact Or.inl xs
  exact Or.inr (λ i => Or.resolve_right (a i) xs)
  
def primes : Set ℕ := {x | Nat.Prime x}

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rw [primes]
  simp
  convert Nat.exists_infinite_primes
  apply Iff.intro
  intro _ n
  apply Nat.exists_infinite_primes
  intro a
  cases (a x) with
  | intro w h =>
    use w
    exact And.symm h

end SetsandFunctions41

namespace SetsandFunctions42

variable {α β : Type}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f '' s ⊆ v ↔ s ⊆ f⁻¹' v := by
  apply Iff.intro
  intro h1 a h2
  rw [mem_preimage]
  rw [image_subset_iff] at h1
  exact h1 h2
  intro h1 a
  simp
  intro b h2 h3
  have h4 : b ∈ f ⁻¹' v := h1 h2
  rw [mem_preimage] at h4
  rwa [h3] at h4

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro a
  rw [mem_preimage, mem_image]
  simp
  intro b h1 h2
  rwa [←(h h2)]

example : f '' (f⁻¹' u) ⊆ u := by
  intro a
  rw [mem_image]
  simp
  intro b h1 h2
  rwa [h2] at h1

example (h : Surjective f) : u ⊆ f '' (f⁻¹' u) := by
  intro a h1
  cases (h a) with
  | intro x h2 =>
    apply Exists.intro
    exact And.intro (by rwa [←h2] at h1) h2

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro a h1
  cases h1 with
  | intro w h1 => 
    use w
    exact And.intro (h h1.left) (h1.right)

example (h : u ⊆ v) : f⁻¹' u ⊆ f⁻¹' v := by
  intro a
  rw [mem_preimage, mem_preimage]
  intro h1
  exact h h1

example : f⁻¹' (u ∪ v) = f⁻¹' u ∪ f⁻¹' v := by
  ext
  apply Iff.intro
  rw [mem_union, mem_preimage, mem_preimage, mem_preimage, mem_union]
  intro a
  exact a
  rw [mem_union, mem_preimage, mem_preimage, mem_preimage, mem_union]
  intro a
  exact a

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro a
  rw [mem_image, mem_inter_iff, mem_image, mem_image, forall_exists_index]
  simp
  intro b h1 h2 h3
  apply And.intro
  use b
  exact And.intro h1 h3
  use b
  exact And.intro h2 h3

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro a
  rw [mem_inter_iff, mem_image, mem_image, mem_image, and_imp, forall_exists_index, forall_exists_index]
  simp
  intro b h1 h2 c h3 h4
  have h5 : f b = f c := by rwa [←h4] at h2
  rw [(h h5)] at h1
  use c
  exact And.intro (And.intro h1 h3) h4

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro a
  simp
  intro b h1 h2 h3
  use b
  have h4 : b ∈ t → ¬ f b = a := h3 b
  have h5 : ¬ b ∈ t := by intro h5; exact absurd h2 (h4 h5)
  exact And.intro (And.intro h1 h5) h2

example : f⁻¹' u \ f⁻¹' v ⊆ f⁻¹' (u \ v) := by
  intro a
  rw [mem_diff, mem_preimage, mem_preimage, mem_preimage, mem_diff]
  intro h1
  exact h1

example : f '' s ∩ v = f '' (s ∩ f⁻¹' v) := by
  ext a
  apply Iff.intro
  simp
  intro b h1 h2 h3
  use b
  rw [←h2] at h3
  exact And.intro (And.intro h1 h3) h2
  simp
  intro b h1 h2 h3
  have h4 : ∃ x, x ∈ s ∧ f x = a := by use b; exact And.intro h1 h3
  rw [h3] at h2
  exact And.intro h4 h2

example : f '' (s ∩ f⁻¹' u) ⊆ f '' s ∪ u := by
  intro a
  simp
  intro b _ h2 h3
  right
  rwa [h3] at h2

example : s ∩ f⁻¹' u ⊆ f⁻¹' (f '' s ∩ u) := by
  intro a
  simp
  intro h1 h2
  have h3 : ∃ x, x ∈ s ∧ f x = f a := by use a; exact And.intro h1 rfl
  exact And.intro h3 h2

example : s ∪ f⁻¹' u ⊆ f⁻¹' (f '' s ∪ u) := by
  intro a
  simp
  intro h1
  cases h1 with
  | inl h1 =>
    left
    use a
    exact And.intro h1 rfl
  | inr h1 =>
    right
    exact h1

/- Not possible as Real.sqrt has not yet been implemented.

example : InjOn Real.sqrt {x | x ≥ 0}

example : InjOn (λ x => x ^ 2) {x : ℝ | x ≥ 0}

example : Real.sqrt '' {x | x ≥ 0} = {y | y ≥ 0}

example : range (λ x => x ^ 2) = {y : ℝ | y ≥ 0} -/

noncomputable section theory

variable {α β : Type} [Inhabited α]
variable (P : α → Prop) (h : ∃ x, P x)
variable (f : α → β)

open Classical

def inverse (f : α → β) : β → α := λ y : β => if h : ∃ x, f x = y then Classical.choose h else default

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  apply Iff.intro
  intro h1 a
  rw [inverse]
  have h2 : ∃ x, f x = f a := by use a
  rw [dif_pos h2]
  exact h1 (choose_spec h2)
  intro h1 a b h2
  rw [LeftInverse] at h1
  have h3 : inverse f (f a) = a := h1 a
  rw [h2, eq_comm] at h3
  exact Eq.trans h3 (h1 b)

example : Surjective f ↔ RightInverse (inverse f) f := by
  apply Iff.intro
  intro h1 a
  have h2 : ∃ x, f x = a := h1 a
  rw [inverse, dif_pos h2]
  exact choose_spec h2
  intro h1 b
  rw [Function.RightInverse, LeftInverse] at h1
  have h2 : f (inverse f b) = b := h1 b
  constructor
  apply h2

end theory

theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
  intro f surjf
  let S := {i | i ∉ f i}
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by rwa [h] at h₁
  contradiction

end SetsandFunctions42

namespace SetsandFunctions43

noncomputable section theory

open Classical

variable {α β : Type} [Nonempty β]
variable (f : α → β) (g : β → α)

def sb_aux : ℕ → Set α
  | 0       => Set.univ \ (g '' Set.univ)
  | (n + 1) => g '' (f '' sb_aux n)

def sb_set := ⋃ n, sb_aux f g n

def sb_fun (x : α) : β := if x ∈ sb_set f g then f x else Function.invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sb_set f g) : g (Function.invFun g x) = x := by
  have : x ∈ g '' Set.univ := by
    contrapose! hx
    rw [sb_set, Set.mem_unionᵢ]
    use 0
    rw [sb_aux, Set.mem_diff]
    exact And.intro (by apply Set.mem_univ) hx
  have : ∃ y, g y = x := by
    rw [Set.mem_image] at this
    simp only [Set.mem_univ, true_and] at this
    exact this
  rw [Function.invFun, dif_pos this]
  exact choose_spec this

theorem sb_injective (hf : Function.Injective f) (_ : Function.Injective g) : Function.Injective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intro x₁ x₂ hxeq
  simp only [h_def, sb_fun, ←A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  cases xA with
  | inl h1 =>
    rw [if_pos h1] at hxeq
    by_cases x₂ ∈ A
    rw [if_pos h] at hxeq
    exact hf hxeq
    rw [if_neg h] at hxeq
    have h2 : x₂ ∈ A := by
      apply not_imp_self.mp
      intro h2
      rw [A_def, sb_set, Set.mem_unionᵢ] at h1
      have h3 : x₂ = g (f x₁) := by rw [hxeq, sb_right_inv f g h2]
      rcases h1 with ⟨n, hn⟩
      rw [A_def, sb_set, Set.mem_unionᵢ]
      use n + 1
      simp [sb_aux]
      use x₁
      exact And.intro hn (Eq.symm h3)
    contradiction
  | inr h1 =>
    rw [if_pos h1] at hxeq
    by_cases x₁ ∈ A
    rw [if_pos h] at hxeq
    exact hf hxeq
    have h2 : x₁ ∈ A := by
      apply not_imp_self.mp
      intro h2
      rw [A_def, sb_set, Set.mem_unionᵢ] at h1
      rw [if_neg h2] at hxeq
      have : x₁ = g (f x₂) := by rw [←hxeq, sb_right_inv f g h2]
      rcases h1 with ⟨n, hn⟩
      rw [A_def, sb_set, Set.mem_unionᵢ]
      use n + 1
      simp [sb_aux]
      use x₂
      exact And.intro hn (Eq.symm this)
    contradiction
  push_neg at xA
  rw [←A_def] at xA
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [←sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]

theorem sb_surjective (_ : Function.Injective f) (hg : Function.Injective g) : Function.Surjective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  rw [A_def, sb_set, Set.mem_unionᵢ] at gyA
  rcases gyA with ⟨n, hn⟩
  cases n with
  | zero => simp [sb_aux] at hn
  | succ n => 
    simp [sb_aux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by rw [A_def, sb_set, Set.mem_unionᵢ]; exact ⟨n, xmem⟩
    simp only [h_def, sb_fun, if_pos this]
    exact hg hx
  use g y
  simp [sb_fun, h_def, if_neg gyA]
  rw [Function.invFun]
  have h1 : ∃ x, g x = g y := by use y
  rw [dif_pos h1]
  exact hg (choose_spec h1)

end theory

end SetsandFunctions43
