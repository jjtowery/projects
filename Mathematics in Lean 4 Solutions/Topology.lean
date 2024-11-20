import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.LibrarySearch

namespace Topology71

def principal {α : Type} (s : Set α) : Filter α := {
  sets := {t | s ⊆ t}
  univ_sets := λ _ _ => trivial
  sets_of_superset := λ h1 h2 _ h3 => h2 (h1 h3)
  inter_sets := λ h1 h2 _ h3 => Set.mem_inter (h1 h3) (h2 h3)
}

example : Filter ℕ := {
  sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s}
  univ_sets := by 
    rw [Set.mem_setOf_eq]
    use 0
    intro a _
    apply Set.mem_univ
  sets_of_superset := by 
    intro a b h1 h2
    rw [Set.mem_setOf_eq] at h1
    cases h1 with
    | intro c h1 =>
      rw [Set.mem_setOf_eq]
      use c
      intro d h3
      exact h2 (h1 d h3)
  inter_sets := by 
    intro a b h1 h2
    rw [Set.mem_setOf_eq] at h1 h2
    cases h1 with
    | intro c h1 => cases h2 with
      | intro d h2 =>
        rw [Set.mem_setOf_eq]
        simp
        use max c d
        intro e h3
        exact ⟨h1 e (le_of_max_le_left h3), h2 e (le_of_max_le_right h3)⟩ 
}

def tendsto₁ {X Y : Type} (f : X → Y) (F : Filter X) (G : Filter Y) := ∀ V ∈ G, f ⁻¹' V ∈ F

example {X Y Z : Type} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z} (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H := λ a h1 => hf (g ⁻¹' a) (hg a h1)

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) : Filter.Tendsto f Filter.atTop ( (x₀, y₀)) ↔ 

end Topology71
