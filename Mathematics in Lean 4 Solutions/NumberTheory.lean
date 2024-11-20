import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

namespace NumberTheory51

example {m n : ℕ} (coprime_mn : m.coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have h1 : 2 ∣ m := by
    have h1 : 2 ∣ m ^ 2 := by
      use n ^ 2
      exact sqr_eq
    have h2 : Even (m ^ 2) := even_iff_two_dvd.2 h1;
    rw [Nat.even_pow, even_iff_two_dvd] at h2
    exact h2.left
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h1
  have h2 : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by rw [←sqr_eq, meq]; ring
  have h3 : 2 * k ^ 2 = n ^ 2 := by linarith
  have h4 : 2 ∣ n := by
    have h4 : 2 ∣ n ^ 2 := by
      use k ^ 2
      exact Eq.symm h3
    have h5 : Even (n ^ 2) := even_iff_two_dvd.2 h4
    rw [Nat.even_pow, even_iff_two_dvd] at h5
    exact h5.left
  have h5 : 2 ∣ m.gcd n := Nat.dvd_gcd h1 h4
  have h6 : 2 ∣ 1 := by rwa [coprime_mn] at h5
  norm_num at h6

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro h1
  have h2 : p ∣ m := by
    have h2 : p ∣ m ^ 2 := by use n ^ 2; exact h1
    rwa [pow_two, Nat.Prime.dvd_mul prime_p, or_self] at h2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp h2
  have h3 : k ^ 2 * p ^ 2 / p = k ^ 2 * p := by rw [pow_two, pow_two, Nat.mul_div_assoc _ (Nat.dvd_mul_right p p), Nat.mul_div_cancel p (Nat.Prime.pos prime_p)]; 
  have h4 : p * n ^ 2 / p = n ^ 2 := by rw [Nat.mul_div_cancel_left (n ^ 2) (Nat.Prime.pos prime_p)]
  rw [meq, mul_pow] at h1
  have h5 : k ^ 2 * p ^ 2 / p = p * n ^ 2 / p := by congr
  rw [h3, h4] at h5
  have h6 : p ∣ n := by
    have h6 : p ∣ n ^ 2 := by
      use k ^ 2
      rw [mul_comm] at h5
      exact Eq.symm h5
    rwa [pow_two, Nat.Prime.dvd_mul prime_p, or_self] at h6
  have h7 : p ∣ m.gcd n := Nat.dvd_gcd h2 h6
  have h8 : p ∣ 1 := by rwa [coprime_mn] at h7
  have h9 : 2 ≤ p := Nat.Prime.two_le prime_p
  have h10 : p ≤ 1 := Nat.le_of_dvd (by linarith) h8
  linarith

/- Don't seem possible until Nat.factorization is ported. 

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := sorry

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k {p : ℕ} (prime_p : p.Prime) : k ∣ r.factorization p := sorry -/

end NumberTheory51

namespace NumberTheory52

def fac : ℕ → ℕ
| 0       => 1
| (n + 1) => (n + 1) * fac n

theorem pow_two_le_fact (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  cases n with
  | zero => simp
  | succ n => 
    simp [fac];
    rw [add_mul, one_mul]
    induction n with
    | zero => simp
    | succ n ih => 
      rw [Nat.succ_eq_add_one, pow_add, pow_one, Nat.mul_two];  
      apply Nat.add_le_add
      rw [fac, add_mul, add_mul, mul_add, mul_add, one_mul, one_mul, one_mul]
      calc
        2 ^ n ≤ n * fac n + fac n                                 := by exact ih
            _ ≤ n * (n * fac n) + n * fac n + (n * fac n + fac n) := self_le_add_left (n * fac n + fac n) (n * (n * fac n) +  n * fac n) 
      rwa [fac, add_mul, one_mul] 
      
open BigOperators

theorem sum_sqr (n : ℕ) : ∑ i in Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm
  apply Nat.div_eq_of_eq_mul_right (by norm_num)
  induction n with
  | zero => simp
  | succ n ih => 
    rw [Finset.sum_range_succ, mul_add 6, ←ih, Nat.succ_eq_add_one]
    ring

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x, zero     => x
| x, (succ y) => succ (add x y)

def mul : my_nat → my_nat → my_nat
| _, zero     => zero
| x, (succ y) => add (mul x y) x

theorem zero_add (n : my_nat) : add zero n = n := by
  induction n with
  | zero => rfl
  | succ a ih => rw [add, ih]

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) := by
  induction n with
  | zero => rfl
  | succ a ih => rw [add, ih]; rfl

theorem add_comm (m n : my_nat) : add m n = add n m := by
  induction n with
  | zero => rw [zero_add]; rfl
  | succ a ih => rw [add, succ_add, ih]

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) := by
  induction k with
  | zero => rw [add_comm, zero_add, add_comm n zero, zero_add]; 
  | succ a ih => rw [add_comm n (succ a), succ_add, add_comm, succ_add, add_comm, ih, add_comm, ←succ_add, add_comm, add_comm n a]

theorem mul_add (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction k with
  | zero => rw [add_comm, zero_add, mul, add_comm, zero_add]
  | succ a ih => rw [add, mul, ih, add_assoc, mul]; 

theorem zero_mul (n : my_nat) : mul zero n = zero := by
  induction n with
  | zero => rfl
  | succ a ih => rwa [←ih, mul, ih, add_comm, zero_add];

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n := by
  induction n with
  | zero => rfl
  | succ a ih => rw [add, mul, add, ih, add_assoc, mul, add_assoc, add_comm a m]

theorem mul_comm (m n : my_nat) : mul m n = mul n m := by
  induction n with
  | zero => rw [zero_mul]; rfl
  | succ a ih => rw [mul, ih, succ_mul]

end my_nat

end NumberTheory52

namespace NumberTheory53

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h : m ≠ 1) : 2 ≤ m := by
  cases m with
  | zero => contradiction
  | succ n => cases n with
    | zero => contradiction
    | succ n => 
      repeat apply Nat.succ_le_succ
      apply zero_le

theorem exists_prime_factor {n : ℕ} (h : 2 ≤ n) : ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  use n
  exact ⟨np, dvd_rfl⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np h with ⟨m, mltn, mdvdn, mne1⟩
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have mgt2 : 2 ≤ m := two_le this mne1
    by_cases mp : m.Prime
    use m
    exact ⟨mp, mdvdn⟩
    rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn⟩

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    induction n with
    | zero => simp
    | succ n ih => 
      rw [Nat.factorial];
      calc
        2 ≤ Nat.factorial (n + 1) + 1 := ih
        _ ≤ Nat.succ (n + 1) * Nat.factorial (n + 1) + 1 := add_le_add_right (le_mul_of_one_le_left' (by apply Nat.succ_pos (n + 1))) 1
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  use p
  have h1 : p > n := by
    by_contra ple
    have : p ∣ Nat.factorial (n + 1) := by
      rw [Nat.Prime.dvd_factorial pp]
      linarith
    have : p ∣ 1 := by
      convert Nat.dvd_sub' pdvd this
      rw [add_comm, Nat.add_sub_assoc, Nat.sub_self, add_zero]
      rfl
    exact absurd this (Nat.Prime.not_dvd_one pp)
  exact ⟨h1, pp⟩ 

variable {α : Type} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ (s ∩ t) := by
  ext
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext
  simp
  tauto

open Finset
open BigOperators

theorem eq_of_dvd_of_prime {p q : ℕ} (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) : p = q := by 
  cases (Nat.Prime.eq_one_or_self_of_dvd prime_q p h) with
  | inl h1 => rw [h1] at prime_p; contradiction
  | inr h1 => assumption

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) : (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction s using Finset.induction_on with
  | empty => simp at h₁; linarith [prime_p.two_le]
  | insert ans ih => 
    simp [prod_insert ans, prime_p.dvd_mul] at h₀ h₁
    rw [mem_insert]
    cases h₁ with
    | inl h1 =>
      left
      symm
      rwa [←Nat.Prime.dvd_iff_eq (h₀.left) (Nat.Prime.ne_one prime_p)]
    | inr h1 =>
      right
      exact ih h₀.right h1

theorem primes_infinite' : ∀ (s : Finset Nat), ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := Nat.le_succ_of_pred_le (prod_pos (λ n => λ h1 => Nat.Prime.pos (Iff.mp mem_s' h1)))
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ (∏ i in s', i) := dvd_prod_of_mem (fun i => i) (Iff.mpr mem_s' pp) 
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    rw [add_comm, Nat.add_sub_assoc, Nat.sub_self, add_zero]
    rfl
  exact absurd this (Nat.Prime.not_dvd_one pp)

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw  [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4
  simp
  simp
  simp
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4
  simp
  norm_num
  intro h1
  contradiction
  simp
  simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le
  intro neq
  rw [neq] at h
  norm_num at h
  intro neq
  rw [neq] at h
  norm_num at h

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] : (∃ n, ∀ k, Q k → k ≤ n) → (∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s) := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : (n / m) ∣ n ∧ n / m < n := ⟨Nat.div_dvd_of_dvd h₀, Nat.div_lt_self (lt_of_le_of_lt (by linarith) h₂) (by linarith)⟩

theorem exists_prime_factor_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  use n
  exact ⟨np, dvd_rfl, h⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
    have meg2 : 2 ≤ m := by
      apply two_le _ mne1
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
    have : m % 4 = 3 ∨ (n / m) % 4 = 3 := by
      apply mod_4_eq_3_or_mod_4_eq_3
      rw [neq, h]
    cases this with
    | inl h1 =>
      by_cases h2 : m.Prime
      use m
      exact ⟨h2, mdvdn, h1⟩
      rcases ih m mltn h1 h2 with ⟨a, h3⟩
      use a
      exact ⟨h3.left, Nat.dvd_trans h3.right.left mdvdn, h3.right.right⟩
    | inr h1 =>
      by_cases h2 : (n / m).Prime  
      exact ⟨n / m, h2, (aux mdvdn meg2 mltn).left, h1⟩ 
      rcases ih (n / m) (aux mdvdn meg2 mltn).right h1 h2 with ⟨a, h3⟩
      use a
      exact ⟨h3.left, Nat.dvd_trans h3.right.left (Nat.div_dvd_of_dvd mdvdn), h3.right.right⟩

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  cases h with
  | intro n hn =>
    have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
      apply ex_finset_of_bounded
      use n
      contrapose! hn
      rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
      exact ⟨p, pltn, pp, p4⟩
    cases this with
    | intro s hs =>
      have h₁ : (4 * (∏ i in erase s 3, i) + 3) % 4 = 3 := by rw [add_comm, Nat.add_mul_mod_self_left]; rfl
      rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
      have ps : p ∈ s := (hs p).mp ⟨pp, p4eq⟩
      have pne3 : p ≠ 3 := by
        intro peq
        rw [peq, ←Nat.dvd_add_iff_left (dvd_refl 3), Nat.Prime.dvd_mul] at pdvd
        norm_num at pdvd
        have : 3 ∈ s.erase 3 := by
          apply mem_of_dvd_prod_primes Nat.prime_three _ (by norm_num at pdvd; exact pdvd)
          intro a h1
          exact ((hs a).mpr (Finset.mem_erase.mp h1).right).left
        simp at this
        norm_num
      have : p ∣ 4 * (∏ i in erase s 3, i) := (Nat.Prime.dvd_mul pp).mpr (Or.inr (dvd_prod_of_mem (λ i => i) (by simp; exact ⟨pne3, ps⟩)))
      have : p ∣ 3 := by
        convert Nat.dvd_sub' pdvd this
        rw [add_comm, Nat.add_sub_assoc, Nat.sub_self, add_zero]
        rfl
      have : p = 3 := Eq.symm ((Nat.Prime.dvd_iff_eq Nat.prime_three (show p ≠ 1 by intro h1; rw [h1] at p4eq; contradiction)).mp this)
      contradiction

end NumberTheory53
