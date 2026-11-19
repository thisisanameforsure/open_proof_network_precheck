import Mathlib
import Nodes.«variant-72919549».Context

open Nat

private theorem v72_choose_mono_k (n j : ℕ) :
    ∀ k : ℕ, j ≤ k → 2 * k ≤ n → choose n j ≤ choose n k := by
  intro k hjk hk
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    have h1 := ih (by omega)
    have h2 : choose n k ≤ choose n (k + 1) := Nat.choose_le_succ_of_lt_half_left (by omega)
    omega

private theorem v72_cassini (n : ℕ) :
    (fib (n + 1) : ℤ) ^ 2 - (fib n : ℤ) * (fib (n + 2) : ℤ) = (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fib (n + 2) : ℤ) = fib n + fib (n + 1) := by
      rw [Nat.fib_add_two]; push_cast; ring
    have h2 : (fib (n + 1 + 2) : ℤ) = fib (n + 1) + fib (n + 2) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [show n + 1 + 1 = n + 2 by ring, h2, pow_succ]
    rw [h1] at ih ⊢
    linear_combination (-1 : ℤ) * ih

private theorem v72_fib_ge (j : ℕ) : j + 5 ≤ fib (2 * j + 5) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h1 : fib (2 * (j + 1) + 5) = fib (2 * j + 5) + fib (2 * j + 6) := by
      rw [show 2 * (j + 1) + 5 = (2 * j + 5) + 2 by ring, Nat.fib_add_two]
    have h2 : 0 < fib (2 * j + 6) := Nat.fib_pos.mpr (by omega)
    omega

/-- The Singmaster identity `C(m+1, k) = C(m, k+1)` from `(m+1)(k+1) = (m-k)(m+1-k)`. -/
private theorem v72_choose_eq (m k : ℕ) (hk : k + 1 ≤ m)
    (h : (m + 1) * (k + 1) = (m - k) * (m + 1 - k)) : choose (m + 1) k = choose m (k + 1) := by
  have e1 : choose m k * (m + 1) = choose (m + 1) k * (m + 1 - k) := Nat.choose_mul_succ_eq m k
  have e2 : choose m (k + 1) * (k + 1) = choose m k * (m - k) := Nat.choose_succ_right_eq m k
  have hpos : 0 < (m + 1 - k) * (k + 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc choose (m + 1) k * ((m + 1 - k) * (k + 1))
      = choose m k * ((m + 1) * (k + 1)) := by rw [← mul_assoc, ← e1]; ring
    _ = choose m k * ((m - k) * (m + 1 - k)) := by rw [h]
    _ = choose m (k + 1) * ((m + 1 - k) * (k + 1)) := by rw [← mul_assoc, ← e2]; ring

/-- Infinitely many integers $a$ are $\binom{n}{k}$ with $1 \le k \le n/2$ in at least three rows
$n$: for every $N$ there is such an $a \ge N$. A consequence of the affirmative answer to
Erdős 849 (it gives one $a$ for each $t \ge 3$, all distinct). The proof uses Singmaster's
Fibonacci family: for $i \ge 1$, $n = F_{2i+2}F_{2i+3}$ and $k = F_{2i}F_{2i+3}$ give
$\binom{n}{k} = \binom{n-1}{k+1}$, and with $\binom{a}{1}$ that is three rows. -/
theorem Opn.erdos_849_three_rows_infinitely_often :
    ∀ N : ℕ, ∃ a ≥ N, 3 ≤ {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard := by
  intro N
  set j := N
  set A := fib (2 * j + 2) with hA
  set B := fib (2 * j + 3) with hB
  set C := fib (2 * j + 4) with hC
  set D := fib (2 * j + 5) with hD
  have hCab : C = A + B := by
    rw [hC, hA, hB, show 2 * j + 4 = (2 * j + 2) + 2 by ring, Nat.fib_add_two]
  have hDbc : D = B + C := by
    rw [hD, hB, hC, show 2 * j + 5 = (2 * j + 3) + 2 by ring, Nat.fib_add_two]
  have hcas : (B : ℤ) ^ 2 - (A : ℤ) * (C : ℤ) = 1 := by
    have := v72_cassini (2 * j + 2)
    rw [show 2 * j + 2 + 1 = 2 * j + 3 by ring, show 2 * j + 2 + 2 = 2 * j + 4 by ring] at this
    rw [this]; exact Even.neg_one_pow ⟨j + 1, by ring⟩
  have hBA : A + 1 ≤ B := by
    have h1 : B = fib (2 * j + 1) + A := by
      rw [hB, hA, show 2 * j + 3 = (2 * j + 1) + 2 by ring, Nat.fib_add_two]
    have h2 : 0 < fib (2 * j + 1) := Nat.fib_pos.mpr (by omega)
    omega
  have hA1 : 1 ≤ A := Nat.fib_pos.mpr (by omega)
  have hDN : j + 5 ≤ D := v72_fib_ge j
  -- n = C * D = m + 1, k = A * D
  set k := A * D with hk
  set m := C * D - 1 with hm
  have hk2 : 2 ≤ k := by
    have : 1 * 5 ≤ A * D := Nat.mul_le_mul hA1 (by omega)
    omega
  have hCD : C * D = k + B * D := by rw [hCab, hk]; ring
  have hBD : B * D ≥ (A + 1) * D := Nat.mul_le_mul_right _ hBA
  have hmk : 2 * (k + 1) ≤ m := by
    have : (A + 1) * D = A * D + D := by ring
    omega
  have hn : m + 1 = C * D := by
    have : 1 ≤ C * D := by omega
    omega
  have hid : (m + 1) * (k + 1) = (m - k) * (m + 1 - k) := by
    have e1 : m - k = B * D - 1 := by omega
    have e2 : m + 1 - k = B * D := by omega
    rw [e1, e2, hn]
    have hBD1 : 1 ≤ B * D := by omega
    zify [hBD1]
    have hC' : (C : ℤ) = A + B := by exact_mod_cast hCab
    have hD' : (D : ℤ) = B + C := by exact_mod_cast hDbc
    push_cast [hk]
    linear_combination (-(D : ℤ) ^ 2) * hcas - (D : ℤ) * hD'
  have hsing : choose (m + 1) k = choose m (k + 1) := v72_choose_eq m k (by omega) hid
  set a := choose (m + 1) k with ha
  have hna : m + 1 < a := by
    have h2 : choose (m + 1) 2 ≤ a := v72_choose_mono_k (m + 1) 2 k hk2 (by omega)
    have h3 : choose (m + 1) 2 = (m + 1) * (m + 1 - 1) / 2 := Nat.choose_two_right (m + 1)
    have h4 : (m + 1) * (m + 1 - 1) ≥ (m + 1) * 3 := Nat.mul_le_mul_left _ (by omega)
    omega
  have hDCD : D ≤ C * D := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨a, by omega, ?_⟩
  set S := {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a} with hS
  have hfin : S.Finite := by
    apply (Set.finite_Iic a).subset
    rintro n ⟨k', hk1, hk2', hk3⟩
    have := v72_choose_mono_k n 1 k' hk1 hk2'
    simp only [Nat.choose_one_right] at this
    simp only [Set.mem_Iic]; omega
  have hsub : ({a, m + 1, m} : Set ℕ) ⊆ S := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, le_rfl, by omega, by simp⟩
    · exact ⟨k, by omega, by omega, rfl⟩
    · exact ⟨k + 1, by omega, hmk, hsing.symm⟩
  have h3 : ({a, m + 1, m} : Set ℕ).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨a, m + 1, m, by omega, by omega, by omega, rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub hfin
