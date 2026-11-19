import Mathlib
import Nodes.«variant-a30f5217».Context

open Nat

private theorem a30_two_pow_le_centralBinom (k : ℕ) : 2 ^ k ≤ Nat.centralBinom k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := Nat.succ_mul_centralBinom_succ k
    have h2 : (k + 1) * (2 * Nat.centralBinom k) ≤ (k + 1) * Nat.centralBinom (k + 1) := by
      rw [h]; nlinarith [Nat.zero_le (Nat.centralBinom k)]
    have h3 : 2 * Nat.centralBinom k ≤ Nat.centralBinom (k + 1) :=
      Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos k)
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ 2 * Nat.centralBinom k := by omega
      _ ≤ _ := h3

private theorem a30_choose_strict (k : ℕ) (hk : 1 ≤ k) :
    ∀ n m : ℕ, k ≤ n → n < m → choose n k < choose m k := by
  intro n m hn hnm
  induction m, hnm using Nat.le_induction with
  | base =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ' n j]
    have : 0 < choose n j := Nat.choose_pos (by omega)
    omega
  | succ m hm ih =>
    have : choose m k ≤ choose (m + 1) k := Nat.choose_le_succ m k
    omega

/-- Erdős 849, the elementary upper bound on multiplicity (the half-triangle form of
Singmaster's 1971 bound `N(a) = O(log a)`): the number of rows `n` in which `a` appears as
`C(n, k)` with `1 ≤ k ≤ n/2` is at most `⌊log₂ a⌋`. Each `k` gives at most one row, since
`C(·, k)` is strictly increasing, and a row with `C(n, k) = a` has `2^k ≤ C(2k, k) ≤ a`. -/
theorem Opn.erdos_849_rows_ncard_le_log : ∀ a : ℕ,
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard ≤ Nat.log 2 a := by
  intro a
  classical
  set S := {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a} with hS
  let f : ℕ → ℕ := fun n => if h : ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a then Classical.choose h else 0
  have hf : ∀ n ∈ S, 1 ≤ f n ∧ 2 * f n ≤ n ∧ choose n (f n) = a := by
    intro n hn
    have hn' : ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a := hn
    simp only [f, dif_pos hn']
    exact Classical.choose_spec hn'
  have hmaps : ∀ n ∈ S, f n ∈ (Finset.Icc 1 (Nat.log 2 a) : Set ℕ) := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hf n hn
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨h1, ?_⟩
    apply Nat.le_log_of_pow_le (by norm_num)
    calc 2 ^ f n ≤ Nat.centralBinom (f n) := a30_two_pow_le_centralBinom _
      _ = choose (2 * f n) (f n) := rfl
      _ ≤ choose n (f n) := Nat.choose_le_choose _ h2
      _ = a := h3
  have hinj : Set.InjOn f S := by
    intro n hn m hm hnm
    obtain ⟨h1, h2, h3⟩ := hf n hn
    obtain ⟨h1', h2', h3'⟩ := hf m hm
    rw [← hnm] at h2' h3'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := a30_choose_strict (f n) h1 n m (by omega) hlt; omega
    · have := a30_choose_strict (f n) h1 m n (by omega) hlt; omega
  calc S.ncard ≤ (Finset.Icc 1 (Nat.log 2 a) : Set ℕ).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj (Finset.finite_toSet _)
    _ = Nat.log 2 a := by rw [Set.ncard_coe_finset]; simp
