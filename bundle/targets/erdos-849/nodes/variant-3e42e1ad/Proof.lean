import Mathlib
import Nodes.«variant-3e42e1ad».Context

open Nat

private theorem v3e_choose_strict (k : ℕ) (hk : 1 ≤ k) :
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

private theorem v3e_choose_mono_k (n j : ℕ) :
    ∀ k : ℕ, j ≤ k → 2 * k ≤ n → choose n j ≤ choose n k := by
  intro k hjk hk
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    have h1 := ih (by omega)
    have h2 : choose n k ≤ choose n (k + 1) := Nat.choose_le_succ_of_lt_half_left (by omega)
    omega

private theorem v3e_prime_le (p n k : ℕ) (hp : p.Prime) (hk : k ≤ n) (h : p ∣ choose n k) :
    p ≤ n := by
  have h1 : choose n k * k ! * (n - k)! = n ! := Nat.choose_mul_factorial_mul_factorial hk
  have h2 : p ∣ n ! := by
    rw [← h1]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  exact (Nat.Prime.dvd_factorial hp).mp h2

private theorem v3e_one_row (p : ℕ) (hp : p.Prime) (hp4 : 4 ≤ p) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = p} = {p} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk1, hk2, hk3⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : k = 1 := by omega
      subst this; simpa using hk3
    · exfalso
      have hpn : p ≤ n := v3e_prime_le p n k hp (by omega) (by rw [hk3])
      have h2 : choose n 2 ≤ choose n k := v3e_choose_mono_k n 2 k hk hk2
      have h3 : choose n 2 = n * (n - 1) / 2 := Nat.choose_two_right n
      have h4 : n * (n - 1) / 2 > n := by
        have : n * (n - 1) ≥ n * 3 := Nat.mul_le_mul_left _ (by omega)
        omega
      omega
  · rintro rfl
    exact ⟨1, le_rfl, by omega, by simp⟩

private theorem v3e_two_rows (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = choose p 2} = {choose p 2, p} := by
  have hb : choose p 2 = p * (p - 1) / 2 := Nat.choose_two_right p
  have hev : 2 ∣ p * (p - 1) := by
    rcases Nat.even_or_odd p with he | ho
    · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp he) _
    · apply Dvd.dvd.mul_left
      obtain ⟨r, hr⟩ := ho
      exact ⟨r, by omega⟩
  have hb2 : choose p 2 * 2 = p * (p - 1) := by
    rw [hb]; exact Nat.div_mul_cancel hev
  have hpb : p ∣ choose p 2 := by
    have h1 : p ∣ choose p 2 * 2 := by rw [hb2]; exact Dvd.intro _ rfl
    rcases (Nat.Prime.dvd_mul hp).mp h1 with h | h
    · exact h
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h
      omega
  have hbig : p < choose p 2 := by
    have : p * (p - 1) ≥ p * 6 := Nat.mul_le_mul_left _ (by omega)
    omega
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk1, hk2, hk3⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have : k = 1 := by omega
      subst this; left; simpa using hk3
    · right
      have hpn : p ≤ n := v3e_prime_le p n k hp (by omega) (by rw [hk3]; exact hpb)
      by_contra hne
      have hlt : p < n := lt_of_le_of_ne hpn (Ne.symm hne)
      have h2 : choose n 2 ≤ choose n k := v3e_choose_mono_k n 2 k hk hk2
      have h3 : choose p 2 < choose n 2 := v3e_choose_strict 2 (by norm_num) p n (by omega) hlt
      omega
  · rintro (h | h)
    · rw [h]; exact ⟨1, le_rfl, by omega, by simp⟩
    · rw [h]; exact ⟨2, by norm_num, by omega, rfl⟩

/-- The cases $t = 1$ and $t = 2$ of Erdős 849 each hold for infinitely many $a$: for every $N$
there are $a, b \ge N$ with $a$ in exactly one row and $b$ in exactly two rows (rows $n$ with
$\binom{n}{k} = a$, $1 \le k \le n/2$). The proof takes a prime $a = p$ (only $\binom{p}{1}$) and
$b = \binom{p}{2}$ for a prime $p \ge 7$ (only $\binom{p}{2}$ and $\binom{b}{1}$), since a prime
dividing $\binom{n}{k}$ is at most $n$. -/
theorem Opn.erdos_849_one_and_two_rows_infinitely_often :
    ∀ N : ℕ, (∃ a ≥ N, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 1) ∧
      (∃ a ≥ N, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ choose n k = a}.ncard = 2) := by
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 7)
  refine ⟨⟨p, by omega, ?_⟩, ⟨choose p 2, ?_, ?_⟩⟩
  · rw [v3e_one_row p hp (by omega)]; exact Set.ncard_singleton p
  · have hb : choose p 2 = p * (p - 1) / 2 := Nat.choose_two_right p
    have : p * (p - 1) ≥ p * 6 := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [v3e_two_rows p hp (by omega)]
    apply Set.ncard_pair
    have hb : choose p 2 = p * (p - 1) / 2 := Nat.choose_two_right p
    have : p * (p - 1) ≥ p * 6 := Nat.mul_le_mul_left _ (by omega)
    omega
