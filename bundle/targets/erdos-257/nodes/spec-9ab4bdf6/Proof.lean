import Mathlib
import Nodes.«spec-9ab4bdf6».Context

private lemma lb_small (m N D : ℕ) (hm : 1092 ≤ m) (h1 : m < N) (h2 : N ≤ m + 12) (hD : D ≤ 12) :
    ((Finset.Icc 2 D).filter (· ∣ N)).card ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.ncard := by
  have hfin : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.Finite :=
    (Set.finite_Iio m).subset (fun a ha => ha.2.1)
  calc ((Finset.Icc 2 D).filter (· ∣ N)).card
      = (((Finset.Icc 2 D).filter (· ∣ N)).image (fun d => N / d)).card := by
        rw [Finset.card_image_of_injOn]
        intro d1 hd1 d2 hd2 heq
        simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hd1 hd2
        have hN : N ≠ 0 := by omega
        rw [← Nat.div_div_self hd1.2 hN, ← Nat.div_div_self hd2.2 hN]
        simp only at heq
        rw [heq]
    _ = ((((Finset.Icc 2 D).filter (· ∣ N)).image (fun d => N / d) : Finset ℕ) : Set ℕ).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ _ := by
        apply Set.ncard_le_ncard _ hfin
        intro a ha
        simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_Icc, Set.mem_image,
          Set.mem_ofPred_eq] at ha
        obtain ⟨d, ⟨⟨hd2, hdD⟩, hdN⟩, rfl⟩ := ha
        obtain ⟨k, hk⟩ := hdN
        have hdpos : 0 < d := by omega
        have hkd : d * k / d = k := Nat.mul_div_cancel_left k hdpos
        refine ⟨?_, ?_, ?_⟩
        · rw [hk, hkd]; nlinarith
        · rw [hk, hkd]; nlinarith
        · rw [hk, hkd]; exact dvd_mul_left k d

private def s12 (N : ℕ) : ℕ :=
  (if 2 ∣ N then 1 else 0) + ((if 3 ∣ N then 1 else 0) + ((if 4 ∣ N then 1 else 0) +
  ((if 5 ∣ N then 1 else 0) + ((if 6 ∣ N then 1 else 0) + ((if 7 ∣ N then 1 else 0) +
  ((if 8 ∣ N then 1 else 0) + ((if 9 ∣ N then 1 else 0) + ((if 10 ∣ N then 1 else 0) +
  ((if 11 ∣ N then 1 else 0) + (if 12 ∣ N then 1 else 0))))))))))

private def s6 (N : ℕ) : ℕ :=
  (if 2 ∣ N then 1 else 0) + ((if 3 ∣ N then 1 else 0) + ((if 4 ∣ N then 1 else 0) +
  ((if 5 ∣ N then 1 else 0) + (if 6 ∣ N then 1 else 0))))

private lemma s12_eq (N : ℕ) : ((Finset.Icc 2 12).filter (· ∣ N)).card = s12 N := by
  rw [Finset.card_filter, show Finset.Icc 2 12 = {2,3,4,5,6,7,8,9,10,11,12} by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rfl


private lemma dvd_shift (m j M d : ℕ) (h : d ∣ M) : d ∣ m + j ↔ d ∣ m % M + j := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, Nat.add_mod m j d,
    Nat.add_mod (m % M) j d, Nat.mod_mod_of_dvd _ h]

private lemma s12_shift (m j : ℕ) : s12 (m + j) = s12 (m % 27720 + j) := by
  unfold s12
  simp only [dvd_shift m j 27720 2 (by norm_num), dvd_shift m j 27720 3 (by norm_num),
    dvd_shift m j 27720 4 (by norm_num), dvd_shift m j 27720 5 (by norm_num),
    dvd_shift m j 27720 6 (by norm_num), dvd_shift m j 27720 7 (by norm_num),
    dvd_shift m j 27720 8 (by norm_num), dvd_shift m j 27720 9 (by norm_num),
    dvd_shift m j 27720 10 (by norm_num), dvd_shift m j 27720 11 (by norm_num),
    dvd_shift m j 27720 12 (by norm_num)]

private lemma summ (m : ℕ) : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1) *
    ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_geometric_two.mul_left ((m : ℝ) / 2))
  have hc : ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) ≤ m := by
    have h1 : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1} ⊆ ((Finset.range m : Finset ℕ) : Set ℕ) := by
      intro a ha; simp only [Finset.coe_range, Set.mem_Iio]; exact ha.2.1
    have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Finset.card_range] at h2
    exact_mod_cast h2
  have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ i := by positivity
  rw [pow_succ]
  nlinarith


private lemma lb_tsum (m I : ℕ) : ∑ i ∈ Finset.range I, (1 / 2 : ℝ) ^ (i + 1) *
    ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
    ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) :=
  (summ m).sum_le_tsum _ (fun i _ => by positivity)


private def B3 (r i : ℕ) : ℕ := if i = 2 then max (s12 (r + i + 1)) 5 else s12 (r + i + 1)

private def W3 (r : ℕ) : ℕ :=
  2 ^ (11 - 0) * B3 r 0 + (2 ^ (11 - 1) * B3 r 1 + (2 ^ (11 - 2) * B3 r 2 + (2 ^ (11 - 3) * B3 r 3 + (2 ^ (11 - 4) * B3 r 4 + (2 ^ (11 - 5) * B3 r 5 + (2 ^ (11 - 6) * B3 r 6 + (2 ^ (11 - 7) * B3 r 7 + (2 ^ (11 - 8) * B3 r 8 + (2 ^ (11 - 9) * B3 r 9 + (2 ^ (11 - 10) * B3 r 10 + (2 ^ (11 - 11) * B3 r 11 + 0)))))))))))

private lemma w3_eq (r : ℕ) : W3 r = ∑ i ∈ Finset.range 12, 2 ^ (11 - i) * B3 r i := by
  rfl

private lemma half_pow (I i : ℕ) (hi : i < I) :
    (1 / 2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ (I - 1 - i) / 2 ^ I := by
  have h : (2 : ℝ) ^ (I - 1 - i) * 2 ^ (i + 1) = 2 ^ I := by
    rw [← pow_add, show I - 1 - i + (i + 1) = I by omega]
  rw [one_div_pow, div_eq_div_iff (by positivity) (by positivity)]
  linarith

private lemma real3 (r : ℕ) : ∑ i ∈ Finset.range 12, (1 / 2 : ℝ) ^ (i + 1) * (B3 r i : ℝ) =
    (W3 r : ℝ) / 4096 := by
  rw [w3_eq, show (4096 : ℝ) = 2 ^ 12 by norm_num]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [half_pow 12 i (Finset.mem_range.mp hi)]
  ring

private lemma chunk3_0 : ∀ k < 2000, (((0 + k) + 1) % 2 = 1 ∧ ((0 + k) + 1) % 3 ≠ 0 ∧
    ((0 + k) + 1) % 5 ≠ 0 ∧ ((0 + k) + 1) % 7 ≠ 0 ∧ ((0 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (0 + k) := by
  decide +kernel

private lemma chunk3_1 : ∀ k < 2000, (((2000 + k) + 1) % 2 = 1 ∧ ((2000 + k) + 1) % 3 ≠ 0 ∧
    ((2000 + k) + 1) % 5 ≠ 0 ∧ ((2000 + k) + 1) % 7 ≠ 0 ∧ ((2000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (2000 + k) := by
  decide +kernel

private lemma chunk3_2 : ∀ k < 2000, (((4000 + k) + 1) % 2 = 1 ∧ ((4000 + k) + 1) % 3 ≠ 0 ∧
    ((4000 + k) + 1) % 5 ≠ 0 ∧ ((4000 + k) + 1) % 7 ≠ 0 ∧ ((4000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (4000 + k) := by
  decide +kernel

private lemma chunk3_3 : ∀ k < 2000, (((6000 + k) + 1) % 2 = 1 ∧ ((6000 + k) + 1) % 3 ≠ 0 ∧
    ((6000 + k) + 1) % 5 ≠ 0 ∧ ((6000 + k) + 1) % 7 ≠ 0 ∧ ((6000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (6000 + k) := by
  decide +kernel

private lemma chunk3_4 : ∀ k < 2000, (((8000 + k) + 1) % 2 = 1 ∧ ((8000 + k) + 1) % 3 ≠ 0 ∧
    ((8000 + k) + 1) % 5 ≠ 0 ∧ ((8000 + k) + 1) % 7 ≠ 0 ∧ ((8000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (8000 + k) := by
  decide +kernel

private lemma chunk3_5 : ∀ k < 2000, (((10000 + k) + 1) % 2 = 1 ∧ ((10000 + k) + 1) % 3 ≠ 0 ∧
    ((10000 + k) + 1) % 5 ≠ 0 ∧ ((10000 + k) + 1) % 7 ≠ 0 ∧ ((10000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (10000 + k) := by
  decide +kernel

private lemma chunk3_6 : ∀ k < 2000, (((12000 + k) + 1) % 2 = 1 ∧ ((12000 + k) + 1) % 3 ≠ 0 ∧
    ((12000 + k) + 1) % 5 ≠ 0 ∧ ((12000 + k) + 1) % 7 ≠ 0 ∧ ((12000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (12000 + k) := by
  decide +kernel

private lemma chunk3_7 : ∀ k < 2000, (((14000 + k) + 1) % 2 = 1 ∧ ((14000 + k) + 1) % 3 ≠ 0 ∧
    ((14000 + k) + 1) % 5 ≠ 0 ∧ ((14000 + k) + 1) % 7 ≠ 0 ∧ ((14000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (14000 + k) := by
  decide +kernel

private lemma chunk3_8 : ∀ k < 2000, (((16000 + k) + 1) % 2 = 1 ∧ ((16000 + k) + 1) % 3 ≠ 0 ∧
    ((16000 + k) + 1) % 5 ≠ 0 ∧ ((16000 + k) + 1) % 7 ≠ 0 ∧ ((16000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (16000 + k) := by
  decide +kernel

private lemma chunk3_9 : ∀ k < 2000, (((18000 + k) + 1) % 2 = 1 ∧ ((18000 + k) + 1) % 3 ≠ 0 ∧
    ((18000 + k) + 1) % 5 ≠ 0 ∧ ((18000 + k) + 1) % 7 ≠ 0 ∧ ((18000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (18000 + k) := by
  decide +kernel

private lemma chunk3_10 : ∀ k < 2000, (((20000 + k) + 1) % 2 = 1 ∧ ((20000 + k) + 1) % 3 ≠ 0 ∧
    ((20000 + k) + 1) % 5 ≠ 0 ∧ ((20000 + k) + 1) % 7 ≠ 0 ∧ ((20000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (20000 + k) := by
  decide +kernel

private lemma chunk3_11 : ∀ k < 2000, (((22000 + k) + 1) % 2 = 1 ∧ ((22000 + k) + 1) % 3 ≠ 0 ∧
    ((22000 + k) + 1) % 5 ≠ 0 ∧ ((22000 + k) + 1) % 7 ≠ 0 ∧ ((22000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (22000 + k) := by
  decide +kernel

private lemma chunk3_12 : ∀ k < 2000, (((24000 + k) + 1) % 2 = 1 ∧ ((24000 + k) + 1) % 3 ≠ 0 ∧
    ((24000 + k) + 1) % 5 ≠ 0 ∧ ((24000 + k) + 1) % 7 ≠ 0 ∧ ((24000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (24000 + k) := by
  decide +kernel

private lemma chunk3_13 : ∀ k < 1720, (((26000 + k) + 1) % 2 = 1 ∧ ((26000 + k) + 1) % 3 ≠ 0 ∧
    ((26000 + k) + 1) % 5 ≠ 0 ∧ ((26000 + k) + 1) % 7 ≠ 0 ∧ ((26000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * W3 (26000 + k) := by
  decide +kernel

private lemma key3 (r : ℕ) (hr : r < 27720) (h : (r + 1) % 2 = 1 ∧ (r + 1) % 3 ≠ 0 ∧
    (r + 1) % 5 ≠ 0 ∧ (r + 1) % 7 ≠ 0 ∧ (r + 1) % 11 ≠ 0) : 99 * 4096 < 100 * W3 r := by
  obtain ⟨c, k, hk, rfl⟩ : ∃ c k, k < 2000 ∧ r = 2000 * c + k :=
    ⟨r / 2000, r % 2000, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 2000).symm⟩
  have hc : c < 14 := by omega
  interval_cases c
  · exact chunk3_0 k (by omega) (by simpa using h)
  · exact chunk3_1 k (by omega) (by simpa using h)
  · exact chunk3_2 k (by omega) (by simpa using h)
  · exact chunk3_3 k (by omega) (by simpa using h)
  · exact chunk3_4 k (by omega) (by simpa using h)
  · exact chunk3_5 k (by omega) (by simpa using h)
  · exact chunk3_6 k (by omega) (by simpa using h)
  · exact chunk3_7 k (by omega) (by simpa using h)
  · exact chunk3_8 k (by omega) (by simpa using h)
  · exact chunk3_9 k (by omega) (by simpa using h)
  · exact chunk3_10 k (by omega) (by simpa using h)
  · exact chunk3_11 k (by omega) (by simpa using h)
  · exact chunk3_12 k (by omega) (by simpa using h)
  · exact chunk3_13 k (by omega) (by simpa using h)

/-- A third-position condition on the calm points of the hole `variant-cce9b284--h6`, the first
step of condition N1 of annex `eaaf51ac…` on that hole: for every `m ≥ 1092` with `m + 1`
prime, either `m + 3` has at most four divisors `a` with `20 < a < m`, or the weighted divisor
count `G(m) = ∑_{i ≥ 0} 2^{-(i+1)} #{a : 20 < a < m, a ∣ m + i + 1}` of that hole exceeds
`99/100`. With `spec-23231427` (a calm `m ≥ 1092` has `m + 1` prime), every calm point has at
most four divisors of `m + 3` in `(20, m)`. -/
theorem Opn.erdos_257_calm_point_third_position :
    ∀ m : ℕ, 1092 ≤ m → (m + 1).Prime →
      {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 3}.ncard ≤ 4 ∨
        (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
          ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
  intro m hm hp
  by_cases H : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 3}.ncard ≤ 4
  · exact Or.inl H
  right
  have h5 : 5 ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + 2 + 1}.ncard := by
    have : m + 2 + 1 = m + 3 := rfl
    rw [this]; omega
  have hq : ∀ q, 1 < q → q < m + 1 → ¬ q ∣ m + 1 := fun q h1 h2 hd => by
    rcases hp.eq_one_or_self_of_dvd q hd with h | h <;> omega
  have q2 := hq 2 (by norm_num) (by omega)
  have q3 := hq 3 (by norm_num) (by omega)
  have q5 := hq 5 (by norm_num) (by omega)
  have q7 := hq 7 (by norm_num) (by omega)
  have q11 := hq 11 (by norm_num) (by omega)
  have hres : (m % 27720 + 1) % 2 = 1 ∧ (m % 27720 + 1) % 3 ≠ 0 ∧ (m % 27720 + 1) % 5 ≠ 0 ∧
      (m % 27720 + 1) % 7 ≠ 0 ∧ (m % 27720 + 1) % 11 ≠ 0 := by
    omega
  have hkey := key3 (m % 27720) (Nat.mod_lt _ (by norm_num)) hres
  have hlb : ∀ i ∈ Finset.range 12, (1 / 2 : ℝ) ^ (i + 1) * (B3 (m % 27720) i : ℝ) ≤
      (1 / 2 : ℝ) ^ (i + 1) * ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hbase : s12 (m % 27720 + i + 1) ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard := by
      have hb := lb_small m (m + i + 1) 12 hm (by omega) (by omega) le_rfl
      have e := s12_shift m (i + 1)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at e
      rw [s12_eq, e] at hb
      exact hb
    have hB : B3 (m % 27720) i ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard := by
      unfold B3
      split_ifs with h1
      · subst h1
        exact max_le hbase h5
      · exact hbase
    exact_mod_cast hB
  have h1 := Finset.sum_le_sum hlb
  rw [real3] at h1
  have h2 := lb_tsum m 12
  have h3 : (99 * 4096 : ℝ) < 100 * (W3 (m % 27720) : ℝ) := by exact_mod_cast hkey
  linarith
