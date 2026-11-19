import Mathlib
import Nodes.«spec-23231427».Context

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

private lemma comp_lb (m N : ℕ) (hm : 1092 ≤ m) (hN : N = m + 1) (hp : ¬ N.Prime) :
    1 ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.ncard := by
  have hfin : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.Finite :=
    (Set.finite_Iio m).subset (fun a ha => ha.2.1)
  have hN1 : N ≠ 1 := by omega
  have hpp : N.minFac.Prime := Nat.minFac_prime hN1
  have h2 : 2 ≤ N.minFac := hpp.two_le
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hp
  obtain ⟨a, ha⟩ := Nat.minFac_dvd N
  have hmem : a ∈ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N} := by
    refine ⟨?_, ?_, Dvd.intro_left _ ha.symm⟩
    · have hpa : N.minFac ≤ a := by nlinarith
      nlinarith
    · nlinarith
  exact (Set.ncard_pos hfin).mpr ⟨a, hmem⟩ |> Nat.one_le_iff_ne_zero.mpr ∘ Nat.pos_iff_ne_zero.mp

private lemma three_mem {S : Set ℕ} (hS : S.Finite) {x y z : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : 3 ≤ S.ncard := by
  have h3 : ({x, y, z} : Set ℕ).ncard = 3 := Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  rw [← h3]
  apply Set.ncard_le_ncard _ hS
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl <;> assumption

private lemma three_lb (m N : ℕ) (hm : 1092 ≤ m) (hN : N = m + 2) (hp : (m + 1).Prime)
    (hs : ¬(((m + 2) / 2).Prime ∨ (4 ∣ m + 2 ∧ ((m + 2) / 4).Prime))) :
    3 ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.ncard := by
  have hfin : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.Finite :=
    (Set.finite_Iio m).subset (fun a ha => ha.2.1)
  have hodd : ¬ 2 ∣ m + 1 := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 2 h with h' | h' <;> omega
  obtain ⟨u, hu⟩ : ∃ u, m + 2 = 2 * u := ⟨(m + 2) / 2, by omega⟩
  have hu2 : (m + 2) / 2 = u := by omega
  rw [hu2] at hs
  have hun : ¬ u.Prime := fun h => hs (Or.inl h)
  rcases Nat.even_or_odd u with ⟨t, ht⟩ | huo
  · -- u = t + t
    have ht4 : (m + 2) / 4 = t := by omega
    have h4 : 4 ∣ m + 2 := ⟨t, by omega⟩
    rw [ht4] at hs
    have htn : ¬ t.Prime := fun h => hs (Or.inr ⟨h4, h⟩)
    have ht1 : t ≠ 1 := by omega
    have hpp : t.minFac.Prime := Nat.minFac_prime ht1
    have h2 : 2 ≤ t.minFac := hpp.two_le
    have hsq : t.minFac ^ 2 ≤ t := Nat.minFac_sq_le_self (by omega) htn
    obtain ⟨w, hw⟩ := Nat.minFac_dvd t
    set s := t.minFac with hsdef
    have hsw : s ≤ w := by nlinarith
    by_cases hs2 : s = 2
    · rw [hs2] at hw
      apply three_mem hfin (x := 2 * t) (y := t) (z := w)
      · exact ⟨by omega, by omega, ⟨2, by omega⟩⟩
      · exact ⟨by omega, by omega, ⟨4, by omega⟩⟩
      · exact ⟨by omega, by omega, ⟨8, by rw [hN]; omega⟩⟩
      all_goals omega
    · have hs3 : 3 ≤ s := by omega
      have hw17 : 17 ≤ w := by nlinarith
      apply three_mem hfin (x := 2 * t) (y := t) (z := 2 * w)
      · exact ⟨by omega, by omega, ⟨2, by omega⟩⟩
      · exact ⟨by omega, by omega, ⟨4, by omega⟩⟩
      · refine ⟨by omega, by nlinarith, ⟨2 * s, ?_⟩⟩
        rw [hN, hu, ht, hw]; ring
      · omega
      · nlinarith
      · nlinarith
  · obtain ⟨k, hk⟩ := huo
    have hu1 : u ≠ 1 := by omega
    have hpp : u.minFac.Prime := Nat.minFac_prime hu1
    have h2 : 2 ≤ u.minFac := hpp.two_le
    have hsq : u.minFac ^ 2 ≤ u := Nat.minFac_sq_le_self (by omega) hun
    obtain ⟨v, hv⟩ := Nat.minFac_dvd u
    set s := u.minFac with hsdef
    have hs2 : s ≠ 2 := by
      intro h; rw [h] at hv; omega
    have hs3 : 3 ≤ s := by omega
    have hsv : s ≤ v := by nlinarith
    have hv24 : 24 ≤ v := by nlinarith
    apply three_mem hfin (x := u) (y := 2 * v) (z := v)
    · exact ⟨by omega, by omega, ⟨2, by omega⟩⟩
    · refine ⟨by omega, by nlinarith, ⟨s, ?_⟩⟩
      rw [hN, hu, hv]; ring
    · refine ⟨by omega, by nlinarith, ⟨2 * s, ?_⟩⟩
      rw [hN, hu, hv]; ring
    · nlinarith
    · nlinarith
    · omega

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

private lemma s6_eq (N : ℕ) : ((Finset.Icc 2 6).filter (· ∣ N)).card = s6 N := by
  rw [Finset.card_filter, show Finset.Icc 2 6 = {2,3,4,5,6} by decide]
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

private lemma s6_shift (m j : ℕ) : s6 (m + j) = s6 (m % 60 + j) := by
  unfold s6
  simp only [dvd_shift m j 60 2 (by norm_num), dvd_shift m j 60 3 (by norm_num),
    dvd_shift m j 60 4 (by norm_num), dvd_shift m j 60 5 (by norm_num),
    dvd_shift m j 60 6 (by norm_num)]

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


private def B12 (r i : ℕ) : ℕ := if i = 1 then max (s12 (r + i + 1)) 3 else s12 (r + i + 1)

private def Wu (r : ℕ) : ℕ :=
  2 ^ (11 - 0) * B12 r 0 + (2 ^ (11 - 1) * B12 r 1 + (2 ^ (11 - 2) * B12 r 2 + (2 ^ (11 - 3) * B12 r 3 + (2 ^ (11 - 4) * B12 r 4 + (2 ^ (11 - 5) * B12 r 5 + (2 ^ (11 - 6) * B12 r 6 + (2 ^ (11 - 7) * B12 r 7 + (2 ^ (11 - 8) * B12 r 8 + (2 ^ (11 - 9) * B12 r 9 + (2 ^ (11 - 10) * B12 r 10 + (2 ^ (11 - 11) * B12 r 11 + 0)))))))))))

private def B6 (r i : ℕ) : ℕ := if i = 0 then max (s6 (r + i + 1)) 1 else s6 (r + i + 1)

private def W6 (r : ℕ) : ℕ :=
  2 ^ (7 - 0) * B6 r 0 + (2 ^ (7 - 1) * B6 r 1 + (2 ^ (7 - 2) * B6 r 2 + (2 ^ (7 - 3) * B6 r 3 + (2 ^ (7 - 4) * B6 r 4 + (2 ^ (7 - 5) * B6 r 5 + (2 ^ (7 - 6) * B6 r 6 + (2 ^ (7 - 7) * B6 r 7 + 0)))))))

private lemma wu_eq (r : ℕ) : Wu r = ∑ i ∈ Finset.range 12, 2 ^ (11 - i) * B12 r i := by
  rfl

private lemma w6_eq (r : ℕ) : W6 r = ∑ i ∈ Finset.range 8, 2 ^ (7 - i) * B6 r i := by
  rfl

private lemma key60 : ∀ r < 60, 99 * 256 < 100 * W6 r := by
  decide +kernel

private lemma half_pow (I i : ℕ) (hi : i < I) :
    (1 / 2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ (I - 1 - i) / 2 ^ I := by
  have h : (2 : ℝ) ^ (I - 1 - i) * 2 ^ (i + 1) = 2 ^ I := by
    rw [← pow_add, show I - 1 - i + (i + 1) = I by omega]
  rw [one_div_pow, div_eq_div_iff (by positivity) (by positivity)]
  linarith

private lemma real12 (r : ℕ) : ∑ i ∈ Finset.range 12, (1 / 2 : ℝ) ^ (i + 1) * (B12 r i : ℝ) =
    (Wu r : ℝ) / 4096 := by
  rw [wu_eq, show (4096 : ℝ) = 2 ^ 12 by norm_num]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [half_pow 12 i (Finset.mem_range.mp hi)]
  ring

private lemma real6 (r : ℕ) : ∑ i ∈ Finset.range 8, (1 / 2 : ℝ) ^ (i + 1) * (B6 r i : ℝ) =
    (W6 r : ℝ) / 256 := by
  rw [w6_eq, show (256 : ℝ) = 2 ^ 8 by norm_num]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [half_pow 8 i (Finset.mem_range.mp hi)]
  ring
private lemma chunk0 : ∀ k < 2000, (((0 + k) + 1) % 2 = 1 ∧ ((0 + k) + 1) % 3 ≠ 0 ∧
    ((0 + k) + 1) % 5 ≠ 0 ∧ ((0 + k) + 1) % 7 ≠ 0 ∧ ((0 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (0 + k) := by
  decide +kernel

private lemma chunk1 : ∀ k < 2000, (((2000 + k) + 1) % 2 = 1 ∧ ((2000 + k) + 1) % 3 ≠ 0 ∧
    ((2000 + k) + 1) % 5 ≠ 0 ∧ ((2000 + k) + 1) % 7 ≠ 0 ∧ ((2000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (2000 + k) := by
  decide +kernel

private lemma chunk2 : ∀ k < 2000, (((4000 + k) + 1) % 2 = 1 ∧ ((4000 + k) + 1) % 3 ≠ 0 ∧
    ((4000 + k) + 1) % 5 ≠ 0 ∧ ((4000 + k) + 1) % 7 ≠ 0 ∧ ((4000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (4000 + k) := by
  decide +kernel

private lemma chunk3 : ∀ k < 2000, (((6000 + k) + 1) % 2 = 1 ∧ ((6000 + k) + 1) % 3 ≠ 0 ∧
    ((6000 + k) + 1) % 5 ≠ 0 ∧ ((6000 + k) + 1) % 7 ≠ 0 ∧ ((6000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (6000 + k) := by
  decide +kernel

private lemma chunk4 : ∀ k < 2000, (((8000 + k) + 1) % 2 = 1 ∧ ((8000 + k) + 1) % 3 ≠ 0 ∧
    ((8000 + k) + 1) % 5 ≠ 0 ∧ ((8000 + k) + 1) % 7 ≠ 0 ∧ ((8000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (8000 + k) := by
  decide +kernel

private lemma chunk5 : ∀ k < 2000, (((10000 + k) + 1) % 2 = 1 ∧ ((10000 + k) + 1) % 3 ≠ 0 ∧
    ((10000 + k) + 1) % 5 ≠ 0 ∧ ((10000 + k) + 1) % 7 ≠ 0 ∧ ((10000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (10000 + k) := by
  decide +kernel

private lemma chunk6 : ∀ k < 2000, (((12000 + k) + 1) % 2 = 1 ∧ ((12000 + k) + 1) % 3 ≠ 0 ∧
    ((12000 + k) + 1) % 5 ≠ 0 ∧ ((12000 + k) + 1) % 7 ≠ 0 ∧ ((12000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (12000 + k) := by
  decide +kernel

private lemma chunk7 : ∀ k < 2000, (((14000 + k) + 1) % 2 = 1 ∧ ((14000 + k) + 1) % 3 ≠ 0 ∧
    ((14000 + k) + 1) % 5 ≠ 0 ∧ ((14000 + k) + 1) % 7 ≠ 0 ∧ ((14000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (14000 + k) := by
  decide +kernel

private lemma chunk8 : ∀ k < 2000, (((16000 + k) + 1) % 2 = 1 ∧ ((16000 + k) + 1) % 3 ≠ 0 ∧
    ((16000 + k) + 1) % 5 ≠ 0 ∧ ((16000 + k) + 1) % 7 ≠ 0 ∧ ((16000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (16000 + k) := by
  decide +kernel

private lemma chunk9 : ∀ k < 2000, (((18000 + k) + 1) % 2 = 1 ∧ ((18000 + k) + 1) % 3 ≠ 0 ∧
    ((18000 + k) + 1) % 5 ≠ 0 ∧ ((18000 + k) + 1) % 7 ≠ 0 ∧ ((18000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (18000 + k) := by
  decide +kernel

private lemma chunk10 : ∀ k < 2000, (((20000 + k) + 1) % 2 = 1 ∧ ((20000 + k) + 1) % 3 ≠ 0 ∧
    ((20000 + k) + 1) % 5 ≠ 0 ∧ ((20000 + k) + 1) % 7 ≠ 0 ∧ ((20000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (20000 + k) := by
  decide +kernel

private lemma chunk11 : ∀ k < 2000, (((22000 + k) + 1) % 2 = 1 ∧ ((22000 + k) + 1) % 3 ≠ 0 ∧
    ((22000 + k) + 1) % 5 ≠ 0 ∧ ((22000 + k) + 1) % 7 ≠ 0 ∧ ((22000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (22000 + k) := by
  decide +kernel

private lemma chunk12 : ∀ k < 2000, (((24000 + k) + 1) % 2 = 1 ∧ ((24000 + k) + 1) % 3 ≠ 0 ∧
    ((24000 + k) + 1) % 5 ≠ 0 ∧ ((24000 + k) + 1) % 7 ≠ 0 ∧ ((24000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (24000 + k) := by
  decide +kernel

private lemma chunk13 : ∀ k < 1720, (((26000 + k) + 1) % 2 = 1 ∧ ((26000 + k) + 1) % 3 ≠ 0 ∧
    ((26000 + k) + 1) % 5 ≠ 0 ∧ ((26000 + k) + 1) % 7 ≠ 0 ∧ ((26000 + k) + 1) % 11 ≠ 0) →
    99 * 4096 < 100 * Wu (26000 + k) := by
  decide +kernel

private lemma key12 (r : ℕ) (hr : r < 27720) (h : (r + 1) % 2 = 1 ∧ (r + 1) % 3 ≠ 0 ∧
    (r + 1) % 5 ≠ 0 ∧ (r + 1) % 7 ≠ 0 ∧ (r + 1) % 11 ≠ 0) : 99 * 4096 < 100 * Wu r := by
  obtain ⟨c, k, hk, rfl⟩ : ∃ c k, k < 2000 ∧ r = 2000 * c + k :=
    ⟨r / 2000, r % 2000, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 2000).symm⟩
  have hc : c < 14 := by omega
  interval_cases c
  · exact chunk0 k (by omega) (by simpa using h)
  · exact chunk1 k (by omega) (by simpa using h)
  · exact chunk2 k (by omega) (by simpa using h)
  · exact chunk3 k (by omega) (by simpa using h)
  · exact chunk4 k (by omega) (by simpa using h)
  · exact chunk5 k (by omega) (by simpa using h)
  · exact chunk6 k (by omega) (by simpa using h)
  · exact chunk7 k (by omega) (by simpa using h)
  · exact chunk8 k (by omega) (by simpa using h)
  · exact chunk9 k (by omega) (by simpa using h)
  · exact chunk10 k (by omega) (by simpa using h)
  · exact chunk11 k (by omega) (by simpa using h)
  · exact chunk12 k (by omega) (by simpa using h)
  · exact chunk13 k (by omega) (by simpa using h)


private lemma lb_tsum (m I : ℕ) : ∑ i ∈ Finset.range I, (1 / 2 : ℝ) ^ (i + 1) *
    ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
    ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) :=
  (summ m).sum_le_tsum _ (fun i _ => by positivity)

private lemma case_prime (m : ℕ) (hm : 1092 ≤ m) (hp : (m + 1).Prime)
    (hs : ¬(((m + 2) / 2).Prime ∨ (4 ∣ m + 2 ∧ ((m + 2) / 4).Prime))) :
    (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
      ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
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
  have hkey := key12 (m % 27720) (Nat.mod_lt _ (by norm_num)) hres
  have hlb : ∀ i ∈ Finset.range 12, (1 / 2 : ℝ) ^ (i + 1) * (B12 (m % 27720) i : ℝ) ≤
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
    have hB : B12 (m % 27720) i ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard := by
      unfold B12
      split_ifs with h1
      · subst h1
        exact max_le hbase (three_lb m (m + 1 + 1) hm (by omega) hp hs)
      · exact hbase
    exact_mod_cast hB
  have h1 := Finset.sum_le_sum hlb
  rw [real12] at h1
  have h2 := lb_tsum m 12
  have h3 : (99 * 4096 : ℝ) < 100 * (Wu (m % 27720) : ℝ) := by exact_mod_cast hkey
  linarith

private lemma case_comp (m : ℕ) (hm : 1092 ≤ m) (hp : ¬ (m + 1).Prime) :
    (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
      ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
  have hkey := key60 (m % 60) (Nat.mod_lt _ (by norm_num))
  have hlb : ∀ i ∈ Finset.range 8, (1 / 2 : ℝ) ^ (i + 1) * (B6 (m % 60) i : ℝ) ≤
      (1 / 2 : ℝ) ^ (i + 1) * ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hbase : s6 (m % 60 + i + 1) ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard := by
      have hb := lb_small m (m + i + 1) 6 hm (by omega) (by omega) (by norm_num)
      have e := s6_shift m (i + 1)
      rw [← Nat.add_assoc, ← Nat.add_assoc] at e
      rw [s6_eq, e] at hb
      exact hb
    have hB : B6 (m % 60) i ≤ {a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard := by
      unfold B6
      split_ifs with h1
      · subst h1
        exact max_le hbase (comp_lb m (m + 0 + 1) hm (by omega) hp)
      · exact hbase
    exact_mod_cast hB
  have h1 := Finset.sum_le_sum hlb
  rw [real6] at h1
  have h2 := lb_tsum m 8
  have h3 : (99 * 256 : ℝ) < 100 * (W6 (m % 60) : ℝ) := by exact_mod_cast hkey
  linarith

/-- The structure lemma for the calm points of the hole `variant-cce9b284--h6` (annex
`e0c02cd3…` on that hole), stated in positive form: for every `m ≥ 1092`, either `m + 1` is prime
and `(m + 2)/2` is prime or `4 ∣ m + 2` with `(m + 2)/4` prime, or the weighted divisor count
`G(m) = ∑_{i ≥ 0} 2^{-(i+1)} #{a : 20 < a < m, a ∣ m + i + 1}` of that hole exceeds `99/100`.
So every calm point `m ≥ 1092` (one with `G(m) ≤ 99/100`) has `m + 1` and `(m + 2)/2` or
`(m + 2)/4` prime, and the hole implies the prime-pair statement `spec-001a7622`. The natural
divisions are exact in the cases that matter (`m + 1` prime forces `m + 2` even). -/
theorem Opn.erdos_257_calm_point_structure :
    ∀ m : ℕ, 1092 ≤ m →
      ((m + 1).Prime ∧ (((m + 2) / 2).Prime ∨ (4 ∣ m + 2 ∧ ((m + 2) / 4).Prime))) ∨
        (99 / 100 : ℝ) < ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) *
          ({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℝ) := by
  intro m hm
  by_cases H : (m + 1).Prime ∧ (((m + 2) / 2).Prime ∨ (4 ∣ m + 2 ∧ ((m + 2) / 4).Prime))
  · exact Or.inl H
  right
  by_cases hp : (m + 1).Prime
  · exact case_prime m hm hp (fun h => H ⟨hp, h⟩)
  · exact case_comp m hm hp
