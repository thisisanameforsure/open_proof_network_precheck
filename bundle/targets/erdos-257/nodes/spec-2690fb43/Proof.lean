import Mathlib
import Nodes.«spec-2690fb43».Context

private def bcnt (N : ℕ) : ℕ :=
  (if N % 2 = 0 then 1 else 0) +
  (if N % 3 = 0 then 1 else 0) +
  (if N % 4 = 0 then 1 else 0) +
  (if N % 5 = 0 then 1 else 0) +
  (if N % 6 = 0 then 1 else 0) +
  (if N % 8 = 0 then 1 else 0) +
  (if N % 9 = 0 then 1 else 0) +
  (if N % 10 = 0 then 1 else 0) +
  (if N % 12 = 0 then 1 else 0) +
  (if N % 15 = 0 then 1 else 0) +
  (if N % 16 = 0 then 1 else 0) +
  (if N % 18 = 0 then 1 else 0) +
  (if N % 20 = 0 then 1 else 0) +
  (if N % 24 = 0 then 1 else 0)

private abbrev cSet (m N : ℕ) : Set ℕ := {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}

private theorem bcnt_periodic (m k : ℕ) : bcnt (m % 720 + k) = bcnt (m + k) := by
  have h2 : (m % 720 + k) % 2 = (m + k) % 2 := by omega
  have h3 : (m % 720 + k) % 3 = (m + k) % 3 := by omega
  have h4 : (m % 720 + k) % 4 = (m + k) % 4 := by omega
  have h5 : (m % 720 + k) % 5 = (m + k) % 5 := by omega
  have h6 : (m % 720 + k) % 6 = (m + k) % 6 := by omega
  have h8 : (m % 720 + k) % 8 = (m + k) % 8 := by omega
  have h9 : (m % 720 + k) % 9 = (m + k) % 9 := by omega
  have h10 : (m % 720 + k) % 10 = (m + k) % 10 := by omega
  have h12 : (m % 720 + k) % 12 = (m + k) % 12 := by omega
  have h15 : (m % 720 + k) % 15 = (m + k) % 15 := by omega
  have h16 : (m % 720 + k) % 16 = (m + k) % 16 := by omega
  have h18 : (m % 720 + k) % 18 = (m + k) % 18 := by omega
  have h20 : (m % 720 + k) % 20 = (m + k) % 20 := by omega
  have h24 : (m % 720 + k) % 24 = (m + k) % 24 := by omega
  unfold bcnt
  rw [h2, h3, h4, h5, h6, h8, h9, h10, h12, h15, h16, h18, h20, h24]

private theorem bA : ∀ r < 720, r % 2 = 1 →
    1014 ≤ 512 * bcnt (r + 1) + 256 * bcnt (r + 2) + 128 * bcnt (r + 3) + 64 * bcnt (r + 4) + 32 * bcnt (r + 5) + 16 * bcnt (r + 6) + 8 * bcnt (r + 7) + 4 * bcnt (r + 8) + 2 * bcnt (r + 9) + 1 * bcnt (r + 10) := by
  decide +kernel

private theorem bB : ∀ r < 720, r % 2 = 0 →
    1014 ≤ 512 * max 1 (bcnt (r + 1)) + 256 * bcnt (r + 2) + 128 * bcnt (r + 3) + 64 * bcnt (r + 4) + 32 * bcnt (r + 5) + 16 * bcnt (r + 6) + 8 * bcnt (r + 7) + 4 * bcnt (r + 8) + 2 * bcnt (r + 9) + 1 * bcnt (r + 10) := by
  decide +kernel

private theorem bC : ∀ r < 720, r % 2 = 0 →
    1014 ≤ 512 * bcnt (r + 1) + 256 * max 3 (bcnt (r + 2)) + 128 * bcnt (r + 3) + 64 * bcnt (r + 4) + 32 * bcnt (r + 5) + 16 * bcnt (r + 6) + 8 * bcnt (r + 7) + 4 * bcnt (r + 8) + 2 * bcnt (r + 9) + 1 * bcnt (r + 10) := by
  decide +kernel

private theorem cS_ge_card (m N : ℕ) (T : Finset ℕ)
    (h : ∀ a ∈ T, 20 < a ∧ a < m ∧ a ∣ N) : T.card ≤ (cSet m N).ncard := by
  have hfin : {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}.Finite :=
    (Finset.range m).finite_toSet.subset (fun a ha => by simpa using ha.2.1)
  have h1 := Set.ncard_le_ncard (s := (↑T : Set ℕ)) (fun a ha => h a (by simpa using ha)) hfin
  rw [Set.ncard_coe_finset] at h1
  exact h1

private theorem cS_le (m N : ℕ) : (cSet m N).ncard ≤ m := by
  have h1 := Set.ncard_le_ncard (s := {a : ℕ | 20 < a ∧ a < m ∧ a ∣ N}) (t := (↑(Finset.range m) : Set ℕ))
    (fun a ha => by simpa using ha.2.1) (Finset.range m).finite_toSet
  rw [Set.ncard_coe_finset, Finset.card_range] at h1
  exact h1

private theorem bcnt_le (m N : ℕ) (h1 : 480 < N) (h2 : N < 2 * m) : bcnt N ≤ (cSet m N).ncard := by
  have hD : ∀ d ∈ ({2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24} : Finset ℕ), 2 ≤ d ∧ d ≤ 24 := by decide
  have hcard : bcnt N = (Finset.filter (fun d => d ∣ N) ({2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24} : Finset ℕ)).card := by
    rw [Finset.card_filter]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    simp only [bcnt, Nat.dvd_iff_mod_eq_zero]
    ring
  rw [hcard, ← Finset.card_image_of_injOn (f := fun d => N / d)]
  · apply cS_ge_card
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_filter] at hd
    obtain ⟨hd2, hd24⟩ := hD d hd.1
    obtain ⟨x, hx⟩ := hd.2
    have hdpos : 0 < d := by omega
    have hdiv : N / d = x := by rw [hx]; exact Nat.mul_div_cancel_left x hdpos
    rw [hdiv]
    have hx2 : 2 * x ≤ d * x := Nat.mul_le_mul_right x hd2
    refine ⟨?_, by omega, ⟨d, by rw [hx, mul_comm]⟩⟩
    by_contra hc
    have : d * x ≤ 24 * 20 := Nat.mul_le_mul hd24 (by omega)
    omega
  · intro d1 hd1 d2 hd2 he
    have hd1' := Finset.mem_filter.mp (Finset.mem_coe.mp hd1)
    have hd2' := Finset.mem_filter.mp (Finset.mem_coe.mp hd2)
    obtain ⟨x, hx⟩ := hd1'.2
    obtain ⟨y, hy⟩ := hd2'.2
    have p1 : 0 < d1 := by have := (hD d1 hd1'.1).1; omega
    have p2 : 0 < d2 := by have := (hD d2 hd2'.1).1; omega
    have e1 : N / d1 = x := by rw [hx]; exact Nat.mul_div_cancel_left x p1
    have e2 : N / d2 = y := by rw [hy]; exact Nat.mul_div_cancel_left y p2
    have hxy : x = y := by
      have he' : N / d1 = N / d2 := he
      rw [e1, e2] at he'
      exact he'
    subst hxy
    have hxpos : 0 < x := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0; omega
      · exact h0
    have : d1 * x = d2 * x := by rw [← hx, ← hy]
    exact Nat.eq_of_mul_eq_mul_right hxpos this

private theorem comp_factor (v : ℕ) (hv : 2 ≤ v) (hnp : ¬ v.Prime) :
    ∃ a b, v = a * b ∧ 2 ≤ a ∧ a ≤ b := by
  obtain ⟨b, hb⟩ := Nat.minFac_dvd v
  have hpa := Nat.minFac_prime (n := v) (by omega)
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < v) hnp
  refine ⟨v.minFac, b, hb, hpa.two_le, ?_⟩
  have h1 : v.minFac * v.minFac ≤ v.minFac * b := by
    calc v.minFac * v.minFac = v.minFac ^ 2 := (sq _).symm
      _ ≤ v := hsq
      _ = v.minFac * b := hb
  exact Nat.le_of_mul_le_mul_left h1 hpa.pos

private theorem cS_one (m : ℕ) (hm : 1093 ≤ m) (hnp : ¬ (m + 1).Prime) : 1 ≤ (cSet m (m + 1)).ncard := by
  obtain ⟨a, b, hab, ha2, hle⟩ := comp_factor (m + 1) (by omega) hnp
  have hb : 34 ≤ b := by
    by_contra hc
    have : a * b ≤ 33 * 33 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h2b : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
  have h := cS_ge_card m (m + 1) {b} (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨by omega, by omega, ⟨a, by rw [hab, mul_comm]⟩⟩)
  rw [Finset.card_singleton] at h
  exact h

private theorem cS_three (m : ℕ) (hm : 1093 ≤ m) (hev : m % 2 = 0)
    (hq : ¬ ((m + 2) / 2).Prime) (hq4 : ¬ ((m + 2) % 4 = 0 ∧ ((m + 2) / 4).Prime)) :
    3 ≤ (cSet m (m + 2)).ncard := by
  obtain ⟨u, hu⟩ : ∃ u, m + 2 = 2 * u := ⟨(m + 2) / 2, by omega⟩
  have hq' : ¬ u.Prime := by
    have e : (m + 2) / 2 = u := by omega
    rwa [e] at hq
  by_cases hu2 : u % 2 = 1
  · obtain ⟨a, b, hab, ha2, hle⟩ := comp_factor u (by omega) hq'
    have ha3 : 3 ≤ a := by
      by_contra hc
      have e : a = 2 := by omega
      subst e
      omega
    have hb : 24 ≤ b := by
      by_contra hc
      have : a * b ≤ 23 * 23 := Nat.mul_le_mul (by omega) (by omega)
      omega
    have h3b : 3 * b ≤ a * b := Nat.mul_le_mul_right b ha3
    have h := cS_ge_card m (m + 2) {b, 2 * b, a * b} (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx | hx
      · subst hx; exact ⟨by omega, by omega, ⟨2 * a, by rw [hu, hab]; ring⟩⟩
      · subst hx; exact ⟨by omega, by omega, ⟨a, by rw [hu, hab]; ring⟩⟩
      · subst hx; exact ⟨by omega, by omega, ⟨2, by rw [hu, hab]; ring⟩⟩)
    have hc : ({b, 2 * b, a * b} : Finset ℕ).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨b, 2 * b, a * b, by omega, by omega, by omega, rfl⟩
    omega
  · obtain ⟨v, hv⟩ : ∃ v, u = 2 * v := ⟨u / 2, by omega⟩
    have hv' : ¬ v.Prime := fun hp => hq4 ⟨by omega, by
      have e : (m + 2) / 4 = v := by omega
      rwa [e]⟩
    obtain ⟨a, b, hab, ha2, hle⟩ := comp_factor v (by omega) hv'
    have hb : 17 ≤ b := by
      by_contra hc
      have : a * b ≤ 16 * 16 := Nat.mul_le_mul (by omega) (by omega)
      omega
    by_cases ha : a = 2
    · subst ha
      have h := cS_ge_card m (m + 2) {b, 2 * b, 4 * b} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · subst hx; exact ⟨by omega, by omega, ⟨8, by omega⟩⟩
        · subst hx; exact ⟨by omega, by omega, ⟨4, by omega⟩⟩
        · subst hx; exact ⟨by omega, by omega, ⟨2, by omega⟩⟩)
      have hc : ({b, 2 * b, 4 * b} : Finset ℕ).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨b, 2 * b, 4 * b, by omega, by omega, by omega, rfl⟩
      omega
    · have h3b : 3 * b ≤ a * b := Nat.mul_le_mul_right b (by omega)
      have h := cS_ge_card m (m + 2) {2 * b, a * b, 2 * (a * b)} (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · subst hx; exact ⟨by omega, by omega, ⟨2 * a, by rw [hu, hv, hab]; ring⟩⟩
        · subst hx; exact ⟨by omega, by omega, ⟨4, by rw [hu, hv, hab]; ring⟩⟩
        · subst hx; exact ⟨by omega, by omega, ⟨2, by rw [hu, hv, hab]; ring⟩⟩)
      have hc : ({2 * b, a * b, 2 * (a * b)} : Finset ℕ).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨2 * b, a * b, 2 * (a * b), by omega, by omega, by omega, rfl⟩
      omega

private theorem L_real (m : ℕ)
    (hG : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (((cSet m (m + i + 1)).ncard : ℕ) : ℝ) ≤ 99 / 100) :
    512 * (cSet m (m + 1)).ncard + 256 * (cSet m (m + 2)).ncard + 128 * (cSet m (m + 3)).ncard + 64 * (cSet m (m + 4)).ncard + 32 * (cSet m (m + 5)).ncard + 16 * (cSet m (m + 6)).ncard + 8 * (cSet m (m + 7)).ncard + 4 * (cSet m (m + 8)).ncard + 2 * (cSet m (m + 9)).ncard + 1 * (cSet m (m + 10)).ncard ≤ 1013 := by
  have hsum : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + 1) * (((cSet m (m + i + 1)).ncard : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
      (((summable_nat_add_iff 1).2 summable_geometric_two).mul_right (m : ℝ))
    have hc : (((cSet m (m + i + 1)).ncard : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast cS_le m (m + i + 1)
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have h := (hsum.sum_le_tsum (Finset.range 10) (fun i _ => by positivity)).trans hG
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_assoc] at h
  norm_num at h
  by_contra hc
  have hc2 := Nat.lt_of_not_ge hc
  have hc' : (1014 : ℝ) ≤ ((512 * (cSet m (m + 1)).ncard + 256 * (cSet m (m + 2)).ncard + 128 * (cSet m (m + 3)).ncard + 64 * (cSet m (m + 4)).ncard + 32 * (cSet m (m + 5)).ncard + 16 * (cSet m (m + 6)).ncard + 8 * (cSet m (m + 7)).ncard + 4 * (cSet m (m + 8)).ncard + 2 * (cSet m (m + 9)).ncard + 1 * (cSet m (m + 10)).ncard : ℕ) : ℝ) := by exact_mod_cast hc2
  push_cast at hc'
  linarith

private theorem calm_structure (m : ℕ) (hm : 1093 ≤ m)
    (hL : 512 * (cSet m (m + 1)).ncard + 256 * (cSet m (m + 2)).ncard + 128 * (cSet m (m + 3)).ncard + 64 * (cSet m (m + 4)).ncard + 32 * (cSet m (m + 5)).ncard + 16 * (cSet m (m + 6)).ncard + 8 * (cSet m (m + 7)).ncard + 4 * (cSet m (m + 8)).ncard + 2 * (cSet m (m + 9)).ncard + 1 * (cSet m (m + 10)).ncard ≤ 1013) :
    (m + 1).Prime ∧ ∃ q : ℕ, q.Prime ∧ (m + 2 = 2 * q ∨ m + 2 = 4 * q) := by
  have hb1 := bcnt_le m (m + 1) (by omega) (by omega)
  have hb2 := bcnt_le m (m + 2) (by omega) (by omega)
  have hb3 := bcnt_le m (m + 3) (by omega) (by omega)
  have hb4 := bcnt_le m (m + 4) (by omega) (by omega)
  have hb5 := bcnt_le m (m + 5) (by omega) (by omega)
  have hb6 := bcnt_le m (m + 6) (by omega) (by omega)
  have hb7 := bcnt_le m (m + 7) (by omega) (by omega)
  have hb8 := bcnt_le m (m + 8) (by omega) (by omega)
  have hb9 := bcnt_le m (m + 9) (by omega) (by omega)
  have hb10 := bcnt_le m (m + 10) (by omega) (by omega)
  have hr : m % 720 < 720 := Nat.mod_lt _ (by norm_num)
  by_cases hodd : m % 2 = 1
  · have h := bA (m % 720) hr (by omega)
    rw [bcnt_periodic m 1, bcnt_periodic m 2, bcnt_periodic m 3, bcnt_periodic m 4, bcnt_periodic m 5, bcnt_periodic m 6, bcnt_periodic m 7, bcnt_periodic m 8, bcnt_periodic m 9, bcnt_periodic m 10] at h
    omega
  have hev : m % 2 = 0 := by omega
  by_cases hp1 : (m + 1).Prime
  swap
  · have h1 := cS_one m hm hp1
    have h := bB (m % 720) hr (by omega)
    rw [bcnt_periodic m 1, bcnt_periodic m 2, bcnt_periodic m 3, bcnt_periodic m 4, bcnt_periodic m 5, bcnt_periodic m 6, bcnt_periodic m 7, bcnt_periodic m 8, bcnt_periodic m 9, bcnt_periodic m 10] at h
    omega
  refine ⟨hp1, ?_⟩
  by_cases hq : ((m + 2) / 2).Prime
  · exact ⟨(m + 2) / 2, hq, Or.inl (by omega)⟩
  by_cases hq4 : (m + 2) % 4 = 0 ∧ ((m + 2) / 4).Prime
  · exact ⟨(m + 2) / 4, hq4.2, Or.inr (by omega)⟩
  have h3 := cS_three m hm hev hq hq4
  have h := bC (m % 720) hr (by omega)
  rw [bcnt_periodic m 1, bcnt_periodic m 2, bcnt_periodic m 3, bcnt_periodic m 4, bcnt_periodic m 5, bcnt_periodic m 6, bcnt_periodic m 7, bcnt_periodic m 8, bcnt_periodic m 9, bcnt_periodic m 10] at h
  omega

/-- The barrier for the calm-points hole `variant-cce9b284--h6`: the hole implies a
twin-prime-type statement. If every interval `(n, 2n - 10]` with `n ≥ 1092` contains a calm point
`m` (weighted divisor count at most `99/100`, verbatim the statement of `variant-cce9b284--h6`),
then every such interval contains `m = 2q - 2` or `m = 4q - 2` with `q` and `m + 1` both prime.
The implication `H → P` is written in the classically equivalent form `¬ H ∨ P` because `H` is
the open hole itself: nobody can exhibit a witness of it, which a hypothesis would require. -/
theorem calm_points_imply_prime_pairs :
  ¬ (∀ n : ℕ, 1092 ≤ n → ∃ m : ℕ, n < m ∧ m + 10 ≤ 2 * n ∧
     ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + 1) * (({a : ℕ | 20 < a ∧ a < m ∧ a ∣ m + i + 1}.ncard : ℕ) : ℝ) ≤ 99 / 100) ∨
  (∀ n : ℕ, 1092 ≤ n → ∃ q : ℕ, q.Prime ∧
     ((n < 2*q - 2 ∧ 2*q + 8 ≤ 2*n ∧ (2*q - 1).Prime) ∨
      (n < 4*q - 2 ∧ 4*q + 8 ≤ 2*n ∧ (4*q - 1).Prime))) := by
  refine or_iff_not_imp_left.mpr (fun hn => ?_)
  have h := not_not.mp hn
  intro n hn
  obtain ⟨m, h1, h2, h3⟩ := h n hn
  obtain ⟨hp1, q, hq, hcase⟩ := calm_structure m (by omega) (L_real m h3)
  refine ⟨q, hq, ?_⟩
  rcases hcase with hc | hc
  · left
    have e : 2 * q - 1 = m + 1 := by omega
    rw [e]
    exact ⟨by omega, by omega, hp1⟩
  · right
    have e : 4 * q - 1 = m + 1 := by omega
    rw [e]
    exact ⟨by omega, by omega, hp1⟩
