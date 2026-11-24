/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import Defs.AnalysisSpecialFunctionsAdditiveCharacter

/-! Reed's omega, delta, and chi conjecture — imported from google-deepmind/formal-conjectures (FormalConjectures/Paper/ReedOmegaDeltaChi.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open scoped Finset

theorem Opn.reed_omega_delta_chi_conjecture_for_finite_graphs :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    let χ := G.chromaticNumber
    let ω := G.cliqueNum
    let Δ := G.maxDegree
    2 * χ ≤ ω + Δ + 2 := by
  -- approach: Greedy colouring and Brooks's theorem settle every graph with clique number at least Δ − 2; what remains is the case ω ≤ Δ − 3.
  -- licence: CC-BY-4.0
  have hall :
      (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.Colorable (G.maxDegree + 1)) ∧
      (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.maxDegree ≤ G.cliqueNum ∨ G.Colorable G.maxDegree) ∧
      (∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.maxDegree ≤ G.cliqueNum + 2 ∨
          ∃ k : ℕ, G.Colorable k ∧ 2 * k ≤ G.cliqueNum + G.maxDegree + 2) := by
    refine ⟨?_, ?_, ?_⟩
    · -- label: greedy colouring bound
      -- claim: $\chi(G) \le \Delta(G) + 1$ for every finite simple graph $G$
      -- Colour the vertices one at a time; each vertex has at most Δ coloured neighbours.
      have h_greedy : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj], G.Colorable (G.maxDegree + 1) := by sorry
      exact @h_greedy
    · -- label: Brooks's theorem, clique-number form
      -- claim: $\omega(G) < \Delta(G) \Rightarrow \chi(G) \le \Delta(G)$ for every finite simple graph $G$
      -- Stated as a disjunction: either Δ ≤ ω, or G is Δ-colourable.
      have h_brooks : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj], G.maxDegree ≤ G.cliqueNum ∨ G.Colorable G.maxDegree := by sorry
      exact @h_brooks
    · -- label: Reed's bound when ω ≤ Δ − 3
      -- claim: $\Delta(G) \ge \omega(G) + 3 \Rightarrow 2\chi(G) \le \omega(G) + \Delta(G) + 2$ for every finite simple graph $G$
      -- Stated as a disjunction: either Δ ≤ ω + 2, or some k-colouring has 2k ≤ ω + Δ + 2.
      have h_core : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
          [DecidableRel G.Adj], G.maxDegree ≤ G.cliqueNum + 2 ∨
            ∃ k : ℕ, G.Colorable k ∧ 2 * k ≤ G.cliqueNum + G.maxDegree + 2 := by sorry
      exact @h_core
  obtain ⟨hg, hb, hc⟩ := hall
  intro V _ _ G _
  have key : ∃ k : ℕ, G.Colorable k ∧ 2 * k ≤ G.cliqueNum + G.maxDegree + 2 := by
    rcases hc G with h1 | h1
    · rcases hb G with h2 | h2
      · exact ⟨G.maxDegree + 1, hg G, by omega⟩
      · exact ⟨G.maxDegree, h2, by omega⟩
    · exact h1
  obtain ⟨k, hk, hk2⟩ := key
  intro χ ω Δ
  have hχ : χ ≤ (k : ℕ∞) := hk.chromaticNumber_le
  calc 2 * χ ≤ 2 * (k : ℕ∞) := by gcongr
    _ = ((2 * k : ℕ) : ℕ∞) := by push_cast; ring
    _ ≤ ((ω + Δ + 2 : ℕ) : ℕ∞) := by exact_mod_cast hk2
    _ = (ω : ℕ∞) + Δ + 2 := by push_cast; ring
