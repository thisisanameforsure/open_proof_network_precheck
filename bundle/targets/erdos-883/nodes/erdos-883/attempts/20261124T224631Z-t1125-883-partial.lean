/-
Copyright 2026 The Formal Conjectures Authors.

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
import Defs.AlgebraWeylAlgebra
import Defs.AnalysisSpecialFunctionsAdditiveCharacter
import Defs.CombinatoricsSimpleGraphCircumference
import Defs.CombinatoricsSimpleGraphClique
import Defs.CombinatoricsSimpleGraphColoringVertex
import Defs.DataNatPrimeFinset
import Defs.FieldTheoryMilnorKTheory
import Defs.GroupTheoryRationalClasses
import Defs.Local

/-! Erdős problem 883, part i: For $A\subseteq \{1,\ldots,n\}$ let $G(A)$ be the graph with vertex set $A$, where two integers are joined by an edge if they are coprime. — imported from google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/883.lean at d8d031d4998c78575159ccab9a7a9e95ce043883, Apache-2.0); stated as the registry states it; the names it takes from its file or the registry's library are ported mechanically under defs/ (R12, F14-T19). Drafted by gate/tools/wave.py (F14-T11) and read by the curator before import (R13). -/

open Filter
open scoped Classical
open Erdos883

private lemma erdos883_tri_mem {A : Finset ℕ} {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A)
    (hc : c ∈ A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (cab : Nat.Coprime a b)
    (cbc : Nat.Coprime b c) (cac : Nat.Coprime a c) :
    3 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let x : (A : Set ℕ) := ⟨a, ha⟩
  let y : (A : Set ℕ) := ⟨b, hb⟩
  let z : (A : Set ℕ) := ⟨c, hc⟩
  have hxy : (coprimeGraph.induce (A : Set ℕ)).Adj x y := by
    simp [x, y, coprimeGraph, SimpleGraph.fromRel_adj, hab]
    exact Or.inl cab
  have hyz : (coprimeGraph.induce (A : Set ℕ)).Adj y z := by
    simp [y, z, coprimeGraph, SimpleGraph.fromRel_adj, hbc]
    exact Or.inl cbc
  have hzx : (coprimeGraph.induce (A : Set ℕ)).Adj z x := by
    simp [z, x, coprimeGraph, SimpleGraph.fromRel_adj, Ne.symm hac]
    exact Or.inr cac
  refine ⟨⟨x, SimpleGraph.Walk.cons hxy (SimpleGraph.Walk.cons hyz
    (SimpleGraph.Walk.cons hzx SimpleGraph.Walk.nil)), ?_, rfl⟩, ⟨1, rfl⟩⟩
  have hxy' : x ≠ y := fun h => hab (congrArg Subtype.val h)
  have hyz' : y ≠ z := fun h => hbc (congrArg Subtype.val h)
  have hxz' : x ≠ z := fun h => hac (congrArg Subtype.val h)
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨?_, ?_⟩
  · apply SimpleGraph.Walk.IsPath.mk'
    simp [hyz', Ne.symm hxz', Ne.symm hxy']
  · simp [SimpleGraph.Walk.edges, hxy', hxz', hyz', Ne.symm hxy']

theorem Opn.erdos_883 :
    ∀ (n : ℕ) (A : Finset ℕ),
      A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 3 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  -- approach: split on l = 3 (three pairwise coprime elements, the Erdős extremal bound) and odd l ≥ 5
  -- licence: CC-BY-4.0
  -- label: Three pairwise coprime elements above the bound
  -- claim: $A\subseteq\{1,\dots,n\},\ |A|>\lfloor n/2\rfloor+\lfloor n/3\rfloor-\lfloor n/6\rfloor\implies\exists\,a,b,c\in A\ \text{distinct, pairwise coprime}$
  have h_tri : ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := sorry
  -- label: Odd cycles of length 5 to n/3 + 1
  -- claim: $A\subseteq\{1,\dots,n\},\ |A|>\lfloor n/2\rfloor+\lfloor n/3\rfloor-\lfloor n/6\rfloor,\ l\ \text{odd},\ 5\le l\le\lfloor n/3\rfloor+1\implies C_l\subseteq G(A)$
  have h_long : ∀ (n : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card →
      ∀ l : ℕ, Odd l → 5 ≤ l → l ≤ n / 3 + 1 →
        l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := sorry
  intro n A hA hcard l hl h3 hln
  rcases (show l = 3 ∨ 5 ≤ l by obtain ⟨k, rfl⟩ := hl; omega) with rfl | h5
  · obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, cab, cbc, cac⟩ := h_tri n A hA hcard
    exact erdos883_tri_mem ha hb hc hab hbc hac cab cbc cac
  · exact h_long n A hA hcard l hl h5 hln
