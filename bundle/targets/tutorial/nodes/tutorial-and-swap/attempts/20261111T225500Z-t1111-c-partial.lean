/-! The tutorial node (D-27): permanently open, off-ledger. Lean core only. -/

theorem OpnProp.and_swap : ∀ p q : Prop, p ∧ q → q ∧ p := by
  -- approach: probe of the label rule, each component as a hole in its own bullet
  -- licence: CC-BY-4.0
  intro p q h
  refine ⟨?_, ?_⟩
  ·
    -- label: the right component
    -- claim: $q$
    have h₁ : q := sorry
    exact h₁
  ·
    -- label: the left component
    -- claim: $p$
    have h₂ : p := sorry
    exact h₂
