theorem OpnProp.and_swap : ∀ p q : Prop, p ∧ q → q ∧ p := by
  intro p q hpq
  exact ⟨hpq.right, hpq.left⟩
