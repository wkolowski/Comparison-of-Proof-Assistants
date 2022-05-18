variable
  (p q r s : Prop)
  (p' q' r' s' : Prop)

-- * Kluczowe prawa

theorem noncontradiction :
  (p ∧ ¬ p) ↔ False := by
  constructor
  case mp =>
    intro ⟨x, nx⟩
    apply nx
    assumption
  case mpr =>
    intro f
    contradiction

theorem noncontradiction_iff :
  (p ↔ ¬ p) ↔ False := by
  constructor
  case mp =>
    intro ⟨f, g⟩
    apply f <;> apply g <;> intro x <;> apply f <;> assumption
  case mpr =>
    intro f
    contradiction

theorem Irrefutable_LEM :
  ¬ ¬ (p ∨ ¬ p) := by
  intro f
  apply f
  apply Or.inr
  intro x
  apply f
  apply Or.inl
  assumption

theorem Irrefutable_reductio_ad_absurdum :
  ¬ ¬ (¬ (p ∧ ¬ q) → (p → q)) := by
  intro f
  apply f
  intro g x
  apply False.elim
  apply g
  constructor
  case h.left =>
    assumption
  case h.right =>
    intro y
    apply False.elim
    apply f
    intro _ _
    assumption

theorem reductio_ad_absurdum_conv :
  (p → q) → ¬ (p ∧ ¬ q) := by
  intro f ⟨x, y⟩
  apply y
  apply f
  assumption

theorem resolution :
  (p ∨ q) ∧ (¬ p ∨ r) → q ∨ r := by
  intro ⟨x, y⟩
  cases x
  case inr =>
    apply Or.inl
    assumption
  case inl =>
    cases y
    case inl =>
      contradiction
    case inr =>
      apply Or.inr
      assumption

theorem resolution' :
  (p ∨ q) ∧ (¬ p ∨ r) → q ∨ r := by
  intro ⟨x, y⟩
  cases x <;> cases y <;> simp [*]
  contradiction