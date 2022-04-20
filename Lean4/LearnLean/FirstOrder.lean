section
  open Classical
  theorem drinker'sParadox
    : forall (bar : Type) (drinks : bar -> Prop) (client : bar),
      ∃ drinker : bar, (∃ x, drinks x) -> drinks drinker
    := by
    intro bar drinks client
    open Or in
    match em (∃ x, drinks x) with
    | inl h =>
      let ⟨drinker, drinks_drinker⟩ := h
      exists drinker
      intro _
      exact drinks_drinker 
    | inr h =>
      exists client
      intro g
      contradiction
end

def getHead : (l : List a) -> l ≠ [] -> a
| x :: _, _ => x

def getLast : (l : List a) -> l.length ≠ 0 -> a
| _ :: x :: xs, g => getLast (x :: xs) $ by
  simp [List.length]
  intro h
  sorry
| [x], _ => x

open Classical in
theorem twierdzenie_o_wodzireju
: ∀ (wesele : Type) (spiewa : wesele -> Prop) (weselarz : wesele),
    ∃ wodzirej : wesele, spiewa wodzirej -> ∀ x : wesele, spiewa x
:= by
intro wesele spiewa weselarz
cases em (∃ x : wesele, ¬ spiewa x)
case inl h =>
  let ⟨x, y⟩ := h
  exists x
  intros sings_x
  contradiction
case inr h =>
  exists weselarz
  intros s x
  cases em (spiewa x)
  case inl h' =>
    assumption
  case inr h' =>
    apply False.elim
    apply h
    exists x
    assumption