variable
  (p q r s : Prop)
  (p' q' r' s' : Prop)
 
-- * Kluczowe prawa

theorem noncontradiction :
  (p ∧ ¬ p) ↔ False := by
  sorry

theorem noncontradiction_curried :
  p → ¬ p → q := by
  sorry

theorem noncontradiction_iff :
  (p ↔ ¬ p) ↔ False := by
  sorry

theorem Irrefutable_LEM :
  ¬ ¬ (p ∨ ¬ p) := by
  sorry

theorem Irrefutable_reductio_ad_absurdum :
  ¬ ¬ (¬ (p ∧ ¬ q) → (p → q)) := by
  sorry

theorem reductio_ad_absurdum_conv :
  (p → q) → ¬ (p ∧ ¬ q) := by
  sorry

theorem resolution :
  (p ∨ q) ∧ (¬ p ∨ r) → q ∨ r := by
  sorry

-- * Dysjunkcja

-- ** reguły

theorem or_intro_l :
  p → p ∨ q := by
  sorry

theorem or_intro_r :
  q → p ∨ q := by
  sorry

theorem or_elim :
  (p → r) → (q → r) → (p ∨ q → r) := by
  sorry

-- ** Właściwości działaniowe

theorem or_True_l :
  True ∨ p ↔ True := by
  sorry

theorem or_True_r :
  p ∨ True ↔ True := by
  sorry

theorem or_False_l :
  False ∨ p ↔ p := by
  sorry

theorem or_False_r :
  p ∨ False ↔ p := by
  sorry

theorem or_True_l' :
  p → p ∨ q ↔ True := by
  sorry

theorem or_True_r' :
  q → p ∨ q ↔ True := by
  sorry

theorem or_False_l' :
  ¬ p → p ∨ q ↔ q := by
  sorry

theorem or_False_r' :
  ¬ q → p ∨ q ↔ p := by
  sorry

theorem or_idem :
  p ∨ p ↔ p := by
  sorry

theorem or_comm :
  p ∨ q ↔ q ∨ p := by
  sorry

theorem or_assoc :
  p ∨ (q ∨ r) ↔ (p ∨ q) ∨ r := by
  sorry

theorem or_mon_l :
  (p → q) → (r ∨ p → r ∨ q) := by
  sorry

theorem or_mon_r :
  (p → q) → (p ∨ r → q ∨ r) := by
  sorry

theorem or_mon :
  (p → q) → (r → s) → p ∨ r → q ∨ s := by
  sorry

theorem or_or_l :
  (p ∨ q) ∨ r ↔ (p ∨ r) ∨ (q ∨ r) := by
  sorry

theorem or_or_r :
  p ∨ (q ∨ r) ↔ (p ∨ q) ∨ (p ∨ r) := by
  sorry

theorem or_and_l :
  (p ∧ q) ∨ r ↔ (p ∨ r) ∧ (q ∨ r) := by
  sorry

theorem or_and_r :
  p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem or_and_l_abs :
  (p ∧ q) ∨ q ↔ q := by
  sorry

theorem or_and_r_abs :
  p ∨ (p ∧ q) ↔ p := by
  sorry

theorem or_iff_l :
  ((p ↔ q) ∨ r) → ((p ∨ r) ↔ (q ∨ r)) := by
  sorry

theorem or_iff_r :
  (p ∨ (q ↔ r)) → ((p ∨ q) ↔ (p ∨ r)) := by
  sorry

theorem or_impl_r :
  p ∨ (q → r) → (p ∨ q → p ∨ r) := by
  sorry

theorem Irrefutable_or_impl_r_conv :
  ¬ ¬ ((p ∨ q → p ∨ r) → p ∨ (q → r)) := by
  sorry

theorem Irrefutable_or_impl_r_conv' :
  (p ∨ q → p ∨ r) → ¬ ¬ (p ∨ (q → r)) := by
  sorry

theorem or_impl_l :
  (p → q) ∨ r → (p ∨ r) → (q ∨ r) := by
  sorry

theorem Irrefutable_or_impl_l :
  ¬ ¬ ((p ∨ r → q ∨ r) → (p → q) ∨ r) := by
  sorry

theorem Irrefutable_or_impl_l' :
  (p ∨ r → q ∨ r) → ¬ ¬ ((p → q) ∨ r) := by
  sorry

-- ** Właściwości relacjowe

-- ** pozostałe właściwości

theorem or_not_l :
  ¬ p ∨ q → (p → q) := by
  sorry

theorem Irrefutable_or_not_l_conv :
  ¬ ¬ ((p → q) → ¬ p ∨ q) := by
  sorry

theorem Irrefutable_or_not_l_conv' :
  (p → q) → ¬ ¬ (¬ p ∨ q) := by
  sorry

-- * Koniunkcja

-- ** reguły

theorem and_intro :
  p → q → p ∧ q := by
  sorry

theorem and_elim_l :
  p ∧ q → p := by
  sorry

theorem and_elim_r :
  p ∧ q → q := by
  sorry

theorem and_elim :
  (p → q → r) → (p ∧ q → r) := by
  sorry

-- ** Właściwości działaniowe

theorem and_True_l :
  True ∧ p ↔ p := by
  sorry

theorem and_True_r :
  p ∧ True ↔ p := by
  sorry

theorem and_False_l :
  False ∧ p ↔ False := by
  sorry

theorem and_False_r :
  p ∧ False ↔ False := by
  sorry

theorem and_True_l' :
  p → p ∧ q ↔ q := by
  sorry

theorem and_True_r' :
  q → p ∧ q ↔ p := by
  sorry

theorem and_False_l' :
  ¬ p → p ∧ q ↔ False := by
  sorry

theorem and_False_r' :
  ¬ q → p ∧ q ↔ False := by
  sorry

theorem and_idem :
  p ∧ p ↔ p := by
  sorry

theorem and_comm :
  p ∧ q ↔ q ∧ p := by
  sorry

theorem and_assoc :
  p ∧ (q ∧ r) ↔ (p ∧ q) ∧ r := by
  sorry

theorem and_mon_l :
  (p → q) → (r ∧ p → r ∧ q) := by
  sorry

theorem and_mon_r :
  (p → q) → (p ∧ r → q ∧ r) := by
  sorry

theorem and_mon :
  (p → q) → (r → s) → p ∧ r → q ∧ s := by
  sorry

theorem and_and_l :
  (p ∧ q) ∧ r ↔ (p ∧ r) ∧ (q ∧ r) := by
  sorry

theorem and_and_r :
  p ∧ (q ∧ r) ↔ (p ∧ q) ∧ (p ∧ r) := by
  sorry

theorem and_or_l :
  (p ∨ q) ∧ r ↔ (p ∧ r) ∨ (q ∧ r) := by
  sorry

theorem and_or_r :
  p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  sorry

theorem and_or_l_abs :
  (p ∨ q) ∧ q ↔ q := by
  sorry

theorem and_or_r_abs :
  p ∧ (p ∨ q) ↔ p := by
  sorry

theorem and_iff_l :
  ((p ↔ q) ∧ r) → ((p ∧ r) ↔ (q ∧ r)) := by
  sorry

theorem and_iff_r :
  (p ∧ (q ↔ r)) → ((p ∧ q) ↔ (p ∧ r)) := by
  sorry

-- ** Właściwości relacjowe

-- ** pozostałe właściwości

theorem and_not_r :
  p ∧ ¬ q → ¬ (p → q) := by
  sorry

theorem Irrefutable_and_not_r_conv :
  ¬ ¬ (¬ (p → q) → p ∧ ¬ q) := by
  sorry

theorem Irrefutable_and_not_r_conv' :
  ¬ (p → q) ↔ ¬ ¬ (p ∧ ¬ q) := by
  sorry

-- * równoważność

-- ** reguły

theorem iff_intro :
  (p → q) → (q → p) → p ↔ q := by
  sorry

theorem iff_elim_l :
  (p ↔ q) → (p → q) := by
  sorry

theorem iff_elim_r :
  (p ↔ q) → (q → p) := by
  sorry

theorem iff_elim :
  ((p → q) → (q → p) → r) → ((p ↔ q) → r) := by
  sorry

-- ** Właściwości działaniowe

theorem iff_True_l :
  (True ↔ p) ↔ p := by
  sorry

theorem iff_True_r :
  (p ↔ True) ↔ p := by
  sorry

theorem iff_False_l :
  (False ↔ p) ↔ ¬ p := by
  sorry

theorem iff_False_r :
  (p ↔ False) ↔ ¬ p := by
  sorry

theorem iff_True_l' :
  p → (p ↔ q) ↔ q := by
  sorry

theorem iff_True_r' :
  q → (p ↔ q) ↔ p := by
  sorry

theorem iff_False_l' :
  ¬ p → (p ↔ q) ↔ ¬ q := by
  sorry

theorem iff_False_r' :
  ¬ q → (p ↔ q) ↔ ¬ p := by
  sorry

theorem iff_refl :
  (p ↔ p) ↔ True := by
  sorry

theorem iff_comm :
  (p ↔ q) ↔ (q ↔ p) := by
  sorry

theorem Irrefutable_iff_assoc :
  ¬ ¬ ((p ↔ (q ↔ r)) ↔ ((p ↔ q) ↔ r)) := by
  sorry

-- ** Właściwości relacjowe

theorem iff_refl' : p ↔ p := by
  sorry

theorem iff_symm : (p ↔ q) ↔ (q ↔ p) := by
  sorry

theorem iff_trans : (p ↔ q) → (q ↔ r) → (p ↔ r) := by
  sorry

-- ** pozostałe właściwości

theorem Irrefutable_iff_not :
  ¬ ¬ ((¬ p ↔ ¬ q) → (p ↔ q)) := by
  sorry

theorem iff_not_conv :
  (p ↔ q) → (¬ p ↔ ¬ q) := by
  sorry

theorem iff_not :
  (¬ p ↔ ¬ q) ↔ ¬ ¬ (p ↔ q) := by
  sorry

theorem Irrefutable_iff_spec :
  ¬ ¬ ((p ↔ q) → (p ∧ q) ∨ (¬ p ∧ ¬ q)) := by
  sorry

theorem Irrefutable_iff_spec' :
  (p ↔ q) → ¬ ¬ ((p ∧ q) ∨ (¬ p ∧ ¬ q)) := by
  sorry

theorem iff_spec_conv :
  (p ∧ q) ∨ (¬ p ∧ ¬ q) → (p ↔ q) := by
  sorry

-- ** Bardzo nudne właściwości

theorem impl_pres_iff :
  (p ↔ p') → (q ↔ q') → (p → q) ↔ (p' → q') := by
  sorry

theorem or_pres_iff :
  (p ↔ p') → (q ↔ q') → p ∨ q ↔ p' ∨ q' := by
  sorry

theorem and_pres_iff :
  (p ↔ p') → (q ↔ q') → p ∧ q ↔ p' ∧ q' := by
  sorry

theorem iff_pres_iff :
  (p ↔ p') → (q ↔ q') → (p ↔ q) ↔ (p' ↔ q') := by
  sorry

theorem not_pres_iff :
  (p ↔ p') → ¬ p ↔ ¬ p' := by
  sorry

-- * Implikacja

-- ** reguły

theorem impl_intro :
  (p → q) → p → q := by
  sorry

theorem impl_elim :
  p → (p → q) → q := by
  sorry

-- ** Właściwości działaniowe

theorem impl_True_l :
  (True → p) ↔ p := by
  sorry

theorem impl_True_r :
  (p → True) ↔ True := by
  sorry

theorem impl_False_l :
  (False → p) ↔ True := by
  sorry

theorem impl_False_r :
  (p → False) ↔ ¬ p := by
  sorry

theorem impl_True_l' :
  p → (p → q) ↔ q := by
  sorry

theorem impl_True_r' :
  q → (p → q) ↔ True := by
  sorry

theorem impl_False_l' :
  ¬ p → (p → q) ↔ True := by
  sorry

theorem impl_False_r' :
  ¬ q → (p → q) ↔ ¬ p := by
  sorry

theorem impl_refl :
  (p → p) ↔ True := by
  sorry

theorem impl_mon_l :
  (p → q) → ((r → p) → (r → q)) := by
  sorry

theorem impl_antimon_r :
  (p → q) → ((q → r) → (p → r)) := by
  sorry

theorem impl_bimon :
  (p → q) → (r → s) → ((q → r) → (p → s)) := by
  sorry

theorem impl_impl_r :
  (p → (q → r)) ↔ (p → q) → (p → r) := by
  sorry

theorem Irrefutable_impl_or_r :
  ¬ ¬ ((p → q ∨ r) → (p → q) ∨ (p → r)) := by
  sorry

theorem Irrefutable_impl_or_r' :
  (p → q ∨ r) → ¬ ¬ ((p → q) ∨ (p → r)) := by
  sorry

theorem impl_or_r_conv :
  (p → q) ∨ (p → r) → (p → q ∨ r) := by
  sorry

theorem Irrefutable_impl_and_l' :
  ¬ ¬ (((p ∧ q) → r) → (p → r) ∨ (q → r)) := by
  sorry

theorem Irrefutable_impl_and_l'' :
  ((p ∧ q) → r) → ¬ ¬ ((p → r) ∨ (q → r)) := by
  sorry

theorem impl_and_l'_conv :
  (p → r) ∨ (q → r) → ((p ∧ q) → r) := by
  sorry

theorem impl_and_r :
  (p → q ∧ r) ↔ (p → q) ∧ (p → r) := by
  sorry

theorem impl_iff_r :
  (p → (q ↔ r)) → ((p → q) ↔ (p → r)) := by
  sorry

-- ** Właściwości relacjowe

theorem impl_refl' : p → p := by
  sorry

theorem impl_trans : (p → q) → (q → r) → (p → r) := by
  sorry

theorem impl_antisym : (p → q) → (q → p) → (p ↔ q) := by
  sorry

-- ** pozostałe właściwości

theorem weakening :
  p → q → p := by
  sorry

theorem impl_and_l :
  (p ∧ q → r) ↔ (p → q → r) := by
  sorry

theorem impl_or_l :
  (p ∨ q → r) ↔ (p → r) ∧ (q → r) := by
  sorry

theorem contraposition :
  (p → q) → (¬ q → ¬ p) := by
  sorry

theorem Irrefutable_contraposition_conv :
  ¬ ¬ ((¬ q → ¬ p) → (p → q)) := by
  sorry

theorem Irrefutable_contraposition_conv' :
  (¬ q → ¬ p) → ¬ ¬ (p → q) := by
  sorry

theorem impl_not_r :
  (p → ¬ q) → (q → ¬ p) := by
  sorry

theorem Irrefutable_impl_not_l :
  ¬ ¬ ((¬ p → q) → (¬ q → p)) := by
  sorry

theorem Irrefutable_impl_not_l' :
  (¬ p → q) → ¬ ¬ (¬ q → p) := by
  sorry

theorem not_impl_converse :
  ¬ (p → q) → (q → p) := by
  sorry

theorem impl_permute :
  (p → q → r) → (q → p → r) := by
  sorry

-- * Negacja

-- ** reguły

theorem not_intro :
  (p → False) → ¬ p := by
  sorry

theorem not_intro_wiki :
  (p → q) → (p → ¬ q) → ¬ p := by
  sorry

-- Z jakiegoś powodu Wikipedia (i parę innych źródeł) nazywa powyższe prawem
    wprowadzania negacji... nie wiem dlaczego. 

theorem not_elim :
  ¬ p → p → False := by
  sorry

-- ** Negacja stałych i spójników

theorem not_True :
  ¬ True ↔ False := by
  sorry

theorem not_False :
  ¬ False ↔ True := by
  sorry

theorem not_or :
  ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by
  sorry

theorem Irrefutable_not_and :
  ¬ ¬ (¬ (p ∧ q) → ¬ p ∨ ¬ q) := by
  sorry

theorem not_and_conv :
  ¬ p ∨ ¬ q → ¬ (p ∧ q) := by
  sorry

theorem not_and :
  ¬ (p ∧ q) ↔ ¬ ¬ (¬ p ∨ ¬ q) := by
  sorry

theorem Irrefutable_not_impl :
  ¬ ¬ (¬ (p → q) → p ∧ ¬ q) := by
  sorry

theorem not_impl_conv :
  p ∧ ¬ q → ¬ (p → q) := by
  sorry

theorem not_impl :
  ¬ (p → q) ↔ ¬ ¬ (p ∧ ¬ q) := by
  sorry

theorem Irrefutable_not_not :
  ¬ ¬ (¬ ¬ p → p) := by
  sorry

theorem not_not_conv :
  p → ¬ ¬ p := by
  sorry

-- ** podwójna negacja

theorem not_not_True :
  ¬ ¬ True ↔ True := by
  sorry

theorem not_not_False :
  ¬ ¬ False ↔ False := by
  sorry

theorem not_not_impl :
  ¬ ¬ (p → q) ↔ ¬ ¬ p → ¬ ¬ q := by
  sorry

theorem not_not_or :
  ¬ ¬ p ∨ ¬ ¬ q → ¬ ¬ (p ∨ q) := by
  sorry

theorem not_not_and :
  ¬ ¬ (p ∧ q) ↔ ¬ ¬ p ∧ ¬ ¬ q := by
  sorry

-- ** potrójna negacja

theorem not_not_not :
  ¬ ¬ ¬ p ↔ ¬ p := by
  sorry

-- ** pozostałe właściwości

theorem reductio_ad_absurdum' :
  ¬ (p ∧ ¬ q) ↔ ¬ ¬ (p → q) := by
  sorry

-- * pozostałe mało istotne prawa

theorem Irrefutable_exchange :
  ¬ ¬ ((¬ p ∨ q) ∧ (p ∨ r) → (p ∧ q) ∨ (¬ p ∧ r)) := by
  sorry

theorem Irrefutable_exchange' :
  (¬ p ∨ q) ∧ (p ∨ r) → ¬ ¬ ((p ∧ q) ∨ (¬ p ∧ r)) := by
  sorry

theorem exchange_conv :
  (p ∧ q) ∨ (¬ p ∧ r) → (¬ p ∨ q) ∧ (p ∨ r) := by
  sorry

theorem isolation :
  (p ∧ ¬ q) ∨ (p ∧ q) → p := by
  sorry

theorem Irrefutable_isolation_conv :
 ¬ ¬ (p → (p ∧ ¬ q) ∨ (p ∧ q)) := by
  sorry

theorem Irrefutable_isolation_conv' :
  p → ¬ ¬ ((p ∧ ¬ q) ∨ (p ∧ q)) := by
  sorry

theorem dd_and_or_r :
  p ∧ (¬ p ∨ q) ↔ p ∧ q := by
  sorry

-- Uwaga: [dd] to skrót od ang. destructive ditheorem (chyba).

theorem dd_and_impl_r :
  p ∧ (p → q) ↔ p ∧ q := by
  sorry

theorem dd_or_and_r :
  p ∨ (¬ p ∧ q) → p ∨ q := by
  sorry

theorem Irrefutable_dd_or_and_r_conv :
  ¬ ¬ (p ∨ q → p ∨ (¬ p ∧ q)) := by
  sorry

theorem Irrefutable_dd_or_and_r_conv' :
  p ∨ q → ¬ ¬ (p ∨ (¬ p ∧ q)) := by
  sorry

theorem Irrefutable_dd_or_impl_r :
  ¬ ¬ (p ∨ (¬ p → q) → p ∨ q) := by
  sorry

theorem Irrefutable_dd_or_impl_r' :
  p ∨ (¬ p → q) → ¬ ¬ (p ∨ q) := by
  sorry

theorem dd_or_impl_r_conv :
  p ∨ q → p ∨ (¬ p → q) := by
  sorry

theorem dd_impl_or_r :
  p → (¬ p ∨ q) ↔ p → q := by
  sorry

theorem dd_impl_or_l :
  (p ∨ q) → q ↔ p → q := by
  sorry

-- ** Wesołe podwójnie zanegowane prawa

theorem Irrefutable_Godel_Dummet :
  ¬ ¬ ((p → q) ∨ (q → p)) := by
  sorry

theorem Irrefutable_fully_disjunctive_reasoning :
  ¬ ¬ ((p → q) ∨ (q → r)) := by
  sorry