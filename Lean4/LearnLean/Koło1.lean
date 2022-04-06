section ListFacts
variable (l r xs ys zs : List a)

def length : List a -> Nat
  | [] => 0
  | x :: xs => length xs + 1

def append : List a -> List a -> List a
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

def reverse : List a -> List a
  | [] => []
  | x :: xs => append (reverse xs) [x]

def reverseAppend : List a -> List a -> List a
  | [], ys => ys
  | x :: xs, ys => reverseAppend xs (x :: ys)

def reverseTR (xs : List a) : List a :=
  reverseAppend xs []

theorem length_append : length (append l r) = length l + length r := by
  induction l
  case nil => simp [append, length]
  case cons hd tl ih =>
    simp [append, length, Nat.succ_add]
    apply ih

theorem append_nil : append xs [] = xs := by
  induction xs <;> simp [append, *]

theorem append_assoc
  : append (append xs ys) zs = append xs (append ys zs) := by
  induction xs <;> simp [append, *]

theorem reverse_append
  : reverse (append l r) = append (reverse r) (reverse l) := by
  induction l with
  | nil => simp [append, reverse, append_nil]
  | cons hd tl ih => simp [append, reverse, *, append_assoc]

@[simp]
theorem reverse_reverse : reverse (reverse l) = l := by
  induction l
  case nil => rfl
  case cons hd tl ih =>
    conv =>
      lhs
      arg 1
      simp [reverse]
    simp [reverse_append, append, *]

theorem reverseAppend_spec :
  ∀ xs ys : List a, reverseAppend xs ys = append (reverse xs) ys := by
  intro xs
  induction xs
  case nil =>
    simp [append, reverseAppend]
  case cons hd tl ih =>
    intro ys
    simp [reverse, reverseAppend, ih]
    rw [append_assoc]
    simp [append]

theorem reverseTR_wd : reverseTR = reverse (a := a) := by
  funext xs
  unfold reverseTR
  rw [reverseAppend_spec, append_nil]

end ListFacts