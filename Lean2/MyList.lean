def last {A : Type} : list A → option A
| [] := none
| [x] := some x
| (h :: t) := last t

eval last (_ :: [1, _, 3] ++ [42])

def len {A : Type} : list A → nat
| [] := 0
| (_ :: t) := nat.succ (len t)

theorem len_app : ∀ (A : Type) (l1 l2 : list A),
    len (l1 ++ l2) = len l1 + len l2 :=
begin
    intros A l1, induction l1 with h t IHl1,
        intros, unfold len, simp,
        intro, rw list.cons_append, unfold len,
            rw IHl1, rw nat.succ_add
end

theorem last_cons : ∀ (A : Type) (h : A) (t : list A),
    t ≠ [] → last (h :: t) = last t :=
begin
    intros, induction t with x xs H,
        contradiction,
        unfold last, trivial
end

theorem last_app : ∀ (A : Type) (l : list A) (x : A),
    last (l ++ [x]) = some x :=
begin
    intros A l, induction l with h t IH; intro x,
        simp, unfold last, trivial,
        simp, unfold last, destruct (t ++ [x]),
            intro x, destruct t; intro H,
                rw H, simp, unfold last, trivial,
                intros, rw a_1 at x, contradiction,
            intros, rw a_2, unfold last, rw -a_2,
                apply IH
end

