open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
  (fun h : p → q ∨ r =>
    Or.elim (em q)                        --Use LEM for cases q and ¬q 
      (fun hq : q =>
        Or.inl (fun hp => hq))
      (fun hnq : ¬q =>
        Or.inr (fun hp : p =>
          Or.elim (h hp)
           (fun hq => absurd hq hnq)
           (fun hr => hr))))

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  (fun hpq : ¬(p ∧ q) => 
    Or.elim (em p)
    (fun hp : p =>
      Or.inr (fun hq : q =>
        show False from hpq (And.intro hp hq)))
    (fun hnp : ¬p =>
      Or.inl hnp))

#check Or.inr
#check Or.intro_right

-- Suppose it is not the case that if p then q
example : ¬(p → q) → p ∧ ¬q := 
  (fun h : ¬(p → q) => 
    Or.elim (em p)    
     (fun hp : p =>                           --Case 1 : Suppose p
        show p ∧ ¬q from And.intro hp 
                          (fun hq : q =>
                           show False from h (fun ptq : p => hq)))
    (fun hnp : ¬p =>                            --Case 2 : Suppose ¬p 
      have hpq : p → q := fun hp => absurd hp hnp
      have hfalse : False := h hpq
      show p ∧ ¬ q from False.elim hfalse))

                                        -- Need to show that p is true and not q holds.
example : (p → q) → (¬p ∨ q) := 
  (fun h : p → q :=
    Or.elim (em p)
      (fun hp : p => _))

example : (¬q → ¬p) → (p → q) := sorry

example : p ∨ ¬p := em p                  --Law of excluded middle

example : (((p → q) → p) → p) := sorry

