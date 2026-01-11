
--For all statement example
section Testscope
  example (α : Type) (p q : α → Prop) : 
      (∀ x : α, p x ∧ q x) → ∀ y : α, p y := 
      fun h : ∀ x : α, p x ∧ q x =>
        fun y : α =>
          show p y from (h y).left

  --We can change up and reuse names for conclusions
  example (α : Type) (p q : α → Prop) :
      (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
        fun h : ∀ x : α, p x ∧ q x =>
          fun z : α =>
            show p z from And.left (h z)

  --showing that a relation, r is transitive:

  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ x y z, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  --a b c are type alpha
  #check trans_r a b c hab hbc


  --Alternative with inferred arguments rather than explicity
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r hab hbc
end Testscope 

--equivalence relations

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

-- First one is from book, the rest are just me playing around
example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d): r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd




  --Exercises
  variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry


variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  sorry

def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

