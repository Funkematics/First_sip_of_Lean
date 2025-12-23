open Classical


theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

--Declaring objects and checking types
def m : Nat := 1
#check m
def b1 : Bool := true
#check b1
def b2 : Bool := false
#check b2
#check Nat → Nat → Nat
#check Nat.succ 2
#check Nat.add 3

--Create new types
def α : Type := Nat
def β : Type := Bool
#check Prod α β
#check α × β 

variable {p : Prop}
variable {q : Prop}

-- Should make nested functions explicit like thsi
theorem t1 : p → q → p :=
  fun hp : p =>
    fun hq : q =>
  show p from hp

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
    Iff.intro
      (fun h : p ∧ q => 
        show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p => 
        show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
        (fun hp : p =>
          show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
          show q ∨ p from Or.intro_left p hq))
    (fun h : q ∨ p =>
      Or.elim h
        (fun hq : q =>
          show p ∨ q from Or.intro_right p hq)
        (fun hp : p =>
          show p ∨ q from Or.intro_left q hp))


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

