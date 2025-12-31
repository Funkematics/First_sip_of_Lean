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

--This one is not part of the problem set
example (C O : Pr
op)(h : C ∨ O) : O ∨ C := by
  exact Or.elim h
    (fun c => Or.inr c)
    (fun o => Or.inl o)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
    (fun h : (p ∧ q) ∧ r => 
      have hp : p ∧ q := And.left h
      have hpp : p := And.left hp
      have hpq : q := And.right hp
      have hr : r := And.right h
      show p ∧ (q ∧ r) from And.intro hpp (And.intro hpq hr))
    (fun h : p ∧ (q ∧ r) => 
      have hqr : q ∧ r := And.right h
      have hpq : q := And.left hqr
      have hpr : r := And.right hqr
      have hp : p := And.left h 
      show (p ∧ q) ∧ r from And.intro (And.intro hp hpq) hpr)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h : (p ∨ q) ∨ r => 
      Or.elim h                                       --split into 2 cases
        (fun hpq : (p ∨ q) => 
          Or.elim hpq                                 --further split into 2 cases
            (fun hp : p =>                            --case p
              show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp )
            (fun hq : q =>                            --case q
              show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_left r hq ) ))
        (fun hr : r =>                                --case r
          show p ∨ (q ∨ r) from Or.intro_right p (Or.intro_right q hr)))
    (fun h: p ∨ (q ∨ r) =>                            -- Backwards direction of proof
      Or.elim h 
        (fun hp : p =>                                --Need to remember order when using Or elimination
          show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_left q hp))
        (fun hqr : (q ∨ r) => 
          Or.elim hqr                                 -- We just split q v r, p hypothesis is separate sub-proof
            (fun hq : q => 
              show (p ∨ q) ∨ r from Or.intro_left r (Or.intro_right p hq)) 
            (fun hr : r => 
              show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr )))
      

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := And.left h
      have hqr : (q ∨ r) := And.right h
      Or.elim hqr
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) (And.intro hp hq))
        (fun hr : r => 
          show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) (And.intro hp hr)))
    (fun h : (p ∧ q) ∨ (p ∧ r) => 
      Or.elim h
      sorry


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

