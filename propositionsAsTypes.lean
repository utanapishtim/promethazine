constant and : Prop → Prop → Prop
constant or : Prop → Prop → Prop
constant not : Prop → Prop → Prop
constant implies : Prop → Prop → Prop

variables p q r : Prop
check and p q
check or (and p q) r
check implies (and p q) (and q p)
check p ∧ q
check r ∨ (p ∧ q)
check (p ∧ q) → (q ∧ p)

constant Proof : Prop → Type

constant and_commutative : Π p q : Prop, Proof (implies (and p q) (and q p))

variables p q : Prop
check and_commutative p q

constant modus_ponens (p q : Prop) : Proof (implies p q) → Proof p → Proof q
constant implies_intro (p q : Prop) : (Proof p → Proof q) → Proof (implies p q)
/-
  simplifications
  1. conflate Proof p with p. For any p : Prop we can interpret p as the type
     of its proofs; t : p then means t is a proof of p.
  2. dependent type theory function constructor is equivalent to implication

  this all follows from the fact that the rules of implication in a proof 
  system for natural deduction correspond EXACTLY to the rules governing
  abstraction and application for functions

  thanks, curry-howard!

  propositions as types, lean tutorial p. 34 has interesting ideas around what
  this means exactly --> constructivist vs. realist view

  constructive:
  a proof of p is a mathematical object, a specification of the type of data that   constitutes a proof.

  other:
  a propoisiton is associated a type, which if empty indicates the proposition is
  false, while if true has a single element. In the latter case, we say that the
  type is INHABITED and function application and abstraction help us track which
  types are inhabited and which aren't. The inhabitant of a type p is "the fact 
  that p is true"
  
  note, on this view if (t1 t2 : p) then t1 and t2 are definitionally equal, they
  carry no more information than "it is the case p is true". This is known as
  proof irrelevance.

  in this view, expression themselves are the proofs

  In summary, to EXPRESS a mathematical assertion in the language of dependent
  type theory we need to exhibit a term p : Prop, and to PROVE that assertion we
  need to exhibit a term t : p. Lean's task is to help us construct t, and verify
  it is well-formed and of the correct type.
-/

constants p q : Prop

-- constant function
theorem t1 : p → q → p := λ Hp : p, λ Hq : q, Hp
-- note above, lambda abstractions can be viewed as temporary assumptions
check t1
reveal t1
print t1

-- 'assume' replaces above lambda abstractions
theorem t2 : p → q → p :=
assume Hp : p,
assume Hq : q,
Hp

check t2

-- we can also specify the type of the final term with 'show'
theorem t3 : p → q → p :=
assume Hp : p,
assume Hq : q,
show p, from Hp

-- we can also use the syntax 'lemma' and 'corollary' instead of 'theorem'
lemma t4 : p → q → p :=
assume Hp : p,
assume Hq : q,
show p, from Hp

check t4

-- we can also move the lambda abstracted variables to the left of the colon
corollary t5 (Hp : p) (Hq : q) : p := Hp

check t5

-- we can apply theorems just as a function application
axiom Hp : p -- 'axiom' is alternative syntax for constant
theorem t6 : q → p := t5 Hp

-- Hp : p is essentially declaring the truth of p, as aduced by Hp

-- notice, applying t5 to the fact Hp : p, yields q → p by modus ponens!!!

-- we can formulate our original theorem to range over all types p, q
theorem t5' (p q : Prop) (Hp : p) (Hq : q) : p := Hp
check t5'

-- '∀' is equivalent to 'Π', Pi types allow us to model universal
--  quantifiers more generally.

variables a b c d : Prop

check t5' a b
check t5' c d
check t5' (a → b) (b → a)

variable H : a → b
check t5' (a → b) (b → c) H

-- in the above formulation, the variable H of type r → s can be viewed
-- as the hypothesis or premise that r → s holds. We can write this as:

premise P : a → b
check t5' (a → b) (b → a) P

variables h i j k : Prop
theorem t7 (H1 : i → j) (H2 : h → i) : h → j :=
assume H3 : h,
show j, from H1 (H2 H3)

premises (H1 : i → j) (H2 : h → i)
theorem t7' : h → j :=
assume H3 : p,
show r, from H1 (H2 H3)
