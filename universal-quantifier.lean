/-
  if A is some type, then a unary predicate p on A can be represented as an object
  of type A →  Prop. In that case, given x : A, 'p x' dentoes the assertion that p
  holds of x.

  In a similar manner, an object r : A → A → Prop denotes a binary relation A.
  Then, if x y : A, 'r x y' denotes the assertion that x is related to y.

  '∀ x : A, p x' asserts that 'for every x : A, p x holds'

  ∀ INTRODUCTION: 

  Given a proof p x, in a context where x : A is arbitrary we have a proof 
  ∀ x : A, p x.

  ∀ ELIMINATION:

  Given a proof ∀ x : A, p x and any term t : A, we have a proof p t

  Π INTRODUCTION
  
  Given a term t of type B x, in a context where x : A is arbitrary we have
  (λ x : A, t) : Π x : A, B x

  Π ELIMINATION:
  
  Given a term s : Π x : A, B x and any term t : A, we have s t : B t

  In ther case where p x has type Prop, if we replace Π x : A, B x with
  ∀ x : A, p x we can read these as the correct rules for building proofs
  involving the universal quantifier.
-/
section
  variables (A : Type) (p q : A → Prop)

  example : (∀ x : A, p x ∧ q x) →  ∀ y : A, p y :=
  assume H : ∀ x : A, p x ∧ q x,
  take y : A,
  show p y, from and.elim_left (H y)
end

section
  variables (A : Type) (r : A → A → Prop)
  variable trans_r : ∀ x y z, r x y →  r y z →  r x z
  
  variables (a b c : A)
  variables (Hab : r a b) (Hbc : r b c)

  check trans_r
  check trans_r a b c
  check trans_r a b c Hab
  check trans_r a b c Hab Hbc
end

section
  variables (A : Type) (r : A →  A →  Prop)
  variable trans_r : ∀ {x y z}, r x y →  r y z →  r x z
  
  variables (a b c : A)
  variables (Hab : r a b) (Hbc : r b c)

  check trans_r
  check trans_r Hab
  check trans_r Hab Hbc
end

section
  variables (A : Type) (r : A →  A →  Prop)

  variable refl_r : ∀ x, r x x
  variable symm_r : ∀ {x y}, r x y →  r y x
  variable trans_r : ∀ {x y z}, r x y →  r y z →  r x z

  example (a b c d : A) (Hab : r a b) (Hcb : r c b) (Hcd : r c d) : rad :=
  trans_r (trans_r Hab (symm_r Hcb)) Hcd
end

-- prove the following
section
  variables (A : Type) (p q : A →  Prop)
  
  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x ) ∧ (∀ x, q x) := _
  example : (∀ x, p x →  q x) →  (∀ x, p x) →  (∀ x, q x) := _
  example : (∀ x, p x) ∨ (∀ x, q x) →  ∀ x, p x ∨ q x := _
end

section
  variables (A : Type) (p q : A →  Prop)
  variable r : Prop

  example : A →  ((∀ x : A, r) ↔ r) := _
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := _
  example : (∀ x, r →  p x) ↔ (r →  ∀ x, p x) := _
end

section
  variables (men : Type) (barber : men) (shaves: men →  men →  Prop)

  example (H : ∀ x : men, shaves barder x ↔  ¬shaves x x) : false := _
end

-- Prop is the type of proposition not data, and this makes Prop impredicative
-- i.e. any type B that depends on var x : A, and B is type Prop then Π x : A, B
-- is of type Prop as well, regardless of what universe A lives in.

-- Prop is its own type!!?? Huh???
