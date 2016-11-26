open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨ 
example : p ∧ q ↔ q ∧ p := _
example : p ∨ q ↔ q ∨ p := _

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := _
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := _


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := _
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := _

-- other properties
example : (p → (p →  r)) ↔ (p ∧ q → r) := _
example : ((p ∨ q) →  r) ↔ (p →  r) ∧ (q →  r) := _
example : ¬(p ∨ q) ↔  ¬p ∧ ¬q := _
example : ¬p ∨ ¬q →  ¬(p ∧ q) := _
example : ¬(p ∧ ¬p) := _
example : p ∧ ¬q →  ¬(p → q) := _
example : ¬p → (p →  q) := _
example : (¬p ∨ q) → (p → q) := _
example : p ∨ false ↔  p := _
example : p ∧ false ↔  false := _
example : ¬(p ↔  ¬p) := _
example : (p → q) → (¬q →  ¬p) := _

--these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := _
example : ¬(p ∧ q) → ¬p ∨ ¬q := _
example : ¬(p → q) → p ∧ ¬q := _
example : (p → q) → (¬p ∨ q) := _
example : (¬q → ¬p) → (p → q) := _
example : p ∨ ¬p := _
example : (((p → q) → p) → p) := _
