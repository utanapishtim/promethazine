import data.nat data.prod
open nat prod

check eq.refl
check eq.symm
check eq.trans

section
  variables (A : Type) (a b c d : A)
  premises (Hab : a = b) (Hcb : c = b) (Hcd : c = d)

  example : a = d := eq.trans (eq.trans Hab (eq.symm Hcb)) Hcd
end

section
  variables (A : Type) (a b c d : A)
  premises (Hab : a = b) (Hcb : c = b) (Hcd : c = d)

  --BEGIN
  open eq.ops

  example : a = d := Hab ⬝ Hcb⁻¹ ⬝ Hcd
end

section
  variables (A B : Type)

  example (f : A → B) (a : A) : (λ x, f x) a = f a := rfl
  example (a : A) (b : A) : pr1 (a, b) = a := rfl
  example : 2 + 3 = (5 : ℕ) := rfl
end

-- equality is more than equivalence relation, it has the property that every
-- assertion respects the equivalence in that we can substitude equal expressions
-- with no effect on truth value

section
  example (A : Type) (a b : A) (P : A → Prop) (H1 : a = b) (H2 : P a) : P b :=
  eq.subst H1 H2
end

section
  open eq.ops

  example (A : Type) (a b : A) (P : A → Prop) (H1 : a = b) (H2 : P a) : P b :=
  H1 ▸ H2
end

open nat eq.ops algebra

-- '!'s infer explicit arguments to a theorem from the context
example (x y : ℕ ) : (x + y) * (x + y) = x * x + y * x + y * y :=
have H1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y, from !left_distrib,
have H2 : (x + y) * (x + y) = x * x + (x * y + y * y),
  from (right_distrib x y x ▸ !right_distrib ▸ H1, !add.assoc⁻¹ ▸ H2

section
  variables (a b c d e : ℕ )
  
  variable H1 : a = b
  variable H2 : b = c + 1
  variable H3 : c = d
  variable H4 : e = 1 + d

  theorem T : a = e :=
  calc
    a   = b     : H1
    ... = c + 1 : H2
    ... = d + 1 : {H3}
    ... = 1 + d : add.comm d 1
    ... = e     : eq.symm H4
end

section
  theorem T2 (a b c : nat) (H1 : a = b) (H2 : b = c + 1) : a ≠ 0 :=
  calc
    a   = b      : H1
    ... = c + 1  : H2
    ... = succ c : add_one c
    ... ≠ 0      : succ_ne_zero c
end

section
  example (x y : ℕ ) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y       : left_distrib
    ...               = x * x + y * x + (x + y) * y     : right_distrib
    ...               = x * x + y * x + (x * y + y * y) : right_distrib
    ...               = x * x + y * x + x * y + y * y   : add.assoc
end

