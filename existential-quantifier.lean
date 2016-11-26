/-
  1. exists x : A, p x
  2. ∃ x : A, p x
  3. Exists (λ x : A, p x)

  (1-3) are all equivalent.
-/

import data.nat
open nat algebra

example : ∃ x : ℕ , x > 0 :=
have H : 1 > 0, from succ_pos 0,
exists.intro 1 H

example (x : ℕ ) (H : x > 0) : ∃ y, y < x :=
exists.intro 0 H

example (x y z : ℕ ) (Hxy : x < y) (Hyz : y < z) : ∃ w, x < w ∧ w < z :=
exists.intro y (and.intro Hxy Hyz)

check @exists.intro

section
  variable g : ℕ → ℕ → ℕ 
  variable Hg : g 0 0 = 0

  theorem gex1 : ∃ x, g x x = x := exists.intro 0 Hg
  theorem gex2 : ∃ x, g x 0 = x := exists.intro 0 Hg
  theorem gex3 : ∃ x, g 0 0 = x := exists.intro 0 Hg
  theorem gex4 : ∃ x, g x x = 0 := exists.intro 0 Hg

  set_option pp.implicit true -- display implict args
  check gex1
  check gex2
  check gex3
  check gex4
end

section
  definition is_even (a : nat) := ∃ b, a = 2 * b

  theorem even_plus_even {a b : nat} (H1 : is_even a) (H2 : is_even b) : is_even (a + b) :=
  exists.elim H1 (λ (w1 : nat) (Hw1 : a = 2 * w1),
  exists.elim H2 (λ (w2 : nat) (Hw2 : b = 2 * w2),
    exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + b      : Hw1
        ...   = 2 * w1 + 2 * w2 : Hw2
        ...   = 2 * (w1 + w2)   : left_distrib)))
end


section
  definition is_even (a : ℕ ) := ∃ b, a = 2 * b
  theorem even_plus_even {a b : ℕ } (H1 : is_even a) (H2 : is_even b) :
    is_even (a + b) :=
      obtain (w1 : ℕ ) (Hw1 : a = 2 * w1), from H1,
      obtain (w2 : ℕ ) (Hw2 : b = 2 * w2), from H2,
      exists.intro (w1 + w2)
        (calc
          a + b = 2 * w1 + b      : Hw1
          ...   = 2 * w1 + 2 * w2 : Hw2
          ...   = 2 * (w1 + w2)   : left_distrib
end

open classical

section
  variables (A : Type) (p : A →  Prop)

  example (H : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  by_contradiction
    (assume H1 : ¬ ∃ x, p x,
      have H2 : ∀ x, ¬ p x, from
        take x,
        assume H3 : p x,
        have H4 : ∃ x, p x, from exists.intro x H3,
        show false, from H1 H4,
    show false, from H H2)
end
