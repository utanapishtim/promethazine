constants A B C : Type
constant f : A →  B
constant g : B →  C
--constant b : B

check λ x : A, x         -- identity fn on A
check λ x : A, b         -- constant fn on A
check λ x : A, g (f x)   -- composition of g and f
check λ x, g (f x)       -- lean infers type of x

check λ b : B, λ x : A, x
check λ (b : B) (x : A), x
check λ (g : B → C) (f : A → B) (x: A), g (f x)

check λ (A B : Type) (b : B) (x : A), x
check λ (A B C : Type) (g : B → C) (f : A → B) (x : A), g (f x)

constant h : A → A
constants (a : A) (b : B)

check (λ x : A, x) a
check (λ x : A, b) a
check (λ x : A, b) (h a)
check (λ x : A, g (f x)) (h (h a))

check (λ v u x, v (u x)) g f a

check (λ (Q R S : Type) (v : R → S) (u : Q → R) (x : Q),
  v (u x)) A B C g f a
