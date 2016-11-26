-- tedious
definition compose (A B C : Type) (g : B → C) (f : A → B) (x : A) : C := g (f x)

definition do_twice (A : Type) (h : A → A) (x : A) : A := h (h x)

definition do_thrice (A : Type) (h : A → A) (x : A) : A := h (h (h x))

-- global looking defs, but scoped locally
variables (A B C : Type)
variables (g : B → C) (f : A → B) (h : A → A)
variable x : A

definition compose := g (f x)
definition do_twice := h (h x)
definition do_thrice := h (h (h x))


-- constant/s create permanent, global entities
-- variable/s insert bound variables in definitions that refer to them
-- sections limit the scope of a variable

section useful
  variables (A B C : Type)
  variables (g : B → C) (f : A → B) (h : A → A)
  variable x : A

  definition compose := g (f x)
  definition do_twice := h (h x)
  definition do_thrice := h (h (h x))
end useful

-- when the section is closed the vars go out of scope
