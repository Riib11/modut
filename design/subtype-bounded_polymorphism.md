# Subtype-bounded Polymorphism

Consider the type of `add`, which is the following least fixpoint.
```ml
                    Zero{,} → n →                     n
               Succ#Zero{,} → n →                Succ#n
          Succ#Succ#Zero{,} → n →           Succ#Succ#n
     Succ#Succ#Succ#Zero{,} → n →      Succ#Succ#Succ#n
Succ#Succ#Succ#Succ#Zero{,} → n → Succ#Succ#Succ#Succ#n
=
Succ#...Succ#Zero → n → Succ#...Succ#n
```
How can this be written at a Modut type? The tricky aspect is that the first
argument is changing on each unfolding of the fixpoint.

Try something like this:
```
μ (Aux : Type → Type → Type) ↦ 
  { ∀ (M <: Zero#{,}) (N <: ℕ) ↦ N → N → N
  , ∀ (M <: Succ#ℕ)   (N <: ℕ) ↦ M → N → Succ#(aux M.Succ N) }
```
Note that the `∀`'s now have a subtype constraint on them. This ensures that the
only types that can instantiate the type variable bound by the `∀` is a subtype
of the given constraint.

Altogether
```ml
add :
    μ (Aux : Type → Type → Type) ↦ 
    { ∀ (M <: Zero#{,}) (N <: ℕ) ↦ N → N → N
    , ∀ (M <: Succ#ℕ)   (N <: ℕ) ↦ M → N → Succ#(aux M.Succ N) }
  >:
    ℕ → ℕ
add = 
    μ (aux : ...) ↦ 
    { Λ (M <: Zero#{,}) (N <: ℕ) ↦ λ (m : M) (n : N) ↦ n
    , Λ (M <: Succ#ℕ)   (N <: ℕ) ↦ λ (m : M) (n : N) ↦ Succ#(aux m n) }
```