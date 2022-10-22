# Subtype Constraints

Since tags are not typed, you can use a tag on any type you want. There is no
checking such as is involved in Haskell's `DataKinds` extension.

But, perhaps something like this is necessary. For example, the type of `add` is
the least fixpoint
```ml
                    Zero{,} → n →                     n
               Succ#Zero{,} → n →                Succ#n
          Succ#Succ#Zero{,} → n →           Succ#Succ#n
     Succ#Succ#Succ#Zero{,} → n →      Succ#Succ#Succ#n
Succ#Succ#Succ#Succ#Zero{,} → n → Succ#Succ#Succ#Succ#n
=
Succ#...Succ#Zero → n → Succ#...Succ#n
```
The reason this is tricky is because the fixpoint changes the type of the first 
argument on each unfolding. In order to write this as a type, we need something like
```ml
μ aux ↦
  { Zero#(_ <: {,}) → (n <: ℕ) → n 
  | Succ#(m <: ℕ)   → (n <: ℕ) → Succ#(aux m n) }
```
But this doesn't quite work, because `aux` is just a type, not a type family
indexed by the arguments types of `add`. To make it work, try this.
```
μ aux ↦ ∀ m n ↦
  { (m : m <: Zero#{,}) → (n : n <: ℕ) → n
  | (m : m <: Succ#ℕ)   → (n : n <: ℕ) → Succ#(aux m.Suc n) }
```
This uses a new feature, a **subtype constraint**, which is written in place of
a normal type and has the form `<typ> : <typ> <: <typ>`. The expectation is that
there will be some type variables involved. The constraint requires that the
subtyoing `<typ> <: <typ>` holds, and the type it results in is the type on the
LHS of the `:`: