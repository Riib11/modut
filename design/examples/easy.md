# Example: Easy

Except
```ml
let Result = ∀ a ⇒ { a | Exception#String }

val map_result : 
    ∀ a b ⇒ 
    (a → b) → 
    { Exception#String → Exception#String
    , a                → b }
  >:
    ∀ a b ⇒ (a → b) → Result a → Result b
let map_result = λ f 
  { Exception#msg ⇒ Exception#msg
  , a ⇒ f a }
```

Option
```ml
let Option = ∀ a ⇒ { None#{,} | Some#a } 
```

Partial
```ml
let Partial = ∀ a ⇒ { a | Undefined#{,} }
```

Natural numbers
```ml
let ℕ = μ n ⇒ { Zero#{,} | Suc#n }

val add :
  0 -> Nat -> Nat |
  1 -> Nat -> Suc Nat |
  2 -> Nat -> Suc (Suc Nat) |
  ...

val add :
    μ add ⇒
    { Zero#{,} → ℕ → ℕ
    , Suc#ℕ → ℕ → Suc#(add@ℕ@ℕ) }
  >:
    { Zero#{,} → ℕ → ℕ
    , Suc#ℕ → ℕ → Suc#ℕ } (* since { ℕ | Suc#ℕ } ⇓ ℕ *)
  >:
    Nat → Nat
let add = λ
  { Zero#{,} ⇒ λ (n : ℕ) ⇒ n
  , Suc#(m : ℕ) ⇒ Suc#(add m n) }
```

List
```ml
let List = ∀ a ⇒ μ l ⇒ { Nil#{,} | Cons#{ Head#a , Tail#l } }

(* partially defined on subtype of List *)
val head : 
    ∀ a ⇒ Cons#{ Head#a } → a
  >:
    ∀ a ⇒ Cons#{ Head#a , Tail#(List a) } → a
let head = λ{ Cons#{ Head#h } ⇒ h }

(* defined on List by tagging bad inputs with None *)
let head_option : 
    ∀ a ⇒ 
    { Nil#{,} ⇒ None#{,} 
    , Cons#{ Head#a , Tail#(List a) } ⇒ Some#a }
  >:
    ∀ a ⇒ List a → Option a
val head_option = λ
  { Nil#{,} ⇒ None#{,} 
  , Cons#{ Head#a , Tail#_ } ⇒ Some#a }

let head_partial :
    ∀ a ⇒
    { Nil#{,} ⇒ Undefined#{,}
    , Cons#{ Head#a , Tail#(List a) } ⇒ a }
  >:
    ∀ a ⇒ List a → Partial (List a)
let head_partial = λ
  { Nil#{,} ⇒ Undefined#{,}
  , Cons#{ Head#a , Tail#_ } ⇒ a }
```


