# Example: Sort

Goals:
- define type of sorted lists
- prove that function sorts a list

Booleans.
```ml
let 𝔹 = { True#{,} | False#{,} }
```

Natural numbers.
```ml
let ℕ = μ n ⇒ { Zero#{,} | Suc#n }

let leq = λ
  { Zero#{,} ⇒ λ (_ : Nat) ⇒ True#{,}
  , Suc#(n : Nat) ⇒ λ
    { Zero#{,} ⇒ False#{,}
    , Suc#(m : Nat) ⇒ leq m n
    }
  }
(* TODO: interesting inferred fixpoint *)
let leq : 
  μ leq ⇒
  { Zero#{,} → Nat → True#{,}
  , Suc#Nat → 
    { Zero#{,} → False#{,}
    | Suc#Nat → leq } }
let leq : 
  μ leq ⇒
  { Zero#{,} → Nat → True#{,}
  , Suc#Nat → Zero#{,} → False#{,} 
  , Suc#Nat → Suc#Nat → leq }
```

List.
```ml
let List = ∀ a ⇒ μ l ⇒ { Nil#{,} | Cons#{ Head#a , Tail#l } }
```

```
let SortedListℕ = μ l ⇒ { Nil#{,} | Cons#{ Head#_ , Tail#l } }
```

