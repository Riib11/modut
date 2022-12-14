# Example: Sort

Goals:
- define type of sorted lists
- prove that function sorts a list

Booleans.
```ml
let πΉ = { True#{,} | False#{,} }
```

Natural numbers.
```ml
let β = ΞΌ n β { Zero#{,} | Suc#n }

let leq = Ξ»
  { Zero#{,} β Ξ» (_ : Nat) β True#{,}
  , Suc#(n : Nat) β Ξ»
    { Zero#{,} β False#{,}
    , Suc#(m : Nat) β leq m n
    }
  }
(* TODO: interesting inferred fixpoint *)
let leq : 
  ΞΌ leq β
  { Zero#{,} β Nat β True#{,}
  , Suc#Nat β 
    { Zero#{,} β False#{,}
    | Suc#Nat β leq } }
let leq : 
  ΞΌ leq β
  { Zero#{,} β Nat β True#{,}
  , Suc#Nat β Zero#{,} β False#{,} 
  , Suc#Nat β Suc#Nat β leq }
```

List.
```ml
let List = β a β ΞΌ l β { Nil#{,} | Cons#{ Head#a , Tail#l } }
```

```
let SortedListβ = ΞΌ l β { Nil#{,} | Cons#{ Head#_ , Tail#l } }
```

