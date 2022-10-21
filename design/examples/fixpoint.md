# Example: Fixpoint

```
ℕ = μ n ⇒ { Zero#{,} | Suc#n }
Zero = Zero#{,}
```

The fixpoint of `add` is.
```
                Zero → n →                 n
            Suc#Zero → n →             Suc#n
        Suc#Suc#Zero → n →         Suc#Suc#n
    Suc#Suc#Suc#Zero → n →     Suc#Suc#Suc#n
Suc#Suc#Suc#Suc#Zero → n → Suc#Suc#Suc#Suc#n
     Suc#...Suc#Zero → n →      Suc#...Suc#n
```
The type that specifies this fixpoint is
```
Add = μ add ⇒ { Π Zero n ⇒ n | Π Suc#m n ⇒ n }
```

TODO: do i really need to add `Π` to achieve this?