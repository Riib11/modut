# Modut

## Syntax

- The notation `*[...]` indicates that the contained phrase can be repeated any number of
  times (including 0 times).
- The notation `+[...]` indicates that the contained phrase can be repeated any
  non-zero number of times.  
- The notation `?[...]` indicates that the contained phrase is optional.
```
<ty1> ::= ?[forall *[<ty-var>] =>] <ty>

<ty> ::=
  #<lbl>?[(<ty>)]  |
  <ty-var>  |
  {*[<ty> ,]}  |
  {*[<ty> |]}  |
  <ty> -> <ty>  |
  fix <ty-var> in <ty>

<tm> ::=
  #<lbl>?[(<tm>)]  |
  <tm-var>  |
  {*[<tm> ,]}  |  <tm>?[.#<lbl>]  |
  <tm>?[: <ty>]  |  match <tm> with {*[<pat> => <tm> |]}  |
  fun (<tm-var> : <ty>) => <tm> | <tm> <tm>

<pat> ::=
  <tm-var>  |
  #<lbl>?[(<ty>)]  |
  {*[<pat> ,]}  |
  {*[<pat> |]}  |

<lbl> ::= <constructor-name>
<ty-var> ::= <type-variable-name>
<tm-var> ::= <term-var-name>
```

Special features:
- Projection from conjunctions is optional since uniquely-named conjuncts can be
  distinguished.
- Injection into disjunctions is options since this is checked by (sub-)typing.
- Polymorphism is implicit
- Patterns can only inspect labels and conjunctions/disjunctions.

```
Option = forall a => #None | #Some(a)
Nat = fix n in #Zero | #Suc(n)

pred : Nat -> Option Nat
pred n = match n with
  { #Z => #None
  | #Suc(n) => #Some(n) }
pred : 
  { #Z -> #None
  | #Suc(Nat) -> #Some(Nat) }

```

## Typing


Subtype under constructor
```
Gamma |- A < A'
------------------------------------
Gamma |- #con(A) < #con(A')
```

Subtype under under arrow
```
Gamma |- A < A'
Gamma |- B' < B
---------------------------------
Gamma |- A -> B < A' -> B'
```

Subtype under conjunction
