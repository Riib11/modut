# Modut

## Syntax

- The notation `*[...]` indicates that the contained phrase can be repeated any number of
  times (including 0 times).
- The notation `+[...]` indicates that the contained phrase can be repeated any
  non-zero number of times.  
- The notation `?[...]` indicates that the contained phrase is optional.
```
<kd> ::= * | * -> <kd>

<ty1> ::= ∀ *[<ty-var>] ⇒ <ty>

<ty> ::=
  | <ty-var>
  | <tag> <ty>
  | {*[<ty> ,]}
  | {*[<ty> |]}
  | <ty> → <ty>
  | μ <ty-var> ⇒ <ty>
  | <ty-var> <ty>

<tm> ::=
  | <tm-var>
  | <tag> <tm>
  | {*[ <tm> , ]} 
  | λ{ *[ <pat> ⇒ <tm> | ] } 
  | <tm> <tm>
  | let <tm-var> : <ty> = <tm> in <tm>
  | let type <ty-var> : <kd> = <ty> in <tm>

<pat> ::=
  | <tm-var> : <ty>
  | <tag> <pat>
  | {*[ <pat> , ]}

<tag> ::= #<tag-name>
<ty-var> ::= <type-variable-name>
<tm-var> ::= <term-var-name>
```

Special features:
- Projection from conjunctions is optional since uniquely-named conjuncts can be
  distinguished.
- Injection into disjunctions is options since this is checked by (sub-)typing.
- Polymorphism is implicit
- Patterns can only inspect labels and conjunctions/disjunctions.

```text
let type Option = ∀ a ⇒ { #None {,} | #Some a }
let type Nat = μ n ⇒ { #Zero {,} | #Suc n }

let pred : Nat → Option Nat = λ
  { #Zero _ ⇒ #None {,}
  | #Suc n ⇒ #Some n }

pred : { #Z {,} → #None | #Suc Nat → #Some Nat }
pred : { #Z {,} | #Suc Nat } → { #None | #Some Nat }
pred : Nat → Option Nat
```

## Typing

Read `A <: A'` as "`A` is less general than `A'`. For example, `A` is less
general than `{ A | B }`, and `{ A , B }` is less general than `A`.

Notation
```text
{ A } ::= { A | } or { A , }
{ Aᵢ * } ::= { A_1 * ... * A_n } for some n
```

Subtyping coercion.
_Intuition:_ if `A` is more specific that `A'`, then `a : A` implies that 
`a : A'`.
```
Γ ⊢ a : A
Γ ⊢ A <: A'
---
Γ ⊢ a : A'
```

### Tag

Type of tag.
```
Γ ⊢ a : A
---
#t(a) : #t(A)
```

Subtype under tag.
```
Γ ⊢ A <: A'
---
Γ ⊢ #t(A) <: #t(A')
```

### Arrow

Subtype under arrow.
_Intuition:_ if `f : A → B` is a subtype of `f' : A' → B'`, then `f` handles
only some of the inputs that `f'` does and `f` yields more outputs that `f'`
does.
```
Γ ⊢ A <: A'
Γ ⊢ B' <: B
---
Γ ⊢ (A → B) <: (A' → B')
```

### Conjunction

Subtype into singleton conjunction.
```
∅
---
Γ ⊢ A <: { A }
```

Subtype under conjunction.
```
Γ ⊢ A <: A'
---
Γ ⊢ { A , [ Aᵢ , ] } <: { A' , [ Aᵢ , ] }
```

Subtype weaken conjunction.
```
∅
---
Γ ⊢ { A , [ Aᵢ , ] } <: { [ Aᵢ , ] }
```

Subtype empty conjunction.
_Intuition_: the empty conjunction `{,}` is like unit, is has one form and so
every other type is more specific than it.
```
∅
---
Γ ⊢ A <: {,}
```

Subtype over arrows under conjunction.
_Intuition:_ this must handle all input types, but client only needs to handle one
output type.
output.
```
∅
---
Γ ⊢ { [ Aᵢ -> Bᵢ , ] } <: { [ Aᵢ , ] } -> { [ Bᵢ | ] }
```

### Disjunction

Subtype into singleton conjunction.
```
∅
---
Γ ⊢ A <: { A }
```

Subtype under conjunction.
```
Γ ⊢ A <: A'
---
Γ ⊢ { A | [ Aᵢ | ] } <: { A' | [ Aᵢ | ] } // forall i
```

Subtype weaken conjunction.
```
∅
---
Γ ⊢ { [ Aᵢ | ] } <: { A | [ Aᵢ | ] } // forall i
```

Subtype empty conjunction.
_Intuition:_ the empty conjunction `{|}` is like void; it has no forms and so it
is more specific than any other type. 
```
∅
---
Γ ⊢ {|} <: A
```

Subtype over arrows under disjunction.  
_Intuition:_ this only needs to handle one input type, but client must handle all
types of output.
```
∅
---
Γ ⊢ { [ Aᵢ -> Bᵢ | ] } <: { [ Aᵢ | ] } -> { [ Bᵢ , ] } // forall i
```

### Abstraction

Abstraction over bind.
```
Γ , (x : A) ⊢ b : B
---
Γ ⊢ λ{ (x : A) ⇒ b } : A → B
```

Abstraction over tag pattern.
```
Γ ⊢ λ{ p ⇒ b } : A → B
---
Γ ⊢ λ{ #t p ⇒ b } : #t A → B
```

Abstraction over conjunction pattern.
```
Γ ⊢ [ λ{ pᵢ ⇒ ] b [ } ] : [ Aᵢ → ] B
---
Γ ⊢ λ{ { [ pᵢ , ] } ⇒ b } : { [ Aᵢ , ] } → B
```

Abstraction over disjunction pattern.
```
[ Γ ⊢ λ{ pᵢ ⇒ bᵢ } ]
---
Γ ⊢ λ{ [ pᵢ ⇒ bᵢ | ] } : { [ Aᵢ → Bᵢ | ] }
```

### Application

```
Γ ⊢ f : A → B
Γ ⊢ a : A
---
Γ ⊢ f a : B
```

## Normalization

**Theorem.** If `a : A` and `a' : A'` and `A ⇓ A'`, then `a : A'` and `a' : A`.
That is, normalization doesn't make a type more or less specific.

Transitivity.
```
A ⇓ A'
A' ⇓ A''
---
A ⇓ A''
```

Flatten conjunction/disjunction.
```
{ { [ A_i , ] }, [ A_j , ] } ⇓ { [ A_i , ] [ A_j , ] }
{ { [ A_i | ] }, [ A_j | ] } ⇓ { [ A_i | ] [ A_j | ] }
```

Normalize under tag. TODO: write
Normalize under conjunction/disjunction. TODO: write
Normalize under arrow. TODO: write

TODO: more normalizations


