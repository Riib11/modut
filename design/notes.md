# Modut

## Syntax

- The notation `*[...]` indicates that the contained phrase can be repeated any number of
  times (including 0 times).
- The notation `+[...]` indicates that the contained phrase can be repeated any
  non-zero number of times.  
- The notation `?[...]` indicates that the contained phrase is optional.
```
<kd> ::= *[ Type -> ] Type

<ty1> ::= ∀ *[<ty-var>] ⇒ <ty>

<ty> ::=
  | <ty-var>
  | <tag> # <ty>
  | {*[<ty> ,]}
  | {*[<ty> |]}
  | <ty> → <ty>
  | μ <ty-var> ⇒ <ty>
  | <ty-var> <ty>

<tm> ::=
  | <tm-var>
  | <tag>#<tm>
  | <tm>.<tag>
  | {*[ <tm> , ]} 
  | λ (<tm-var> : <ty>) ⇒ b
  | <tm> <tm>
  | let <tm-var> : <ty1> = <tm> in <tm>
  | let <ty-var> : <kd> = <ty1> in <tm>

<tag> ::= <tag-name>
<ty-var> ::= <type-variable-name>
<tm-var> ::= <term-var-name>
```

Syntax sugar
```text
<tm> +::= λ{ *[ <pat> ⇒ <tm> | ] }

<pat> ::=
  | <tm-var> : <ty>
  | <tag>#<pat>
  | {*[ <pat> , ]}

λ{ (x : A) ⇒ b }      ::= λ (x : A) ⇒ b
λ{ t#p ⇒ b }          ::= λ (x : t#_) ⇒ λ{ p ⇒ b } x.t
λ{ { [ pᵢ , ] } ⇒ b } ::= λ a ⇒ [ λ{ pᵢ ⇒ ] b [ } a ] 
λ{ [ pᵢ ⇒ bᵢ | ] }    ::= { [ λ{ pᵢ ⇒ bᵢ } , ] }
```

Special features:
- Polymorphism is *implicit*
- No *pattern matching* in basic syntax
  - can be achieved via conjunctions of annotated lambdas
- Tag types and terms are special. They are uniquely identified by their tag.
  - The `<tag>#<tm>` form "wraps", or "tags", a type or term.
  - The `<tm>.<tag>` form "unwraps", or "untags", a tagged term.
    - There is no type-level operation to untag a tagged type.

**Examples**
```text
Option = ∀ a ⇒ { None#{,} | Some#a }
Nat = μ n ⇒ { Zero#{,} | Suc#n }


// without syntax sugar
pred_of_Nat =
  { λ (_ : Zero#{,}) ⇒ None#{,} }
  , λ (n : Suc#Nat) ⇒ Some#(n.Suc) }
// with syntax sugar
pred_of_Nat = λ
  { Zero#{,} ⇒ None#{,}
  , Suc#(n : Nat) ⇒ Some#n }

pred_of_Nat : 
  { Zero#{,} → None#{,} | Suc#Nat → Some#Nat } <:
  { Zero#{,} | Suc#Nat } → { None#{,} | Some#Nat } =
  Nat → Option Nat

// without syntax sugar
pred_of_Suc = λ (n : Suc Nat) ⇒ n.Suc#
// with syntax sugar
pred_of_Suc = λ{ Suc#(n : Nat) ⇒ n }

pred_of_Suc :
  Suc#Nat → Nat <:
  Nat → Nat
```

## Kinding

```
Γ , [ (Xᵢ : Type) ] ⊢ A : Type
---
Γ ⊢ ∀ [ Xᵢ ] ⇒ A : [ Type → ] Type
```

## Subtyping

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

**Tagged type**

Subtype under tag.
```
Γ ⊢ A <: A'
---
Γ ⊢ t#A <: t#A'
```

**Arrow**

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

**Conjunction**

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

**Disjunction**

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

**Type fixed point**

TODO

**Type application**

## Typing

**Tagged term**

Type of tag.
```
Γ ⊢ a : A
---
t#a : t#A
```

**Untagged term**

Type of untag.
```
Γ ⊢ b : t#A
---
b.t : A
```

**Abstraction**

Abstraction.
```
Γ , (x : A) ⊢ b : B
---
Γ ⊢ (λ (x : A) ⇒ b) : A → B
```

**Application**

```
Γ ⊢ f : A → B
Γ ⊢ a : A
---
Γ ⊢ f a : B
```

**Conjunction**

```
[ Γ ⊢ aᵢ : Aᵢ ]
---
Γ ⊢ { [ aᵢ , ] } : { [ Aᵢ , ] }
```

**Let-term**

```
Γ ⊢ a : A
Γ , (a : A) ⊢ b : B
--- 
Γ ⊢ let x : A = a in b : B
```

**Let-type**

```
Γ ⊢ X : K
Γ , (X : K = A) ⊢ b : B
--- 
Γ ⊢ let X : K = A in b : B
```

## Normalization of Types

**Theorem.** If `Γ ⊢ a : A` and `Γ ⊢ a' : A'` and `Γ ⊢ A ⇓ A'`, then 
`Γ ⊢ a : A'` and `Γ ⊢ a' : A`. That is, normalization doesn't make a type more
or less specific.

Transitivity.
```
Γ ⊢ A ⇓ A'
Γ ⊢ A' ⇓ A''
---
Γ ⊢ A ⇓ A''
```

Flatten conjunction/disjunction.
```
Γ ⊢ { { [ Aᵢ , ] }, [ Aⱼ , ] } ⇓ { [ Aᵢ , ] [ Aⱼ , ] }
Γ ⊢ { { [ Aᵢ | ] }, [ Aⱼ | ] } ⇓ { [ Aᵢ | ] [ Aⱼ | ] }
```

Normalize under tag. TODO: write
Normalize under conjunction/disjunction. TODO: write
Normalize under arrow. TODO: write

Normalize under type application.
```
Γ , (F = ∀ [ xᵢ ] ⇒ B) ⊢ F [ Aᵢ ] ⇓ B[ xᵢ ↦ Aᵢ ] 
```

TODO: more normalizations

## Normalization of Terms

**Theorem.** _(Evaluation)_ If `∅ ⊢ a : A` and `∅ ⊢ a ⇓ a'` then `∅ ⊢ a' val`.

**Theorem.** _(Type preservation)_ If `∅ ⊢ a : A` and `∅ ⊢ a ⇓ a'` then 
`a' : A`.

**Theorem.** _(Progress)_ If `∅ ⊢ a : A` then either `∅ ⊢ a val` or `∅ ⊢ a ⇓ a'`
for some `a'`.

**Variable**

```
∅
---
Δ , (x = a) ⊢ x ⇓ a
```

**Tag**

```
Δ ⊢ a ⇓ a'
---
Δ ⊢ t#a ⇓ t#a'
```

**Untag**

```
Δ ⊢ a ⇓ t#b
---
Δ ⊢ a.t ⇓ b
```

**Conjunction**

```
[ Δ ⊢ aᵢ ⇓ aᵢ' ]
---
Δ ⊢ { [ aᵢ , ] } ⇓ { [ aᵢ' , ] }
```

**Abstraction**

```
Δ ⊢ (λ (x : A) ⇒ b) val
```

**Application**

Application of abstraction.
```
Δ ⊢ f ⇓ (λ (x : A) ⇒ b)
Δ ⊢ a ⇓ a'
Δ ⊢ b[x ↦ a'] ⇓ b'
---
Δ ⊢ f a ⇓ b'
```

**Let-Term**

```
Δ ⊢ a ⇓ a'
Δ , (x = a') ⊢ b ⇓ b' 
---
Δ ⊢ let x : A = a in b ⇓ b'
```

**Let-Type**

```
Δ ⊢ b ⇓ b'
---
Δ ⊢ let … : … = … in b ⇓ b'
```



