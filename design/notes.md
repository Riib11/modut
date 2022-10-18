# Modut

## Restrictions

No higher-kinded polymorphism
- Higher-kinded polymorphism would require keeping track of polarity constraints
  on higher-kinded type variables

Tuple fields must be named (tagged).
- It's better etiquette anyway
- The flattening and unordering of conjunctions is important to many subtyping
  features, so its cumbersome to add ordered tuples as a basic language feature
  rather than just as a type alias i.e.
  `Tuple3 = forall a b c => { Field1#a , Field2#b , Field3#c }`.

No basic datatypes i.e. `data Nat = ...`
- Tags, conjunctions, disjunctions, and fixed points allow for the full
  expressiveness (and more) of _regular types_, which has been recognized as a
  reasonable basis for a polymorphic datatype system.
- Named datatypes are just type aliases. Let-normal form keeps track of the
  named given in type aliases to ensure nice-looking error messages.

## Syntax

- The notation `*[...]` indicates that the contained phrase can be repeated any number of
  times (including 0 times).
- The notation `+[...]` indicates that the contained phrase can be repeated any
  non-zero number of times.  
- The notation `?[...]` indicates that the contained phrase is optional.
```
<kd> ::= *[ Type -> ] Type

// TODO: need to keep track of polarities? for the sake of subtyping? 
// TODO: or, will this work out since let-type just makes an alias which is expanded during typechecking
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

Kinding type variable.
```
∅
---
Γ , (X : Type) ⊢ X : Type
```

Kinding abstraction.
```
Γ , [ (Xᵢ : Type) ] ⊢ A : Type
---
Γ ⊢ ∀ [ Xᵢ ] ⇒ A : [ Type → ] Type
```

Kinding application.
```
Γ ⊢ F = ∀ [ Xᵢ ] ⇒ A
Γ ⊢ F : [ Type → ] Type
[ Γ ⊢ Aᵢ : Type ]
---
Γ ⊢ F [ Aᵢ ] : Type
```

Kinding conjunction.
```
TODO
```

Kinding type disjunction.
```
TODO
```

Kinding arrow.
```
Γ ⊢ A : Type
Γ ⊢ B : Type
---
Γ ⊢ A -> B : Type
```

Kinding fixed point.
```
Γ , (X : Type) ⊢ A : Type 
---
Γ ⊢ fix X => A : Type
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

Subtype into singleton conjunction (Same as singleton disjunction).
```
∅
---
Γ ⊢ A <: { A }
```

Subtype under conjunction.
```
Γ ⊢ A <: A'
---
Γ ⊢ { A , B } <: { A' , B }
```

Subtype weaken conjunction.
```
∅
---
Γ ⊢ { A , B } <: { B }
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

Subtype into singleton disjunction. (Same as singleton conjunction.)
```
∅
---
Γ ⊢ A <: { A }
```

Subtype under disjunction.
```
Γ ⊢ A <: A'
---
Γ ⊢ { A | B } <: { A' | B }
```

Subtype weaken disjunction.
```
∅
---
Γ ⊢ { A } <: { A | B }
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
Γ ⊢ { [ Aᵢ -> Bᵢ | ] } <: { [ Aᵢ | ] } -> { [ Bᵢ , ] }
```

**Fixed point**

Subtype under fixed point.
```
Γ (X = A) ⊢ A <: A'
---
Γ ⊢ fix X => A <: fix X => A'
```
This implies that unrolling a step of the fixed point makes the type more specific,
making use of the substitution subtyping rule.
For example
```
fix n => { Zero#{,} | Suc#{ Zero#{,} | Suc#n } } <:
fix n => { Zero#{,} | Suc#n }
```

**Application**

TODO

**Substitution**

Subtype using substitution.
TODO: is this ok, or does it break typechecking? 
TODO: if this works, then typechecking can just use let-normal form
```
---
Γ , (X = A) ⊢ A <: X
```

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

## Unification

The unifier type of two types is the most specific type that both types are subtypes of e.g.

```
Gamma |- A ~{U}~ B
---
Gamma |- A <: U
Gamma |- B <: U
Gamma |- forall U' if A <: U' and B <: U', then U <: U'
```

**Theorem.** For all types `A` and `B`, exists `C` such that `A ~{C}~ B`.

TODO: unification rules

## Typechecker Algorithm

TODO
