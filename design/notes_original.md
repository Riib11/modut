# Structural Refinement Types for Extrinsic Proofs
Grammar: regular types with constructors
```
Sign ::= Pi x . T
T ::= C [T] | T \/ T | T /\ T | fix x . T | x
C in constructors
```
Note that `\/` and `/\` are commutative. You can only access specific fields/cases by pattern matching.

## Natural Numbers
```
Constructors 
  Z : Type
  S : Type -> Type
Nat = fix a . Z \/ S a
```

## Simple Intrinsic Proofs
Consider the following function
```
Add2 n = S (S n)
```
The type of this function can be inferred to be
```
Add2 : forall a . a -> S (S a)
```
But actually we want `Add2` to be defined over natural numbers specifically! We can either check that it does via
```
#Check Add2 : Nat -> Nat
```
Which gets verified automatically by (sub)type-checking.
Or, we can declare the type of `Add2` before defining it, which only exposes the declared type of `Add2` to other functions.
```
Add2 : Nat -> Nat
Add n = S (S n)
```
But, perhaps this is too restrictive. We still want to expose that `Add2 n = S (S n)`. So, we can partially annotate the type of `Add2` like so:
```
Add2 : Nat -> _
Add2 n = S (S n)
```
The `_` indicates that this type should be inferred. The type is inferred to be the following:
```
Add2 : Nat -> S (S Nat)
```
This type is normal.

Suppose that we want to prove that `Add2` preserves `Even`? Where `Even` is defined as follows.
```
Even = fix a . Z \/ S (S a)
```
We can try to write the signature of this proof as something like the following
```
Add2-preserves-Even : Even -> Even
```
But, this does not claim that `Add2` is the function in particular that has this signature! So, unlike usually approaches to refinement types, we actually want something like the following:
```
#Check Add2 : Even -> Even
```
Which proves the claim automatically via typechecking!

## Typing Rules
Subtype over constructor
```
G |- [A <: B]
–––––––––––––––––––––––––––––––––––––––
G |- C [A] <: C [B]
```

Subtype over arrow
```
G |- A  <: A’
G |- B’ <: B
–––––––––––––––––––––––––––––––––––––––
G |- A -> B <: A’ -> B’
```

Subtype over conjunction
```
G |- A <: A’
G |- B <: B’
–––––––––––––––––––––––––––––––––––––––
G |- A /\ B <: A’ /\ B’

–––––––––––––––––––––––––––––––––––––––
G |- A /\ B <: A

–––––––––––––––––––––––––––––––––––––––
G |- (A -> B) /\ (A’ -> B’) <: A \/ A’ -> B /\ B’
```

Subtype over disjunction
```
G |- A <: A’
G |- B <: B’
–––––––––––––––––––––––––––––––––––––––
G |- A \/ B <: A’ \/ B’

–––––––––––––––––––––––––––––––––––––––
G |- A <: A \/ B

–––––––––––––––––––––––––––––––––––––––
G |- (A -> B) /\ (A’ -> B’) <: A /\ A’ -> B \/ B’
```

## Normalizing Refinement Types
In a refinement type system, we often want to be able to write Pi-like function types i.e. `a:A -> B[a]` where `P a` is the claim of some predicate holding over `a` and the value of `B`. But, so far this isn’t part of our syntax. But there is a translation from this form to our syntax, since all definitions are lifted in a sense (we know about the structure of their output).

### Normalization Rules

Substitution of named argument.
```
B[x] ==> B[x=A] where x:A
```

Constructors
```
C (A \/ B) = C A \/ C B // distribute over sum
C (A /\ B) = C A \/ C B // distribute over product
```

Subtypes in sums and products.
```
A \/ A’ ==> A’ if A <: A’ // simplifies to most general disjunct
A /\ A’ ==> A if A <: A’ // simplifies to most specific conjunct
```

Arrow
```
TODO
```

## Example: (nat) add is commutative
```
Add (n : Nat) (m : Nat) =
Add Z n = n
Add m Z = m
Add (S m) n = S (Add m n)
```
The type of  `Add` is inferred to be
```
Add : ((n : Z) -> (m : Nat) -> Nat) \/
      ((n : S Nat) -> (m : Z) -> S Nat) \/
      (fix a . (n : S Nat) -> (m : S Nat) -> S a) )
```
Here we have a disjunction of (function) types, via `\/`, as the type of `Add`. What does this mean? Well, it handles each different case of `Add`, which matches onto the inputs.