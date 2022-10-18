data Nat : * where
  Zero : Nat
  Suc : Nat -> Nat

::=

mutual
  axiom Zero : *
  axiom Suc : * -> *

  type Nat : *
  type Nat = fix n in {Zero | Suc n}

  axiom Zero : Zero
  axiom Suc : Nat -> Suc Nat