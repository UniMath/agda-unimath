# Multivariable operations

```agda
module foundation.multivariable-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given `n` types, an n-ary multivariable operation on them is a function that
takes as inputs one element of each type, and returns an element in some type
`X`.

## Definitions

```agda
multivariable-operation :
  {l : Level}
  (n : ℕ)
  (As : functional-vec (UU l) n)
  (X : UU l) →
  UU l
multivariable-operation zero-ℕ As X = X
multivariable-operation (succ-ℕ n) As X =
  ( head-functional-vec n As) →
  ( multivariable-operation n (tail-functional-vec n As) X)

apply-multivariable-operation :
  {l : Level}
  (n : ℕ)
  (As : functional-vec (UU l) n)
  (X : UU l) →
  multivariable-operation n As X →
  ((i : Fin n) → As i) → X
apply-multivariable-operation zero-ℕ As X f as = f
apply-multivariable-operation (succ-ℕ n) As X f as =
  apply-multivariable-operation n
    ( tail-functional-vec n As)
    ( X)
    ( f (as (neg-one-Fin n)))
    ( λ i → as (inl-Fin n i))
```
