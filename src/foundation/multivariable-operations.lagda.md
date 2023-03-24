# Multivariable operations

```agda
module foundation.multivariable-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.coproduct-types
open import foundation.identity-types
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
multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) n) →
  UU l
multivariable-input zero-ℕ A = raise-unit _
multivariable-input (succ-ℕ n) A =
  A (inr star) × multivariable-input n (tail-functional-vec n A)

empty-multivariable-input :
  {l : Level}
  (A : functional-vec (UU l) 0) →
  multivariable-input 0 A
empty-multivariable-input A = raise-star

head-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  head-functional-vec n A
head-multivariable-input n A (a0 , a) = a0

tail-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  multivariable-input n (tail-functional-vec n A)
tail-multivariable-input n A (a0 , a) = a

cons-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : functional-vec (UU l) n) →
  {A0 : UU l} →
  A0 →
  multivariable-input n A →
  multivariable-input (succ-ℕ n) (cons-functional-vec n A0 A)
pr1 (cons-multivariable-input n A a0 a) = a0
pr2 (cons-multivariable-input n A a0 a) = a

multivariable-operation :
  { l : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l) n)
  ( X : UU l) →
  UU l
multivariable-operation n A X =
 (multivariable-input n A → X)
```
