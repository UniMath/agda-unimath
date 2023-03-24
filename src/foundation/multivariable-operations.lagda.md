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
  (As : functional-vec (UU l) n) →
  UU l
multivariable-input zero-ℕ As = raise-unit _
multivariable-input (succ-ℕ n) As =
  As (inr star) × multivariable-input n (tail-functional-vec n As)
--(i : Fin n) → As i

-- empty-multivariable-input :
--   {l : Level}
--   (As : functional-vec (UU l) 0) →
--   multivariable-input 0 As
-- empty-multivariable-input As ()

-- head-multivariable-input :
--   {l : Level}
--   (n : ℕ)
--   (As : functional-vec (UU l) (succ-ℕ n)) →
--   multivariable-input (succ-ℕ n) As →
--   head-functional-vec n As
-- head-multivariable-input n As as =
--   as (neg-one-Fin n)

tail-multivariable-input :
  {l : Level}
  (n : ℕ)
  (As : functional-vec (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) As →
  multivariable-input n (tail-functional-vec n As)
tail-multivariable-input n As (a , a0) = a0
  -- (λ i → as (inl-Fin n i))

-- cons-multivariable-input :
--   {l : Level}
--   (n : ℕ)
--   (As : functional-vec (UU l) n) →
--   {A : UU l} →
--   A →
--   multivariable-input n As →
--   multivariable-input (succ-ℕ n) (cons-functional-vec n A As)
-- cons-multivariable-input n As a as (inl x) = as x
-- cons-multivariable-input n As a as (inr x) = a

-- cons-multivariable-input' :
--   { l1 : Level}
--   ( n : ℕ)
--   ( As : functional-vec (UU l1) (succ-ℕ n))
--   ( a0 : As (inr star))
--   ( as : multivariable-input n (tail-functional-vec n As)) →
--   multivariable-input (succ-ℕ n) As
-- cons-multivariable-input' n As a as (inl x) = as x
-- cons-multivariable-input' n As a as (inr star) = a

-- multivariable-operation :
--   { l : Level}
--   ( n : ℕ)
--   ( As : functional-vec (UU l) n)
--   ( X : UU l) →
--   UU l
-- multivariable-operation n As X =
--  (multivariable-input n As → X)

-- curry-once-multivariable-operation :
--   { l : Level}
--   ( n : ℕ)
--   ( As : functional-vec (UU l) (succ-ℕ n))
--   ( X : UU l) →
--   ( multivariable-operation (succ-ℕ n) As X) →
--   ( head-functional-vec n As) →
--   multivariable-operation n (tail-functional-vec n As) X
-- curry-once-multivariable-operation n As X f a v =
--   f (cons-multivariable-input' n As a v)
```
