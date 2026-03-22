# Multivariable operations

```agda
module foundation.multivariable-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import lists.finite-sequences
open import lists.tuples
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
  (A : fin-sequence (UU l) n) →
  UU l
multivariable-input zero-ℕ A = raise-unit _
multivariable-input (succ-ℕ n) A =
  A (inr star) × multivariable-input n (tail-fin-sequence n A)

empty-multivariable-input :
  {l : Level}
  (A : fin-sequence (UU l) 0) →
  multivariable-input 0 A
empty-multivariable-input A = raise-star

head-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  head-fin-sequence n A
head-multivariable-input n A (a0 , a) = a0

tail-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) (succ-ℕ n)) →
  multivariable-input (succ-ℕ n) A →
  multivariable-input n (tail-fin-sequence n A)
tail-multivariable-input n A (a0 , a) = a

cons-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : fin-sequence (UU l) n) →
  {A0 : UU l} →
  A0 →
  multivariable-input n A →
  multivariable-input (succ-ℕ n) (cons-fin-sequence n A0 A)
pr1 (cons-multivariable-input n A a0 a) = a0
pr2 (cons-multivariable-input n A a0 a) = a

multivariable-operation :
  { l : Level}
  ( n : ℕ)
  ( A : fin-sequence (UU l) n)
  ( X : UU l) →
  UU l
multivariable-operation n A X =
  multivariable-input n A → X
```

## Properties

### For the case of constant families, multivariable inputs and tuples coincide

```agda
tuple-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  multivariable-input n (λ _ → A) →
  tuple A n
tuple-multivariable-input zero-ℕ A _ = empty-tuple
tuple-multivariable-input (succ-ℕ n) A (a0 , a) =
  a0 ∷ (tuple-multivariable-input n A a)

multivariable-input-tuple :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  tuple A n →
  multivariable-input n (λ _ → A)
multivariable-input-tuple zero-ℕ A _ = raise-star
multivariable-input-tuple (succ-ℕ n) A (a0 ∷ a) =
  cons-multivariable-input n (λ _ → A) a0
    ( multivariable-input-tuple n A a)

is-section-multivariable-input-tuple :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  ( tuple-multivariable-input n A ∘
    multivariable-input-tuple n A) ~ id
is-section-multivariable-input-tuple zero-ℕ A empty-tuple = refl
is-section-multivariable-input-tuple (succ-ℕ n) A (a0 ∷ a) =
  ap (_∷_ a0) ( is-section-multivariable-input-tuple n A a)

is-retraction-multivariable-input-tuple :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  ( multivariable-input-tuple n A ∘
    tuple-multivariable-input n A) ~ id
is-retraction-multivariable-input-tuple zero-ℕ A (map-raise star) = refl
is-retraction-multivariable-input-tuple (succ-ℕ n) A (a0 , a) =
  eq-pair refl ( is-retraction-multivariable-input-tuple n A a)

is-equiv-tuple-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  is-equiv (tuple-multivariable-input n A)
is-equiv-tuple-multivariable-input n A =
  is-equiv-is-invertible
    ( multivariable-input-tuple n A)
    ( is-section-multivariable-input-tuple n A)
    ( is-retraction-multivariable-input-tuple n A)

compute-tuple-multivariable-input :
  {l : Level}
  (n : ℕ)
  (A : UU l) →
  multivariable-input n (λ _ → A) ≃ tuple A n
pr1 (compute-tuple-multivariable-input n A) =
  tuple-multivariable-input n A
pr2 (compute-tuple-multivariable-input n A) =
  is-equiv-tuple-multivariable-input n A
```
