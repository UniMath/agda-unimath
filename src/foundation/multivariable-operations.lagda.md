# Multivariable operations

```agda
module foundation.multivariable-operations where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types

open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.tuples

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

### Multivariable inputs are equivalent to elements of finite sequences of types

```agda
module _
  {l : Level}
  where

  Π-fin-sequence : (n : ℕ) → fin-sequence (UU l) n → UU l
  Π-fin-sequence n A = (i : Fin n) → A i

  multivariable-input-Π-fin-sequence :
    (n : ℕ)
    (A : fin-sequence (UU l) n) →
    Π-fin-sequence n A →
    multivariable-input n A
  multivariable-input-Π-fin-sequence zero-ℕ A H = raise-star
  multivariable-input-Π-fin-sequence (succ-ℕ n) A H =
    ( H (neg-one-Fin n) ,
      multivariable-input-Π-fin-sequence
        ( n)
        ( tail-fin-sequence n A)
        ( H ∘ inl-Fin n))

  Π-fin-sequence-multivariable-input :
    (n : ℕ)
    (A : fin-sequence (UU l) n) →
    multivariable-input n A →
    Π-fin-sequence n A
  Π-fin-sequence-multivariable-input zero-ℕ A H ()
  Π-fin-sequence-multivariable-input (succ-ℕ n) A H (inl x) =
    Π-fin-sequence-multivariable-input
      ( n)
      ( tail-fin-sequence n A)
      ( tail-multivariable-input n A H)
      ( x)
  Π-fin-sequence-multivariable-input (succ-ℕ n) A H (inr x) =
    head-multivariable-input n A H

  is-section-multivariable-input-Π-fin-sequence :
    ( n : ℕ)
    ( A : fin-sequence (UU l) n) →
    ( multivariable-input-Π-fin-sequence n A ∘
      Π-fin-sequence-multivariable-input n A) ~
    id
  is-section-multivariable-input-Π-fin-sequence zero-ℕ A =
    is-section-map-inv-raise
  is-section-multivariable-input-Π-fin-sequence (succ-ℕ n) A H =
    eq-pair
      ( refl)
      ( is-section-multivariable-input-Π-fin-sequence
        ( n)
        ( tail-fin-sequence n A)
        ( tail-multivariable-input n A H))

  htpy-retraction-multivariable-input-Π-fin-sequence :
    (n : ℕ)
    (A : fin-sequence (UU l) n) →
    (u : Π-fin-sequence n A) →
    (i : Fin n) →
    Π-fin-sequence-multivariable-input
      ( n)
      ( A)
      ( multivariable-input-Π-fin-sequence
        ( n)
        ( A)
        ( u))
      ( i) ＝
    u i
  htpy-retraction-multivariable-input-Π-fin-sequence (succ-ℕ n) A u (inl x) =
    htpy-retraction-multivariable-input-Π-fin-sequence
      ( n)
      ( tail-fin-sequence n A)
      ( u ∘ inl-Fin n)
      ( x)
  htpy-retraction-multivariable-input-Π-fin-sequence (succ-ℕ n) A u (inr x) =
    refl

  is-retraction-multivariable-input-Π-fin-sequence :
    ( n : ℕ)
    ( A : fin-sequence (UU l) n) →
    ( Π-fin-sequence-multivariable-input n A ∘
      multivariable-input-Π-fin-sequence n A) ~
    id
  is-retraction-multivariable-input-Π-fin-sequence n A =
    eq-htpy ∘ htpy-retraction-multivariable-input-Π-fin-sequence n A

  is-equiv-multivariable-input-Π-fin-sequence :
    (n : ℕ)
    (A : fin-sequence (UU l) n) →
    is-equiv (multivariable-input-Π-fin-sequence n A)
  is-equiv-multivariable-input-Π-fin-sequence n A =
    is-equiv-is-invertible
      ( Π-fin-sequence-multivariable-input n A)
      ( is-section-multivariable-input-Π-fin-sequence n A)
      ( is-retraction-multivariable-input-Π-fin-sequence n A)

  equiv-multivariable-input-Π-fin-sequence :
    (n : ℕ) →
    (A : fin-sequence (UU l) n) →
    Π-fin-sequence n A ≃
    multivariable-input n A
  equiv-multivariable-input-Π-fin-sequence n A =
    ( multivariable-input-Π-fin-sequence n A ,
      is-equiv-multivariable-input-Π-fin-sequence n A)
```

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
