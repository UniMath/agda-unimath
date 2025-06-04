# Convolution of sequences in commutative semirings

```agda
module commutative-algebra.convolution-sequences-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.pairs-with-natural-sums
open import elementary-number-theory.natural-numbers
open import commutative-algebra.commutative-semirings
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.sequences
open import foundation.unit-type
open import foundation.coproduct-types
open import foundation.identity-types
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings
open import univalent-combinatorics.standard-finite-types
```

## Idea

## Definition

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  convolution-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R) →
    sequence (type-Commutative-Semiring R) →
    sequence (type-Commutative-Semiring R)
  convolution-sequence-Commutative-Semiring a b n =
    sum-finite-Commutative-Semiring
      ( R)
      ( finite-type-pair-with-sum-ℕ n)
      ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a i) (b j))
```

## Properties

### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-commutative-convolution-sequence-Commutative-Semiring :
    (a b : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R a b ~
    convolution-sequence-Commutative-Semiring R b a
  htpy-commutative-convolution-sequence-Commutative-Semiring a b n =
    equational-reasoning
      sum-finite-Commutative-Semiring
        ( R)
        ( finite-type-pair-with-sum-ℕ n)
        ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a i) (b j))
      ＝
        sum-finite-Commutative-Semiring
          ( R)
          ( finite-type-pair-with-sum-ℕ n)
          ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (a j) (b i))
        by
          sum-aut-finite-Commutative-Semiring
            ( R)
            ( finite-type-pair-with-sum-ℕ n)
            ( aut-swap-pair-with-sum-ℕ n)
            ( _)
      ＝
        sum-finite-Commutative-Semiring
          ( R)
          ( finite-type-pair-with-sum-ℕ n)
          ( λ (i , j , j+i=n) → mul-Commutative-Semiring R (b i) (a j))
        by
          htpy-sum-finite-Commutative-Semiring R _
            ( λ (i , j , j+i=n) → commutative-mul-Commutative-Semiring R _ _)

  commutative-convolution-sequence-Commutative-Semiring :
    (a b : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R a b ＝
    convolution-sequence-Commutative-Semiring R b a
  commutative-convolution-sequence-Commutative-Semiring a b =
    eq-htpy (htpy-commutative-convolution-sequence-Commutative-Semiring a b)
```

### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  unit-convolution-sequence-Commutative-Semiring :
    sequence (type-Commutative-Semiring R)
  unit-convolution-sequence-Commutative-Semiring zero-ℕ =
    one-Commutative-Semiring R
  unit-convolution-sequence-Commutative-Semiring (succ-ℕ n) =
    zero-Commutative-Semiring R

  htpy-left-unit-law-convolution-sequence-Commutative-Semiring :
    (a : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( unit-convolution-sequence-Commutative-Semiring)
      ( a)
      ~ a
  htpy-left-unit-law-convolution-sequence-Commutative-Semiring a n =
    equational-reasoning
      sum-finite-Commutative-Semiring R
        ( finite-type-pair-with-sum-ℕ n)
        ( λ (i , j , j+i=n) →
          mul-Commutative-Semiring R
            ( unit-convolution-sequence-Commutative-Semiring i)
            ( a j))
      ＝
        add-Commutative-Semiring R
          ( sum-fin-sequence-type-Commutative-Semiring R
            ( n)
            ( λ k → mul-Commutative-Semiring R (zero-Commutative-Semiring R) _))
          ( mul-Commutative-Semiring R (one-Commutative-Semiring R) (a n))
          by
            eq-sum-finite-sum-count-Commutative-Semiring R
              ( finite-type-pair-with-sum-ℕ n)
              ( count-pair-with-sum-ℕ n)
              ( _)
      ＝
        add-Commutative-Semiring R
          ( sum-fin-sequence-type-Commutative-Semiring R
            ( n)
            ( λ _ → zero-Commutative-Semiring R))
          ( a n)
          by
            ap-add-Commutative-Semiring R
              ( htpy-sum-fin-sequence-type-Commutative-Semiring R n
                ( λ _ → left-zero-law-mul-Commutative-Semiring R _))
              ( left-unit-law-mul-Commutative-Semiring R _)
      ＝
        add-Commutative-Semiring R
          ( zero-Commutative-Semiring R)
          ( a n)
          by
            ap-add-Commutative-Semiring R
              ( sum-zero-fin-sequence-type-Commutative-Semiring R n)
              ( refl)
      ＝ a n by left-unit-law-add-Commutative-Semiring R _

  left-unit-law-convolution-sequence-Commutative-Semiring :
    (a : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( unit-convolution-sequence-Commutative-Semiring)
      ( a)
      ＝ a
  left-unit-law-convolution-sequence-Commutative-Semiring a =
    eq-htpy (htpy-left-unit-law-convolution-sequence-Commutative-Semiring a)

  right-unit-law-convolution-sequence-Commutative-Semiring :
    (a : sequence (type-Commutative-Semiring R)) →
    convolution-sequence-Commutative-Semiring R
      ( a)
      ( unit-convolution-sequence-Commutative-Semiring)
      ＝ a
  right-unit-law-convolution-sequence-Commutative-Semiring a =
    commutative-convolution-sequence-Commutative-Semiring R _ _ ∙
    left-unit-law-convolution-sequence-Commutative-Semiring a
```
