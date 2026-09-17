# Multiplication of square matrices on rings

```agda
{-# OPTIONS --lossy-unification #-}
module linear-algebra.multiplication-square-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.singleton-subtypes-discrete-types
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups

open import linear-algebra.diagonal-matrices-on-rings
open import linear-algebra.identity-matrices-on-rings
open import linear-algebra.multiplication-matrices-on-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings
open import ring-theory.sums-of-finite-families-of-elements-rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

[Square matrices](linear-algebra.square-matrices-on-rings.md) on a
[ring](ring-theory.rings.md) form a [monoid](group-theory.monoids.md) under
[multiplication](linear-algebra.multiplication-matrices-on-rings.md).

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  mul-square-matrix-Ring :
    square-matrix-Ring R n → square-matrix-Ring R n → square-matrix-Ring R n
  mul-square-matrix-Ring = mul-matrix-Ring R n n n
```

## Properties

### Associativity of square matrix multiplication

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  associative-mul-square-matrix-Ring :
    (A B C : square-matrix-Ring R n) →
    mul-square-matrix-Ring R n (mul-square-matrix-Ring R n A B) C ＝
    mul-square-matrix-Ring R n A (mul-square-matrix-Ring R n B C)
  associative-mul-square-matrix-Ring =
    associative-mul-matrix-Ring R n n n n
```

### The left identity law of square matrix multiplication

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (A : square-matrix-Ring R n)
  where

  abstract
    htpy-left-unit-law-mul-square-matrix-Ring :
      binary-htpy
        ( mul-square-matrix-Ring R n (id-matrix-Ring R n) A)
        ( A)
    htpy-left-unit-law-mul-square-matrix-Ring i j =
      equational-reasoning
        sum-fin-sequence-type-Ring R n
          ( λ k → mul-Ring R (id-matrix-Ring R n i k) (A k j))
        ＝
          sum-finite-Ring R
            ( Fin-Finite-Type n)
            ( λ k → mul-Ring R (id-matrix-Ring R n i k) (A k j))
          by inv (eq-sum-finite-sum-fin-sequence-Ring R n _)
        ＝
          sum-finite-Ring R
            ( finite-type-subset-Finite-Type
              ( Fin-Finite-Type n)
              ( decidable-standard-singleton-subtype-Discrete-Type
                ( Fin-Discrete-Type n) i))
            ( λ (k , i=k) → mul-Ring R (id-matrix-Ring R n i k) (A k j))
          by
            vanish-sum-complement-decidable-subset-finite-Ring
              ( R)
              ( Fin-Finite-Type n)
              ( decidable-standard-singleton-subtype-Discrete-Type
                ( Fin-Discrete-Type n)
                ( i))
              ( _)
              ( λ k i≠k →
                equational-reasoning
                  mul-Ring R (id-matrix-Ring R n i k) (A k j)
                  ＝ mul-Ring R (zero-Ring R) (A k j)
                    by
                      ap-mul-Ring R
                        ( ap
                          ( rec-coproduct _ _)
                          ( eq-type-Prop
                            ( is-decidable-Prop (Id-Prop (Fin-Set n) i k))
                            { y = inr (i≠k ∘ inv)}))
                        ( refl)
                  ＝ zero-Ring R
                    by left-zero-law-mul-Ring R _)
        ＝ mul-Ring R (id-matrix-Ring R n i i) (A i j)
          by sum-finite-is-contr-Ring R _ (is-torsorial-Id' i) (i , refl) _
        ＝ mul-Ring R (one-Ring R) (A i j)
          by
            ap-mul-Ring R
              ( ap
                ( rec-coproduct _ _)
                ( eq-type-Prop
                  ( is-decidable-Prop (Id-Prop (Fin-Set n) i i))
                  { y = inl refl}))
              ( refl)
        ＝ A i j
          by left-unit-law-mul-Ring R _

    left-unit-law-mul-square-matrix-Ring :
      mul-square-matrix-Ring R n (id-matrix-Ring R n) A ＝ A
    left-unit-law-mul-square-matrix-Ring =
      eq-binary-htpy _ _ htpy-left-unit-law-mul-square-matrix-Ring
```

### The right identity law of matrix multiplication

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (A : square-matrix-Ring R n)
  where

  abstract
    htpy-right-unit-law-mul-square-matrix-Ring :
      binary-htpy
        ( mul-square-matrix-Ring R n A (id-matrix-Ring R n))
        ( A)
    htpy-right-unit-law-mul-square-matrix-Ring i j =
      equational-reasoning
        sum-fin-sequence-type-Ring R
          ( n)
          ( λ k → mul-Ring R (A i k) (id-matrix-Ring R n k j))
        ＝
          sum-finite-Ring R
            ( Fin-Finite-Type n)
            ( λ k → mul-Ring R (A i k) (id-matrix-Ring R n k j))
          by inv (eq-sum-finite-sum-fin-sequence-Ring R n _)
        ＝
          sum-finite-Ring R
            ( finite-type-subset-Finite-Type
              ( Fin-Finite-Type n)
              ( decidable-standard-singleton-subtype-Discrete-Type
                ( Fin-Discrete-Type n)
                ( j)))
            ( λ (k , k=j) → mul-Ring R (A i k) (id-matrix-Ring R n k j))
          by
            vanish-sum-complement-decidable-subset-finite-Ring
              ( R)
              ( Fin-Finite-Type n)
              ( decidable-standard-singleton-subtype-Discrete-Type
                ( Fin-Discrete-Type n)
                ( j))
              ( _)
              ( λ k k≠j →
                equational-reasoning
                  mul-Ring R (A i k) (id-matrix-Ring R n k j)
                  ＝ mul-Ring R (A i k) (zero-Ring R)
                    by
                      ap-mul-Ring
                        ( R)
                        ( refl)
                        ( ap
                          ( rec-coproduct _ _)
                          ( eq-type-Prop
                            ( is-decidable-Prop (Id-Prop (Fin-Set n) k j))
                            { y = inr k≠j}))
                  ＝ zero-Ring R
                    by right-zero-law-mul-Ring R _)
        ＝ mul-Ring R (A i j) (id-matrix-Ring R n j j)
          by sum-finite-is-contr-Ring R _ (is-torsorial-Id' j) (j , refl) _
        ＝ mul-Ring R (A i j) (one-Ring R)
          by
            ap-mul-Ring
              ( R)
              ( refl)
              ( ap
                ( rec-coproduct _ _)
                ( eq-type-Prop
                  ( is-decidable-Prop (Id-Prop (Fin-Set n) j j))
                  { y = inl refl}))
        ＝ A i j
          by right-unit-law-mul-Ring R _

    right-unit-law-mul-square-matrix-Ring :
      mul-square-matrix-Ring R n A (id-matrix-Ring R n) ＝ A
    right-unit-law-mul-square-matrix-Ring =
      eq-binary-htpy _ _ htpy-right-unit-law-mul-square-matrix-Ring
```

### The monoid of matrix multiplication on a ring

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  semigroup-mul-square-matrix-Ring : Semigroup l
  semigroup-mul-square-matrix-Ring =
    ( set-square-matrix-Ring R n ,
      mul-square-matrix-Ring R n ,
      associative-mul-square-matrix-Ring R n)

  monoid-mul-square-matrix-Ring : Monoid l
  monoid-mul-square-matrix-Ring =
    ( semigroup-mul-square-matrix-Ring ,
      id-matrix-Ring R n ,
      left-unit-law-mul-square-matrix-Ring R n ,
      right-unit-law-mul-square-matrix-Ring R n)
```
