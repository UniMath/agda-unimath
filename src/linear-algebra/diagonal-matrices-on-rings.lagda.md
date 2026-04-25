# Diagonal rings on matrices

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.diagonal-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.diagonals-of-square-matrices
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.square-matrices-on-rings

open import ring-theory.rings

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "diagonal matrix" Disambiguation="on a ring" WD="diagonal matrix" WDID=Q332791 Agda=diagonal-matrix-Ring}}
on a [ring](ring-theory.rings.md) is a
[square matrix](linear-algebra.square-matrices-on-rings.md) `A` where if `i` is
[not equal to](foundation.negated-equality.md) `j`, then `Aᵢⱼ` is zero.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  is-diagonal-prop-square-matrix-Ring : square-matrix-Ring R n → Prop l
  is-diagonal-prop-square-matrix-Ring A =
    Π-Prop
      ( Fin n)
      ( λ i →
        Π-Prop (Fin n) (λ j → nonequal-Prop i j ⇒ is-zero-ring-Prop R (A i j)))

  is-diagonal-square-matrix-Ring : square-matrix-Ring R n → UU l
  is-diagonal-square-matrix-Ring =
    is-in-subtype is-diagonal-prop-square-matrix-Ring

  diagonal-matrix-Ring : UU l
  diagonal-matrix-Ring = type-subtype is-diagonal-prop-square-matrix-Ring

  matrix-diagonal-matrix-Ring : diagonal-matrix-Ring → square-matrix-Ring R n
  matrix-diagonal-matrix-Ring = pr1
```

### Constructing a diagonal matrix from the finite sequence of elements on the diagonal

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  matrix-from-diagonal-fin-sequence-type-Ring :
    fin-sequence-type-Ring R n → square-matrix-Ring R n
  matrix-from-diagonal-fin-sequence-type-Ring u i j =
    rec-coproduct
      ( λ i=j → u i)
      ( λ i≠j → zero-Ring R)
      ( has-decidable-equality-Fin n i j)
```

## Properties

### A matrix constructed from its diagonal is diagonal

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  abstract
    is-diagonal-matrix-from-diagonal-fin-sequence-type-Ring :
      (u : fin-sequence-type-Ring R n) →
      is-diagonal-square-matrix-Ring R n
        ( matrix-from-diagonal-fin-sequence-type-Ring R n u)
    is-diagonal-matrix-from-diagonal-fin-sequence-type-Ring u i j i≠j =
      ap
        ( rec-coproduct _ _)
        ( eq-is-prop' (is-prop-is-decidable (is-set-Fin n i j)) _ (inr i≠j))

  diagonal-matrix-fin-sequence-type-Ring :
    (u : fin-sequence-type-Ring R n) →
    diagonal-matrix-Ring R n
  diagonal-matrix-fin-sequence-type-Ring u =
    ( matrix-from-diagonal-fin-sequence-type-Ring R n u ,
      is-diagonal-matrix-from-diagonal-fin-sequence-type-Ring u)
```

### The diagonal of a matrix constructed from its diagonal is the original sequence

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  abstract
    htpy-diagonal-matrix-from-diagonal-fin-sequence-type-Ring :
      (u : fin-sequence-type-Ring R n) →
      diagonal-square-matrix n
        ( matrix-from-diagonal-fin-sequence-type-Ring R n u) ~
      u
    htpy-diagonal-matrix-from-diagonal-fin-sequence-type-Ring u i =
      ap
        ( rec-coproduct _ _)
        ( eq-is-prop' (is-prop-is-decidable (is-set-Fin n i i)) _ (inl refl))

    diagonal-matrix-from-diagonal-fin-sequence-type-Ring :
      (u : fin-sequence-type-Ring R n) →
      diagonal-square-matrix n
        ( matrix-from-diagonal-fin-sequence-type-Ring R n u) ＝
      u
    diagonal-matrix-from-diagonal-fin-sequence-type-Ring u =
      eq-htpy (htpy-diagonal-matrix-from-diagonal-fin-sequence-type-Ring u)
```

### If a matrix is diagonal, it is equal to the diagonal matrix constructed from its diagonal

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (A : square-matrix-Ring R n)
  (D : is-diagonal-square-matrix-Ring R n A)
  where

  abstract
    htpy-diagonal-matrix-diagonal-square-matrix-Ring :
      binary-htpy
        ( matrix-from-diagonal-fin-sequence-type-Ring R n
          ( diagonal-square-matrix n A))
        ( A)
    htpy-diagonal-matrix-diagonal-square-matrix-Ring i j
      with has-decidable-equality-Fin n i j
    ... | inl i=j = ap (A i) i=j
    ... | inr i≠j = inv (D i j i≠j)

    diagonal-matrix-diagonal-square-matrix-Ring :
      matrix-from-diagonal-fin-sequence-type-Ring R n
        ( diagonal-square-matrix n A) ＝
      A
    diagonal-matrix-diagonal-square-matrix-Ring =
      eq-binary-htpy _ _ htpy-diagonal-matrix-diagonal-square-matrix-Ring
```

### The type of diagonal `n × n` matrices is equivalent to the type of finite sequences of length `n`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  where

  is-equiv-matrix-from-diagonal-fin-sequence-type-Ring :
    is-equiv
      ( diagonal-matrix-fin-sequence-type-Ring R n)
  is-equiv-matrix-from-diagonal-fin-sequence-type-Ring =
    is-equiv-is-invertible
      ( diagonal-square-matrix n ∘ pr1)
      ( λ (A , D) →
        eq-type-subtype
          ( is-diagonal-prop-square-matrix-Ring R n)
          ( diagonal-matrix-diagonal-square-matrix-Ring R n A D))
      ( diagonal-matrix-from-diagonal-fin-sequence-type-Ring R n)

  equiv-diagonal-matrix-fin-sequence-type-Ring :
    fin-sequence-type-Ring R n ≃ diagonal-matrix-Ring R n
  equiv-diagonal-matrix-fin-sequence-type-Ring =
    ( diagonal-matrix-fin-sequence-type-Ring R n ,
      is-equiv-matrix-from-diagonal-fin-sequence-type-Ring)
```
