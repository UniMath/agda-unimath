# Multiplying matrices and finite sequences on commutative rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.multiplication-matrices-finite-sequences-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.column-matrices
open import linear-algebra.column-matrices-on-commutative-rings
open import linear-algebra.finite-sequences-in-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
open import linear-algebra.matrices-on-commutative-rings
open import linear-algebra.multiplication-matrices-finite-sequences-rings
open import linear-algebra.sums-of-finite-sequences-of-elements-left-modules-commutative-rings

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The product of an `m × n`
[matrix](linear-algebra.matrices-on-commutative-rings.md) on a
[commutative ring](commutative-algebra.commutative-rings.md) `R` and a
[finite sequence](linear-algebra.finite-sequences-in-commutative-rings.md) `v`
of length `n` in `R` is the `m`-element finite sequence `w` defined as
`wᵢ ≔ ∑ⱼ Mᵢⱼ vⱼ`.

## Definition

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  where

  mul-matrix-fin-sequence-type-Commutative-Ring :
    matrix-Commutative-Ring R m n →
    fin-sequence-type-Commutative-Ring R n →
    fin-sequence-type-Commutative-Ring R m
  mul-matrix-fin-sequence-type-Commutative-Ring =
    mul-matrix-fin-sequence-type-Ring (ring-Commutative-Ring R) m n
```

### Multiplication by a matrix is a linear map

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  (M : matrix-Commutative-Ring R m n)
  (let _+R_ = add-Commutative-Ring R)
  (let _*R_ = mul-Commutative-Ring R)
  where

  abstract
    is-additive-mul-matrix-fin-sequence-type-Commutative-Ring :
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( left-module-fin-sequence-Commutative-Ring R n)
        ( left-module-fin-sequence-Commutative-Ring R m)
        ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
    is-additive-mul-matrix-fin-sequence-type-Commutative-Ring u v =
      eq-htpy
        ( λ i →
          ( htpy-sum-fin-sequence-type-Commutative-Ring R n
            ( λ j →
              left-distributive-mul-add-Commutative-Ring
                ( R)
                ( M i j)
                ( u j)
                ( v j))) ∙
          ( inv
            ( interchange-add-sum-fin-sequence-type-Commutative-Ring R n _ _)))

    is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring :
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( left-module-fin-sequence-Commutative-Ring R n)
        ( left-module-fin-sequence-Commutative-Ring R m)
        ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
    is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring c v =
      eq-htpy
        ( λ i →
          ( htpy-sum-fin-sequence-type-Commutative-Ring R n
            ( λ j → left-swap-mul-Commutative-Ring R (M i j) c (v j))) ∙
          ( inv
            ( left-distributive-mul-sum-fin-sequence-type-Commutative-Ring
              ( R)
              ( n)
              ( c)
              ( _))))

  is-linear-mul-matrix-fin-sequence-type-Commutative-Ring :
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( left-module-fin-sequence-Commutative-Ring R m)
      ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M)
  is-linear-mul-matrix-fin-sequence-type-Commutative-Ring =
    ( is-additive-mul-matrix-fin-sequence-type-Commutative-Ring ,
      is-homogeneous-mul-matrix-fin-sequence-type-Commutative-Ring)

  linear-map-mul-matrix-fin-sequence-type-Commutative-Ring :
    linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( left-module-fin-sequence-Commutative-Ring R m)
  linear-map-mul-matrix-fin-sequence-type-Commutative-Ring =
    ( mul-matrix-fin-sequence-type-Commutative-Ring R m n M ,
      is-linear-mul-matrix-fin-sequence-type-Commutative-Ring)
```

### Every linear map from `Mⁿ → Mᵐ` is homotopic to a multiplication by an `m × n` matrix

```agda
module _
  {l : Level}
  (R : Commutative-Ring l)
  (m n : ℕ)
  (f :
    linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( left-module-fin-sequence-Commutative-Ring R m))
  where

  matrix-linear-map-left-module-fin-sequence-Commutative-Ring :
    matrix-Commutative-Ring R m n
  matrix-linear-map-left-module-fin-sequence-Commutative-Ring i j =
    map-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-fin-sequence-Commutative-Ring R n)
      ( left-module-fin-sequence-Commutative-Ring R m)
      ( f)
      ( indicator-fin-sequence-type-Commutative-Ring R n j)
      ( i)

  abstract
    binary-htpy-mul-matrix-map-linear-map-left-module-fin-sequence-Commutative-Ring :
      binary-htpy
        ( mul-matrix-fin-sequence-type-Commutative-Ring R
          ( m)
          ( n)
          ( matrix-linear-map-left-module-fin-sequence-Commutative-Ring))
        ( map-linear-map-left-module-Commutative-Ring R
          ( left-module-fin-sequence-Commutative-Ring R n)
          ( left-module-fin-sequence-Commutative-Ring R m)
          ( f))
    binary-htpy-mul-matrix-map-linear-map-left-module-fin-sequence-Commutative-Ring
      v i =
      equational-reasoning
        sum-fin-sequence-type-Commutative-Ring R n
          ( λ j → mul-Commutative-Ring R
            ( matrix-linear-map-left-module-fin-sequence-Commutative-Ring i j)
            ( v j))
        ＝
          sum-fin-sequence-type-Commutative-Ring R n
            ( λ j →
              mul-Commutative-Ring R
                ( v j)
                ( map-linear-map-left-module-Commutative-Ring
                  ( R)
                  ( left-module-fin-sequence-Commutative-Ring R n)
                  ( left-module-fin-sequence-Commutative-Ring R m)
                  ( f)
                  ( indicator-fin-sequence-type-Commutative-Ring R n j)
                  ( i)))
          by
            htpy-sum-fin-sequence-type-Commutative-Ring R n
              ( λ j → commutative-mul-Commutative-Ring R _ _)
        ＝
          sum-fin-sequence-type-Commutative-Ring R n
            ( λ j →
              map-linear-map-left-module-Commutative-Ring
                ( R)
                ( left-module-fin-sequence-Commutative-Ring R n)
                ( left-module-fin-sequence-Commutative-Ring R m)
                ( f)
                ( scalar-mul-fin-sequence-type-Commutative-Ring R n
                  ( v j)
                  ( indicator-fin-sequence-type-Commutative-Ring R n j))
                ( i))
          by
            htpy-sum-fin-sequence-type-Commutative-Ring R n
              ( λ j →
                ap
                  ( ev i)
                  ( inv
                    ( is-homogeneous-map-linear-map-left-module-Commutative-Ring
                      ( R)
                      ( left-module-fin-sequence-Commutative-Ring R n)
                      ( left-module-fin-sequence-Commutative-Ring R m)
                      ( f)
                      ( v j)
                      ( indicator-fin-sequence-type-Commutative-Ring R n j))))
        ＝
          sum-fin-sequence-type-left-module-Commutative-Ring
            ( R)
            ( left-module-fin-sequence-Commutative-Ring R m)
            ( n)
            ( λ j →
              map-linear-map-left-module-Commutative-Ring
                ( R)
                ( left-module-fin-sequence-Commutative-Ring R n)
                ( left-module-fin-sequence-Commutative-Ring R m)
                ( f)
                ( scalar-mul-fin-sequence-type-Commutative-Ring R n
                  ( v j)
                  ( indicator-fin-sequence-type-Commutative-Ring R n j)))
            ( i)
            by
              inv
                ( coordinate-sum-fin-sequence-fin-sequence-type-Commutative-Ring
                  ( R)
                  ( n)
                  ( m)
                  ( i)
                  ( _))
        ＝
          map-linear-map-left-module-Commutative-Ring
            ( R)
            ( left-module-fin-sequence-Commutative-Ring R n)
            ( left-module-fin-sequence-Commutative-Ring R m)
            ( f)
            ( sum-fin-sequence-type-left-module-Commutative-Ring
              ( R)
              ( left-module-fin-sequence-Commutative-Ring R n)
              ( n)
              ( λ j →
                scalar-mul-fin-sequence-type-Commutative-Ring R n
                  ( v j)
                  ( indicator-fin-sequence-type-Commutative-Ring R n j)))
            ( i)
          by
            ap
              ( ev i)
              ( inv
                ( distributive-map-linear-map-sum-fin-sequence-type-left-module-Commutative-Ring
                  ( R)
                  ( left-module-fin-sequence-Commutative-Ring R n)
                  ( left-module-fin-sequence-Commutative-Ring R m)
                  ( f)
                  ( n)
                  ( _)))
        ＝
          map-linear-map-left-module-Commutative-Ring
            ( R)
            ( left-module-fin-sequence-Commutative-Ring R n)
            ( left-module-fin-sequence-Commutative-Ring R m)
            ( f)
            ( v)
            ( i)
          by
            ap
              ( λ w → map-linear-map-left-module-Commutative-Ring R _ _ f w i)
              ( eq-linear-combination-indicator-fin-sequence-type-Commutative-Ring
                ( R)
                ( n)
                ( v))

    htpy-mul-matrix-linear-map-left-module-fin-sequence-Commutative-Ring :
      htpy-linear-map-left-module-Commutative-Ring
        ( R)
        ( left-module-fin-sequence-Commutative-Ring R n)
        ( left-module-fin-sequence-Commutative-Ring R m)
        ( linear-map-mul-matrix-fin-sequence-type-Commutative-Ring R m n
          ( matrix-linear-map-left-module-fin-sequence-Commutative-Ring))
        ( f)
    htpy-mul-matrix-linear-map-left-module-fin-sequence-Commutative-Ring v =
      eq-htpy
        ( binary-htpy-mul-matrix-map-linear-map-left-module-fin-sequence-Commutative-Ring
          ( v))
```
