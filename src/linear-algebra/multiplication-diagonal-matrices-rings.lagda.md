# Multiplication by diagonal matrices over rings

```agda
module linear-algebra.multiplication-diagonal-matrices-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.diagonal-matrices-on-rings
open import linear-algebra.finite-sequences-in-rings
open import linear-algebra.indicator-finite-sequences-in-rings
open import linear-algebra.matrices-on-rings
open import linear-algebra.multiplication-matrices-on-rings
open import linear-algebra.transposition-matrices

open import ring-theory.rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [diagonal matrix](linear-algebra.diagonal-matrices-on-rings.md) `M` on a
[ring](ring-theory.rings.md) `R` with diagonal `d`, `MN` is `N` with row `i`
multiplied by `dᵢ`, and `NM` is `N` with column `j` multiplied by `dⱼ`.

## Properties

### The row at index `i` of a diagonal matrix with diagonal `d` is `dᵢ * χᵢ`

```agda
module _
  {l : Level}
  (R : Ring l)
  (n : ℕ)
  (d : fin-sequence-type-Ring R n)
  where abstract

  htpy-row-matrix-from-diagonal-fin-sequence-type-Ring :
    (i : Fin n) →
    matrix-from-diagonal-fin-sequence-type-Ring R n d i ~
    scalar-mul-fin-sequence-type-Ring R n
      ( d i)
      ( indicator-fin-sequence-type-Ring R n i)
  htpy-row-matrix-from-diagonal-fin-sequence-type-Ring i j
    with has-decidable-equality-Fin n i j
  ... | inl i=j =
    inv (right-unit-law-mul-Ring R (d i))
  ... | inr i≠j =
    inv (right-zero-law-mul-Ring R (d i))
```

### Left multiplication by a diagonal matrix with diagonal `d` multiplies row `i` by `dᵢ`

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  (d : fin-sequence-type-Ring R m)
  where abstract

  compute-left-mul-diagonal-matrix-Ring :
    (M : matrix-Ring R m n) (i : Fin m) (j : Fin n) →
    mul-matrix-Ring R m m n
      ( matrix-from-diagonal-fin-sequence-type-Ring R m d)
      ( M)
      ( i)
      ( j) ＝
    mul-Ring R (d i) (M i j)
  compute-left-mul-diagonal-matrix-Ring M i j =
    equational-reasoning
      sum-fin-sequence-type-Ring R m
        ( λ k →
          mul-Ring R
            ( matrix-from-diagonal-fin-sequence-type-Ring R m d i k)
            ( M k j))
      ＝
        sum-fin-sequence-type-Ring R m
          ( λ k →
            mul-Ring R
              ( mul-Ring R
                ( d i)
                ( indicator-fin-sequence-type-Ring R m i k))
              ( M k j))
        by
          htpy-sum-fin-sequence-type-Ring R m
            ( λ k →
              ap-mul-Ring R
                ( htpy-row-matrix-from-diagonal-fin-sequence-type-Ring R
                  ( m)
                  ( d)
                  ( i)
                  ( k))
                ( refl))
      ＝
        sum-fin-sequence-type-Ring R m
          ( λ k →
            mul-Ring R
              ( d i)
              ( mul-Ring R
                ( indicator-fin-sequence-type-Ring R m i k)
                ( M k j)))
        by
          htpy-sum-fin-sequence-type-Ring R m
            ( λ k → associative-mul-Ring R _ _ _)
      ＝
        mul-Ring R
          ( d i)
          ( sum-fin-sequence-type-Ring R m
            ( λ k →
              mul-Ring R
                ( indicator-fin-sequence-type-Ring R m i k)
                ( M k j)))
        by inv (left-distributive-mul-sum-fin-sequence-type-Ring R m _ _)
      ＝ mul-Ring R (d i) (M i j)
        by
          ap-mul-Ring R
            ( refl)
            ( left-dot-product-indicator-fin-sequence-type-Ring R m i
              ( transpose-matrix m n M j))
```

### Right multiplication by a diagonal matrix with diagonal `d` multiplies column `j` by `dⱼ`

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n : ℕ)
  (d : fin-sequence-type-Ring R n)
  where abstract

  compute-right-mul-diagonal-matrix-Ring :
    (M : matrix-Ring R m n) (i : Fin m) (j : Fin n) →
    mul-matrix-Ring R m n n
      ( M)
      ( matrix-from-diagonal-fin-sequence-type-Ring R n d)
      ( i)
      ( j) ＝
    mul-Ring R (M i j) (d j)
  compute-right-mul-diagonal-matrix-Ring M i j =
    equational-reasoning
      sum-fin-sequence-type-Ring R n
        ( λ k →
          mul-Ring R
            ( M i k)
            ( matrix-from-diagonal-fin-sequence-type-Ring R n d k j))
      ＝
        sum-fin-sequence-type-Ring R n
          ( λ k →
            mul-Ring R
              ( M i k)
              ( matrix-from-diagonal-fin-sequence-type-Ring R n d j k))
        by
          htpy-sum-fin-sequence-type-Ring R n
            ( λ k →
              ap-mul-Ring R
                ( refl)
                ( is-symmetric-matrix-from-diagonal-fin-sequence-type-Ring
                  ( R)
                  ( n)
                  ( d)
                  ( j)
                  ( k)))
      ＝
        sum-fin-sequence-type-Ring R n
          ( λ k →
            mul-Ring R
              ( M i k)
              ( mul-Ring R
                ( d j)
                ( indicator-fin-sequence-type-Ring R n j k)))
        by
          htpy-sum-fin-sequence-type-Ring R n
            ( λ k →
              ap-mul-Ring R
                ( refl)
                ( htpy-row-matrix-from-diagonal-fin-sequence-type-Ring
                  ( R)
                  ( n)
                  ( d)
                  ( j)
                  ( k)))
      ＝
        sum-fin-sequence-type-Ring R n
          ( λ k →
            mul-Ring R
              ( mul-Ring R (M i k) (d j))
              ( indicator-fin-sequence-type-Ring R n j k))
        by
          htpy-sum-fin-sequence-type-Ring R n
            ( λ k → inv (associative-mul-Ring R _ _ _))
      ＝ mul-Ring R (M i j) (d j)
        by right-dot-product-indicator-fin-sequence-type-Ring R n j _
```
