# Multiplication of matrices on rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.multiplication-matrices-on-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import linear-algebra.matrices-on-rings

open import ring-theory.rings
open import ring-theory.sums-of-finite-families-of-elements-rings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.finite-types
```

</details>

## Idea

In a [ring](ring-theory.rings.md) `R`, the
{{#concept "product" Disambiguation="of two matrices over a ring" Agda=mul-matrix-Ring}}
of an `m × n` [matrix](linear-algebra.matrices-on-rings.md) `A` and an `n × p`
matrix `B` is the `m × p` matrix defined by `(AB)ᵢₖ = ∑ⱼ AᵢⱼBⱼₖ`.

## Definition

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n p : ℕ)
  where

  mul-matrix-Ring :
    matrix-Ring R m n → matrix-Ring R n p → matrix-Ring R m p
  mul-matrix-Ring A B i k =
    sum-fin-sequence-type-Ring R
      ( n)
      ( λ j → mul-Ring R (A i j) (B j k))
```

## Properties

### Multiplication of matrices is associative

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n p q : ℕ)
  where

  abstract
    htpy-associative-mul-matrix-Ring :
      (A : matrix-Ring R m n)
      (B : matrix-Ring R n p)
      (C : matrix-Ring R p q) →
      binary-htpy
        ( mul-matrix-Ring R m p q (mul-matrix-Ring R m n p A B) C)
        ( mul-matrix-Ring R m n q A (mul-matrix-Ring R n p q B C))
    htpy-associative-mul-matrix-Ring A B C i j =
      equational-reasoning
        sum-fin-sequence-type-Ring R
          ( p)
          ( λ a →
            mul-Ring R
              ( sum-fin-sequence-type-Ring R
                ( n)
                ( λ b → mul-Ring R (A i b) (B b a)))
              ( C a j))
        ＝
          sum-fin-sequence-type-Ring R
            ( p)
            ( λ a →
              sum-finite-Ring R
                ( Fin-Finite-Type n)
                ( λ b → mul-Ring R (A i b) (mul-Ring R (B b a) (C a j))))
          by
            htpy-sum-fin-sequence-type-Ring R
              ( p)
              ( λ a →
                ( right-distributive-mul-sum-fin-sequence-type-Ring R n _ _) ∙
                ( htpy-sum-fin-sequence-type-Ring R n
                  ( λ b → associative-mul-Ring R _ _ _)) ∙
                ( inv (eq-sum-finite-sum-fin-sequence-Ring R n _)))
        ＝
          sum-finite-Ring R
            ( Fin-Finite-Type p)
            ( λ a →
              sum-finite-Ring R
                ( Fin-Finite-Type n)
                ( λ b → mul-Ring R (A i b) (mul-Ring R (B b a) (C a j))))
          by inv (eq-sum-finite-sum-fin-sequence-Ring R p _)
        ＝
          sum-finite-Ring R
            ( Fin-Finite-Type n)
            ( λ b →
              sum-finite-Ring R
                ( Fin-Finite-Type p)
                ( λ a → mul-Ring R (A i b) (mul-Ring R (B b a) (C a j))))
          by interchange-sum-sum-finite-Ring R _ _ _
        ＝
          sum-finite-Ring R
            ( Fin-Finite-Type n)
            ( λ b →
              mul-Ring R
                ( A i b)
                ( mul-matrix-Ring R n p q B C b j))
          by
            htpy-sum-finite-Ring R _
              ( λ b →
                ( eq-sum-finite-sum-fin-sequence-Ring R p _) ∙
                ( inv
                  ( left-distributive-mul-sum-fin-sequence-type-Ring R p _ _)))
        ＝
          mul-matrix-Ring R m n q
            ( A)
            ( mul-matrix-Ring R n p q B C)
            ( i)
            ( j)
          by eq-sum-finite-sum-fin-sequence-Ring R n _

    associative-mul-matrix-Ring :
      (A : matrix-Ring R m n)
      (B : matrix-Ring R n p)
      (C : matrix-Ring R p q) →
      mul-matrix-Ring R m p q (mul-matrix-Ring R m n p A B) C ＝
      mul-matrix-Ring R m n q A (mul-matrix-Ring R n p q B C)
    associative-mul-matrix-Ring A B C =
      eq-binary-htpy _ _
        ( htpy-associative-mul-matrix-Ring A B C)
```

## See also

- [Multiplication of square matrices on rings](linear-algebra.multiplication-square-matrices-on-rings.md)
