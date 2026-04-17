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

### Left distributivity of matrix multiplication over addition

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n p : ℕ)
  (A : matrix-Ring R m n)
  (B C : matrix-Ring R n p)
  where

  abstract
    htpy-left-distributive-mul-add-matrix-Ring :
      binary-htpy
        ( mul-matrix-Ring R m n p A (add-matrix-Ring R n p B C))
        ( add-matrix-Ring R m p
          ( mul-matrix-Ring R m n p A B)
          ( mul-matrix-Ring R m n p A C))
    htpy-left-distributive-mul-add-matrix-Ring i k =
      ( htpy-sum-fin-sequence-type-Ring R
        ( n)
        ( λ j → left-distributive-mul-add-Ring R _ _ _)) ∙
      ( inv (interchange-add-sum-fin-sequence-type-Ring R n _ _))

    left-distributive-mul-add-matrix-Ring :
      mul-matrix-Ring R m n p A (add-matrix-Ring R n p B C) ＝
      add-matrix-Ring R m p
        ( mul-matrix-Ring R m n p A B)
        ( mul-matrix-Ring R m n p A C)
    left-distributive-mul-add-matrix-Ring =
      eq-binary-htpy _ _ htpy-left-distributive-mul-add-matrix-Ring
```

### Right distributivity of matrix multiplication over addition

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n p : ℕ)
  (A B : matrix-Ring R m n)
  (C : matrix-Ring R n p)
  where

  abstract
    htpy-right-distributive-mul-add-matrix-Ring :
      binary-htpy
        ( mul-matrix-Ring R m n p (add-matrix-Ring R m n A B) C)
        ( add-matrix-Ring R m p
          ( mul-matrix-Ring R m n p A C)
          ( mul-matrix-Ring R m n p B C))
    htpy-right-distributive-mul-add-matrix-Ring i k =
      ( htpy-sum-fin-sequence-type-Ring R
        ( n)
        ( λ j → right-distributive-mul-add-Ring R _ _ _)) ∙
      ( inv (interchange-add-sum-fin-sequence-type-Ring R n _ _))

    right-distributive-mul-add-matrix-Ring :
      mul-matrix-Ring R m n p (add-matrix-Ring R m n A B) C ＝
      add-matrix-Ring R m p
        ( mul-matrix-Ring R m n p A C)
        ( mul-matrix-Ring R m n p B C)
    right-distributive-mul-add-matrix-Ring =
      eq-binary-htpy _ _ htpy-right-distributive-mul-add-matrix-Ring
```

### `(cA)B = c(AB)`

```agda
module _
  {l : Level}
  (R : Ring l)
  (m n p : ℕ)
  (r : type-Ring R)
  (A : matrix-Ring R m n)
  (B : matrix-Ring R n p)
  where

  abstract
    htpy-associative-scalar-mul-mul-matrix-Ring :
      binary-htpy
        ( mul-matrix-Ring R m n p (scalar-mul-matrix-Ring R m n r A) B)
        ( scalar-mul-matrix-Ring R m p r (mul-matrix-Ring R m n p A B))
    htpy-associative-scalar-mul-mul-matrix-Ring i k =
      ( htpy-sum-fin-sequence-type-Ring R n
        ( λ j → associative-mul-Ring R r _ _)) ∙
      ( inv (left-distributive-mul-sum-fin-sequence-type-Ring R n r _))

    associative-scalar-mul-mul-matrix-Ring :
      mul-matrix-Ring R m n p (scalar-mul-matrix-Ring R m n r A) B ＝
      scalar-mul-matrix-Ring R m p r (mul-matrix-Ring R m n p A B)
    associative-scalar-mul-mul-matrix-Ring =
      eq-binary-htpy _ _ htpy-associative-scalar-mul-mul-matrix-Ring
```

## See also

- [Multiplication of square matrices on rings](linear-algebra.multiplication-square-matrices-on-rings.md)
