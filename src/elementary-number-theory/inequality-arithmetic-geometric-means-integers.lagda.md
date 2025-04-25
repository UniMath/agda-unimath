# Inequality of arithmetic and geometric means on the integers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.inequality-arithmetic-geometric-means-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.squares-integers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "arithmetic mean-geometric mean inequality" Disambiguation="on integers" WD="AM-GM inequality" WDID=Q841170 Agda=leq-arithmetic-mean-geometric-mean-ℤ}}
states that $\sqrt{xy} \leq \frac{x + y}{2}$. We cannot take arbitrary square
roots in integers, but we can prove the equivalent inequality that
$4xy \leq (x + y)^2$.

## Proof

```agda
abstract
  leq-arithmetic-mean-geometric-mean-ℤ :
    (x y : ℤ) →
    leq-ℤ (int-ℕ 4 *ℤ (x *ℤ y)) (square-ℤ (x +ℤ y))
  leq-arithmetic-mean-geometric-mean-ℤ x y =
    inv-tr
      ( is-nonnegative-ℤ)
      ( equational-reasoning
        square-ℤ (x +ℤ y) -ℤ (int-ℕ 4 *ℤ (x *ℤ y))
        ＝
          (square-ℤ x +ℤ (int-ℕ 2 *ℤ (x *ℤ y)) +ℤ square-ℤ y) -ℤ
          (int-ℕ 4 *ℤ (x *ℤ y))
          by ap (_-ℤ int-ℕ 4 *ℤ (x *ℤ y)) (square-add-ℤ x y)
        ＝
          (square-ℤ x +ℤ square-ℤ y +ℤ (int-ℕ 2 *ℤ (x *ℤ y))) +ℤ
          (neg-ℤ (int-ℕ 4) *ℤ (x *ℤ y))
          by
            ap-add-ℤ
              ( right-swap-add-ℤ
                ( square-ℤ x)
                ( int-ℕ 2 *ℤ (x *ℤ y))
                ( square-ℤ y))
              ( inv (left-negative-law-mul-ℤ _ _))
        ＝
          (square-ℤ x +ℤ square-ℤ y) +ℤ
          (int-ℕ 2 *ℤ (x *ℤ y) +ℤ neg-ℤ (int-ℕ 4) *ℤ (x *ℤ y))
          by associative-add-ℤ _ _ _
        ＝
          (square-ℤ x +ℤ square-ℤ y) +ℤ
          (neg-ℤ (int-ℕ 2) *ℤ (x *ℤ y))
          by
            ap
              ( square-ℤ x +ℤ square-ℤ y +ℤ_)
              ( inv
                ( right-distributive-mul-add-ℤ
                  ( int-ℕ 2)
                  ( neg-ℤ (int-ℕ 4))
                  ( x *ℤ y)))
        ＝ (square-ℤ x +ℤ square-ℤ y) -ℤ (int-ℕ 2 *ℤ (x *ℤ y))
          by
            ap
              ( square-ℤ x +ℤ square-ℤ y +ℤ_)
              ( left-negative-law-mul-ℤ _ (x *ℤ y))
        ＝ square-ℤ x -ℤ int-ℕ 2 *ℤ (x *ℤ y) +ℤ square-ℤ y
          by right-swap-add-ℤ _ _ _
        ＝ square-ℤ (x -ℤ y) by inv (square-diff-ℤ x y))
      ( is-nonnegative-square-ℤ (x -ℤ y))
```
