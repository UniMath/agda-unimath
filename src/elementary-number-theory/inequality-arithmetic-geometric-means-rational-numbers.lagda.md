# Inequality of arithmetic and geometric means on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.inequality-arithmetic-geometric-means-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.squares-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "arithmetic mean-geometric mean inequality" Disambiguation="on rational numbers" WD="AM-GM inequality" WDID=Q841170 Agda=leq-geometric-mean-arithmetic-mean-ℚ}}
states that $\sqrt{xy} \leq \frac{x + y}{2}$, where that square root is defined.
We cannot take arbitrary square roots in
[rational numbers](elementary-number-theory.rational-numbers.md), but we can
prove the equivalent inequality that $4xy \leq (x + y)^2$ for all rational
numbers.

### Proof

```agda
opaque
  unfolding mul-ℚ
  unfolding neg-ℚ

  eq-square-sum-minus-four-mul-ℚ-square-diff :
    (x y : ℚ) →
    square-ℚ (x +ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y) ＝ square-ℚ (x -ℚ y)
  eq-square-sum-minus-four-mul-ℚ-square-diff x y =
    equational-reasoning
      square-ℚ (x +ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y)
      ＝
        ((square-ℚ x +ℚ rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y) -ℚ
        rational-ℕ 4 *ℚ (x *ℚ y)
        by
          ap
            ( _-ℚ rational-ℕ 4 *ℚ (x *ℚ y))
            ( square-add-ℚ x y)
      ＝
        ((square-ℚ x +ℚ square-ℚ y) +ℚ
        rational-ℕ 2 *ℚ (x *ℚ y)) -ℚ
        rational-ℕ 4 *ℚ (x *ℚ y)
        by
          ap
            ( _-ℚ rational-ℕ 4 *ℚ (x *ℚ y))
            ( right-swap-add-ℚ
              ( square-ℚ x)
              ( rational-ℕ 2 *ℚ (x *ℚ y))
              ( square-ℚ y))
      ＝
        (square-ℚ x +ℚ square-ℚ y) +ℚ
        (rational-ℕ 2 *ℚ (x *ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y))
        by
          associative-add-ℚ
            ( square-ℚ x +ℚ square-ℚ y)
            ( rational-ℕ 2 *ℚ (x *ℚ y))
            ( neg-ℚ (rational-ℕ 4 *ℚ (x *ℚ y)))
      ＝
        (square-ℚ x +ℚ square-ℚ y) +ℚ
        ((rational-ℕ 2 -ℚ rational-ℕ 4) *ℚ (x *ℚ y))
        by
          ap
            ( square-ℚ x +ℚ square-ℚ y +ℚ_)
            ( inv (right-distributive-mul-diff-ℚ _ _ _))
      ＝
        (square-ℚ x +ℚ square-ℚ y) +ℚ
        (rational-ℤ (neg-ℤ (int-ℕ 2)) *ℚ (x *ℚ y))
        by
          ap
            ( square-ℚ x +ℚ square-ℚ y +ℚ_)
            ( ap
              ( _*ℚ (x *ℚ y))
              (diff-rational-ℤ _ _))
      ＝
        (square-ℚ x +ℚ square-ℚ y) -ℚ
        (rational-ℕ 2 *ℚ (x *ℚ y))
        by
          ap
            ( square-ℚ x +ℚ square-ℚ y +ℚ_)
            ( left-negative-law-mul-ℚ _ _)
      ＝ square-ℚ x -ℚ (rational-ℕ 2 *ℚ (x *ℚ y)) +ℚ square-ℚ y
        by
          right-swap-add-ℚ
            ( square-ℚ x)
            ( square-ℚ y)
            ( neg-ℚ (rational-ℕ 2 *ℚ (x *ℚ y)))
      ＝ square-ℚ (x -ℚ y) by inv (square-diff-ℚ x y)

  leq-geometric-mean-arithmetic-mean-ℚ :
    (x y : ℚ) →
    leq-ℚ (rational-ℕ 4 *ℚ (x *ℚ y)) (square-ℚ (x +ℚ y))
  leq-geometric-mean-arithmetic-mean-ℚ x y =
    leq-is-nonnegative-diff-ℚ
      ( rational-ℕ 4 *ℚ (x *ℚ y))
      ( square-ℚ (x +ℚ y))
      ( inv-tr
        ( is-nonnegative-ℚ)
        ( eq-square-sum-minus-four-mul-ℚ-square-diff x y)
        ( is-nonnegative-square-ℚ (x -ℚ y)))
```

### The arithmetic and geometric means of `x` and `y` are equal if and only if `x = y`

```agda
abstract
  eq-eq-geometric-mean-arithmetic-mean-ℚ :
    (x y : ℚ) → rational-ℕ 4 *ℚ (x *ℚ y) ＝ square-ℚ (x +ℚ y) → x ＝ y
  eq-eq-geometric-mean-arithmetic-mean-ℚ x y 4xy=⟨x+y⟩² =
    eq-is-zero-diff-ℚ
      ( x)
      ( y)
      ( is-zero-square-is-zero-ℚ
        ( x -ℚ y)
        ( equational-reasoning
          square-ℚ (x -ℚ y)
          ＝ square-ℚ (x +ℚ y) -ℚ rational-ℕ 4 *ℚ (x *ℚ y)
            by inv (eq-square-sum-minus-four-mul-ℚ-square-diff x y)
          ＝ zero-ℚ by is-zero-diff-ℚ (inv 4xy=⟨x+y⟩²)))

  eq-geometric-mean-arithmetic-mean-eq-ℚ :
    (x y : ℚ) → x ＝ y → rational-ℕ 4 *ℚ (x *ℚ y) ＝ square-ℚ (x +ℚ y)
  eq-geometric-mean-arithmetic-mean-eq-ℚ x .x refl =
    inv
      ( equational-reasoning
        square-ℚ (x +ℚ x)
        ＝ square-ℚ (rational-ℕ 2 *ℚ x) by ap square-ℚ (inv (mul-two-ℚ x))
        ＝ square-ℚ (rational-ℕ 2) *ℚ square-ℚ x
          by distributive-square-mul-ℚ _ _
        ＝ rational-ℕ 4 *ℚ square-ℚ x
          by ap (_*ℚ square-ℚ x) (mul-rational-ℕ 2 2))

  eq-geometric-mean-arithmetic-mean-iff-eq-ℚ :
    (x y : ℚ) → (rational-ℕ 4 *ℚ (x *ℚ y) ＝ square-ℚ (x +ℚ y)) ↔ (x ＝ y)
  pr1 (eq-geometric-mean-arithmetic-mean-iff-eq-ℚ x y) =
    eq-eq-geometric-mean-arithmetic-mean-ℚ x y
  pr2 (eq-geometric-mean-arithmetic-mean-iff-eq-ℚ x y) =
    eq-geometric-mean-arithmetic-mean-eq-ℚ x y
```
