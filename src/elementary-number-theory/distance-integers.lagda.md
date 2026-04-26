# The distance between integers

```agda
module elementary-number-theory.distance-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.difference-integers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.identity-types
```

</details>

## Idea

The
{{#concept "distance function" Disambiguation="between integers" Agda=dist-ℤ}}
between [integers](elementary-number-theory.integers.md) measures how far two
integers are apart.

## Definition

```agda
dist-ℤ : ℤ → ℤ → ℕ
dist-ℤ x y = abs-ℤ (x -ℤ y)

ap-dist-ℤ :
  {x x' y y' : ℤ} → x ＝ x' → y ＝ y' → dist-ℤ x y ＝ dist-ℤ x' y'
ap-dist-ℤ p q = ap-binary dist-ℤ p q
```

## Properties

### Zero laws

```agda
abstract
  left-zero-law-dist-ℤ : (x : ℤ) → dist-ℤ zero-ℤ x ＝ abs-ℤ x
  left-zero-law-dist-ℤ x = ap abs-ℤ (left-zero-law-diff-ℤ x) ∙ abs-neg-ℤ x

  right-zero-law-dist-ℤ : (x : ℤ) → dist-ℤ x zero-ℤ ＝ abs-ℤ x
  right-zero-law-dist-ℤ x = ap abs-ℤ (right-zero-law-diff-ℤ x)
```

### The canonical embedding of natural numbers into the integers preserves distance

```agda
abstract
  dist-int-ℕ :
    (x y : ℕ) → dist-ℤ (int-ℕ x) (int-ℕ y) ＝ dist-ℕ x y
  dist-int-ℕ zero-ℕ zero-ℕ = refl
  dist-int-ℕ zero-ℕ (succ-ℕ y) = left-zero-law-dist-ℤ (int-ℕ (succ-ℕ y))
  dist-int-ℕ (succ-ℕ x) zero-ℕ = right-zero-law-dist-ℤ (int-ℕ (succ-ℕ x))
  dist-int-ℕ (succ-ℕ x) (succ-ℕ y) =
    ( ( ap-dist-ℤ (inv (succ-int-ℕ x)) (inv (succ-int-ℕ y))) ∙
      ( ap abs-ℤ (diff-succ-ℤ (int-ℕ x) (int-ℕ y)))) ∙
    ( dist-int-ℕ x y)
```

### If two integers are nonnegative, the distance between their absolute values is the distance between them

```agda
abstract
  dist-abs-ℤ :
    (x y : ℤ) → (H : is-nonnegative-ℤ x) → (K : is-nonnegative-ℤ y) →
    dist-ℕ (abs-ℤ x) (abs-ℤ y) ＝ dist-ℤ x y
  dist-abs-ℤ (inr (inl _)) y H K =
    equational-reasoning
      dist-ℕ 0 (abs-ℤ y)
      ＝ abs-ℤ y
        by left-unit-law-dist-ℕ (abs-ℤ y)
      ＝ dist-ℤ (zero-ℤ) y
        by inv (left-zero-law-dist-ℤ y)
  dist-abs-ℤ (inr (inr x)) (inr (inl _)) H K =
    equational-reasoning
      dist-ℕ (abs-ℤ (inr (inr x))) 0
      ＝ succ-ℕ x
        by right-unit-law-dist-ℕ (abs-ℤ (inr (inr x)))
      ＝ dist-ℤ (inr (inr x)) zero-ℤ
        by inv (right-zero-law-dist-ℤ (inr (inr x)))
  dist-abs-ℤ (inr (inr x)) (inr (inr y)) H K =
    equational-reasoning
      dist-ℕ (succ-ℕ x) (succ-ℕ y)
      ＝ dist-ℤ (int-ℕ (succ-ℕ x)) (int-ℕ (succ-ℕ y))
        by inv (dist-int-ℕ (succ-ℕ x) (succ-ℕ y))
```
