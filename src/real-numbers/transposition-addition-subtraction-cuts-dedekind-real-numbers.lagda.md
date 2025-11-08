# Transposition of addition and subtraction through cuts of Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

Transposition laws for [addition](real-numbers.addition-real-numbers.md) and
[subtraction](real-numbers.difference-real-numbers.md) on the cuts of
[Dedekind real numbers](real-numbers.dedekind-real-numbers.md) include:

- `p + q` is in the lower cut of `x` [iff](foundation.logical-equivalences.md)
  `p` is in the lower cut of `x - q`
- `p - q` is in the lower cut of `x` iff `p` is in the lower cut of `x + q`

These laws follow from the more general transposition laws for addition and
subtraction on real numbers with respect to
[strict inequality](real-numbers.strict-inequality-real-numbers.md).

### Transposition laws for lower cuts

```agda
module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  abstract
    transpose-add-is-in-lower-cut-ℝ :
      is-in-lower-cut-ℝ x (p +ℚ q) →
      is-in-lower-cut-ℝ (x -ℝ real-ℚ q) p
    transpose-add-is-in-lower-cut-ℝ p+q<x =
      is-in-lower-cut-le-real-ℚ
        ( x -ℝ real-ℚ q)
        ( le-transpose-left-add-ℝ
          ( real-ℚ p)
          ( real-ℚ q)
          ( x)
          ( inv-tr
            ( λ y → le-ℝ y x)
            ( add-real-ℚ p q)
            ( le-real-is-in-lower-cut-ℚ x p+q<x)))

    transpose-is-in-lower-cut-diff-ℝ :
      is-in-lower-cut-ℝ (x -ℝ real-ℚ p) q → is-in-lower-cut-ℝ x (q +ℚ p)
    transpose-is-in-lower-cut-diff-ℝ x-p<q =
      is-in-lower-cut-le-real-ℚ
        ( x)
        ( tr
          ( λ y → le-ℝ y x)
          ( add-real-ℚ q p)
          ( le-transpose-right-diff-ℝ
            ( real-ℚ q)
            ( x)
            ( real-ℚ p)
            ( le-real-is-in-lower-cut-ℚ (x -ℝ real-ℚ p) x-p<q)))

module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  abstract
    transpose-diff-is-in-lower-cut-ℝ :
      is-in-lower-cut-ℝ x (p -ℚ q) →
      is-in-lower-cut-ℝ (x +ℝ real-ℚ q) p
    transpose-diff-is-in-lower-cut-ℝ x<p-q =
      tr
        ( λ y → is-in-lower-cut-ℝ y p)
        ( ap
          ( x +ℝ_)
          ( ap neg-ℝ (inv (neg-real-ℚ q)) ∙ neg-neg-ℝ (real-ℚ q)))
        ( transpose-add-is-in-lower-cut-ℝ x p (neg-ℚ q) x<p-q)

    transpose-is-in-lower-cut-add-ℝ :
      is-in-lower-cut-ℝ (x +ℝ real-ℚ p) q →
      is-in-lower-cut-ℝ x (q -ℚ p)
    transpose-is-in-lower-cut-add-ℝ q<x+p =
      transpose-is-in-lower-cut-diff-ℝ
        ( x)
        ( neg-ℚ p)
        ( q)
        ( tr
          ( λ y → is-in-lower-cut-ℝ y q)
          ( ap
            ( x +ℝ_)
            ( inv (neg-neg-ℝ (real-ℚ p)) ∙ ap neg-ℝ (neg-real-ℚ p)))
          ( q<x+p))
```

### Transposition laws for upper cuts

```agda
module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  abstract
    transpose-add-is-in-upper-cut-ℝ :
      is-in-upper-cut-ℝ x (p +ℚ q) →
      is-in-upper-cut-ℝ (x -ℝ real-ℚ q) p
    transpose-add-is-in-upper-cut-ℝ x<p+q =
      is-in-upper-cut-le-real-ℚ
        ( x -ℝ real-ℚ q)
        ( le-transpose-right-add-ℝ
          ( x)
          ( real-ℚ p)
          ( real-ℚ q)
          ( inv-tr
            ( le-ℝ x)
            ( add-real-ℚ p q)
            ( le-real-is-in-upper-cut-ℚ x x<p+q)))

    transpose-is-in-upper-cut-diff-ℝ :
      is-in-upper-cut-ℝ (x -ℝ real-ℚ p) q → is-in-upper-cut-ℝ x (q +ℚ p)
    transpose-is-in-upper-cut-diff-ℝ x-p<q =
      is-in-upper-cut-le-real-ℚ
        ( x)
        ( tr
          ( le-ℝ x)
          ( add-real-ℚ q p)
          ( le-transpose-left-diff-ℝ
            ( x)
            ( real-ℚ p)
            ( real-ℚ q)
            ( le-real-is-in-upper-cut-ℚ (x -ℝ real-ℚ p) x-p<q)))

module _
  {l : Level} (x : ℝ l) (p q : ℚ)
  where

  abstract
    transpose-diff-is-in-upper-cut-ℝ :
      is-in-upper-cut-ℝ x (p -ℚ q) →
      is-in-upper-cut-ℝ (x +ℝ real-ℚ q) p
    transpose-diff-is-in-upper-cut-ℝ x<p-q =
      tr
        ( λ y → is-in-upper-cut-ℝ y p)
        ( ap
          ( x +ℝ_)
          ( ap neg-ℝ (inv (neg-real-ℚ q)) ∙ neg-neg-ℝ (real-ℚ q)))
        ( transpose-add-is-in-upper-cut-ℝ x p (neg-ℚ q) x<p-q)

    transpose-is-in-upper-cut-add-ℝ :
      is-in-upper-cut-ℝ (x +ℝ real-ℚ p) q →
      is-in-upper-cut-ℝ x (q -ℚ p)
    transpose-is-in-upper-cut-add-ℝ q<x+p =
      transpose-is-in-upper-cut-diff-ℝ
        ( x)
        ( neg-ℚ p)
        ( q)
        ( tr
          ( λ y → is-in-upper-cut-ℝ y q)
          ( ap
            ( x +ℝ_)
            ( inv (neg-neg-ℝ (real-ℚ p)) ∙ ap neg-ℝ (neg-real-ℚ p)))
          ( q<x+p))
```
