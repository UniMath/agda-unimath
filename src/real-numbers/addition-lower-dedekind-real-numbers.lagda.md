# Addition of lower Dedekind real numbers

```agda
module real-numbers.addition-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.existential-quantification
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.minkowski-multiplication-commutative-monoids

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

The sum of two [lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md)
is the Minkowski sum of their cuts.

```agda
module _
  {l1 l2 : Level}
  (x : lower-ℝ l1)
  (y : lower-ℝ l2)
  where

  cut-add-lower-ℝ : subtype (l1 ⊔ l2) ℚ
  cut-add-lower-ℝ =
    minkowski-mul-Commutative-Monoid
      ( commutative-monoid-add-ℚ)
      ( cut-lower-ℝ x)
      ( cut-lower-ℝ y)

  is-in-add-lower-ℝ-cut : ℚ → UU (l1 ⊔ l2)
  is-in-add-lower-ℝ-cut = is-in-subtype cut-add-lower-ℝ

  -- is-inhabited-add-lower-ℝ : exists ℚ cut-add-lower-ℝ
  -- is-inhabited-add-lower-ℝ
```

## Properties

### Addition of lower Dedekind real numbers is commutative

```agda
-- commutative-add-lower-ℝ :
```
