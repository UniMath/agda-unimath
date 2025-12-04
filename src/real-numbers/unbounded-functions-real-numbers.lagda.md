# Unbounded functions on `ℝ`

```agda
module real-numbers.unbounded-functions-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A function is:

- unbounded below if for every
  [rational](elementary-number-theory.rational-numbers.md) `q`, there
  [exists](foundation.existential-quantification.md) `x : ℝ` such that `f x < q`
- unbounded above if for every
  [rational](elementary-number-theory.rational-numbers.md) `q`, there
  [exists](foundation.existential-quantification.md) `x : ℝ` such that `q < f x`
- {{#concept "unbounded" Agda=is-unbounded-function-ℝ Disambiguation="function on ℝ"}}
  if it is both unbounded above and below

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-unbounded-above-prop-function-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-above-prop-function-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → le-prop-ℝ (real-ℚ q) (f x)))

  is-unbounded-above-function-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-above-function-ℝ = type-Prop is-unbounded-above-prop-function-ℝ

  is-unbounded-below-prop-function-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-below-prop-function-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → le-prop-ℝ (f x) (real-ℚ q)))

  is-unbounded-below-function-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-below-function-ℝ = type-Prop is-unbounded-below-prop-function-ℝ

  is-unbounded-prop-function-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-prop-function-ℝ =
    is-unbounded-above-prop-function-ℝ ∧ is-unbounded-below-prop-function-ℝ

  is-unbounded-function-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-function-ℝ = type-Prop is-unbounded-prop-function-ℝ
```
