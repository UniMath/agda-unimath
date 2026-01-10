# Unbounded endomaps on the real numbers

```agda
module real-numbers.unbounded-endomaps-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers

open import foundation.conjunction
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

An [endomorphism](foundation.endomorphisms.md) `f` on the
[real numbers](real-numbers.dedekind-real-numbers.md) is

- {{#concept "unbounded above" Disambiguation="endomap on ℝ" Agda=is-unbounded-above-endomap-ℝ}}
  if for every [rational](elementary-number-theory.rational-numbers.md) `q`,
  there exists `x` such that `q ≤ f x`
- {{#concept "unbounded below" Disambiguation="endomap on ℝ" Agda=is-unbounded-below-endomap-ℝ}}
  if for every rational `q`, there exists `x` such that `f x ≤ q`

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-unbounded-above-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-above-prop-endomap-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → leq-prop-ℝ (real-ℚ q) (f x)))

  is-unbounded-above-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-above-endomap-ℝ = type-Prop is-unbounded-above-prop-endomap-ℝ

  is-unbounded-below-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-below-prop-endomap-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → leq-prop-ℝ (f x) (real-ℚ q)))

  is-unbounded-below-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-below-endomap-ℝ = type-Prop is-unbounded-below-prop-endomap-ℝ

  is-unbounded-above-and-below-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-unbounded-above-and-below-prop-endomap-ℝ =
    is-unbounded-above-prop-endomap-ℝ ∧ is-unbounded-below-prop-endomap-ℝ

  is-unbounded-above-and-below-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-unbounded-above-and-below-endomap-ℝ =
    type-Prop is-unbounded-above-and-below-prop-endomap-ℝ
```
