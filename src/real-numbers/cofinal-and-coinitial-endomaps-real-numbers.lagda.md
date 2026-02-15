# Cofinal and coinitial endomaps on the real numbers

```agda
module real-numbers.cofinal-and-coinitial-endomaps-real-numbers where
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

An [endomap](foundation.endomorphisms.md) `f` on the
[real numbers](real-numbers.dedekind-real-numbers.md) is

- {{#concept "cofinal" Disambiguation="endomap on ℝ" Agda=is-cofinal-endomap-ℝ}}
  if for every [rational](elementary-number-theory.rational-numbers.md) `q`,
  there [exists](foundation.existential-quantification.md) `x` such that
  `q ≤ f x`
- {{#concept "coinitial" Disambiguation="endomap on ℝ" Agda=is-coinitial-endomap-ℝ}}
  if for every rational `q`, there exists `x` such that `f x ≤ q`

## Definition

```agda
module _
  {l1 l2 : Level}
  (f : ℝ l1 → ℝ l2)
  where

  is-cofinal-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-cofinal-prop-endomap-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → leq-prop-ℝ (real-ℚ q) (f x)))

  is-cofinal-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-cofinal-endomap-ℝ = type-Prop is-cofinal-prop-endomap-ℝ

  is-coinitial-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-coinitial-prop-endomap-ℝ =
    Π-Prop ℚ (λ q → ∃ (ℝ l1) (λ x → leq-prop-ℝ (f x) (real-ℚ q)))

  is-coinitial-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-coinitial-endomap-ℝ = type-Prop is-coinitial-prop-endomap-ℝ

  is-cofinal-and-coinitial-prop-endomap-ℝ : Prop (lsuc l1 ⊔ l2)
  is-cofinal-and-coinitial-prop-endomap-ℝ =
    is-cofinal-prop-endomap-ℝ ∧ is-coinitial-prop-endomap-ℝ

  is-cofinal-and-coinitial-endomap-ℝ : UU (lsuc l1 ⊔ l2)
  is-cofinal-and-coinitial-endomap-ℝ =
    type-Prop is-cofinal-and-coinitial-prop-endomap-ℝ
```
