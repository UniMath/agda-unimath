# Raising universe levels of upper Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.raising-universe-levels-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-cartesian-product-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md)
`upper-ℝ` relative to `𝒰`, `upper-ℝ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a dedekind real number" Agda=raise-ℝ}} a
upper Dedekind real number `x` from the universe `𝒰` to a upper Dedekind real
number in the universe `𝒱`.

## Definition

```agda
module _
  {l0 : Level} (l : Level) (x : upper-ℝ l0)
  where

  cut-raise-upper-ℝ : subtype (l0 ⊔ l) ℚ
  cut-raise-upper-ℝ = raise-subtype l (cut-upper-ℝ x)

  abstract
    is-inhabited-cut-raise-upper-ℝ : is-inhabited-subtype cut-raise-upper-ℝ
    is-inhabited-cut-raise-upper-ℝ =
      map-tot-exists (λ _ → map-raise) (is-inhabited-cut-upper-ℝ x)

    is-rounded-cut-raise-upper-ℝ :
      (q : ℚ) →
      is-in-subtype cut-raise-upper-ℝ q ↔
      exists ℚ (λ p → le-ℚ-Prop p q ∧ cut-raise-upper-ℝ p)
    is-rounded-cut-raise-upper-ℝ q =
      ( iff-tot-exists
        ( λ p →
          iff-equiv
            ( equiv-product-right
              ( compute-raise l (is-in-cut-upper-ℝ x p))))) ∘iff
      ( is-rounded-cut-upper-ℝ x q) ∘iff
      ( iff-equiv (inv-compute-raise l (is-in-cut-upper-ℝ x q)))

  raise-upper-ℝ : upper-ℝ (l0 ⊔ l)
  raise-upper-ℝ =
    cut-raise-upper-ℝ ,
    is-inhabited-cut-raise-upper-ℝ ,
    is-rounded-cut-raise-upper-ℝ
```
