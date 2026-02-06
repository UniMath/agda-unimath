# Raising universe levels of lower Dedekind real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.raising-universe-levels-lower-dedekind-real-numbers where
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

open import real-numbers.lower-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[lower Dedekind real numbers](real-numbers.lower-dedekind-real-numbers.md)
`lower-ℝ` relative to `𝒰`, `lower-ℝ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="a dedekind real number" Agda=raise-ℝ}} a
lower Dedekind real number `x` from the universe `𝒰` to a lower Dedekind real
number in the universe `𝒱`.

## Definition

```agda
module _
  {l0 : Level} (l : Level) (x : lower-ℝ l0)
  where

  cut-raise-lower-ℝ : subtype (l0 ⊔ l) ℚ
  cut-raise-lower-ℝ = raise-subtype l (cut-lower-ℝ x)

  abstract
    is-inhabited-cut-raise-lower-ℝ : is-inhabited-subtype cut-raise-lower-ℝ
    is-inhabited-cut-raise-lower-ℝ =
      map-tot-exists (λ _ → map-raise) (is-inhabited-cut-lower-ℝ x)

    is-rounded-cut-raise-lower-ℝ :
      (q : ℚ) →
      is-in-subtype cut-raise-lower-ℝ q ↔
      exists ℚ (λ r → le-ℚ-Prop q r ∧ cut-raise-lower-ℝ r)
    is-rounded-cut-raise-lower-ℝ q =
      ( iff-tot-exists
        ( λ r →
          iff-equiv
            ( equiv-product-right
              ( compute-raise l (is-in-cut-lower-ℝ x r))))) ∘iff
      ( is-rounded-cut-lower-ℝ x q) ∘iff
      ( iff-equiv (inv-compute-raise l (is-in-cut-lower-ℝ x q)))

  raise-lower-ℝ : lower-ℝ (l0 ⊔ l)
  raise-lower-ℝ =
    cut-raise-lower-ℝ ,
    is-inhabited-cut-raise-lower-ℝ ,
    is-rounded-cut-raise-lower-ℝ
```
