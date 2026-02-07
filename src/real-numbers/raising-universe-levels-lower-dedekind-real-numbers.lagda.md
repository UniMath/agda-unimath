# Raising the universe levels of lower Dedekind real numbers

```agda
module real-numbers.raising-universe-levels-lower-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
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
{{#concept "raise" Disambiguation="a lower Dedekind real number" Agda=raise-lower-ℝ}}
a lower real number `x` from the universe `𝒰` to a similar lower real number in
the universe `𝒱`.

## Definitions

### Raising lower Dedekind real numbers

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
    pr1 (is-rounded-cut-raise-lower-ℝ q) (map-raise q<x) =
      map-tot-exists
        ( λ _ → map-product id map-raise)
        ( forward-implication (is-rounded-cut-lower-ℝ x q) q<x)
    pr2 (is-rounded-cut-raise-lower-ℝ q) ∃r =
      map-raise
        ( backward-implication
          ( is-rounded-cut-lower-ℝ x q)
          ( map-tot-exists (λ _ → map-product id map-inv-raise) ∃r))

  raise-lower-ℝ : lower-ℝ (l0 ⊔ l)
  raise-lower-ℝ =
    cut-raise-lower-ℝ ,
    is-inhabited-cut-raise-lower-ℝ ,
    is-rounded-cut-raise-lower-ℝ
```

## See also

- [Raising the universe levels of upper Dedekind real numbers](real-numbers.raising-universe-levels-upper-dedekind-real-numbers.md)
- [Raising the universe levels of Dedekind real numbers](real-numbers.raising-universe-levels-real-numbers.md)
- [Raising the universe levels of MacNeille real numbers](real-numbers.raising-universe-levels-macneille-real-numbers.md)
