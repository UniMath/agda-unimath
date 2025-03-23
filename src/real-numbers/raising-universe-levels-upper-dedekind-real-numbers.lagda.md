# Raising the universe levels of upper Dedekind real numbers

```agda
module real-numbers.raising-universe-levels-upper-dedekind-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import real-numbers.similarity-upper-dedekind-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

For every [universe](foundation.universe-levels.md) `𝒰` there is a type of
[upper Dedekind real numbers](real-numbers.upper-dedekind-real-numbers.md)
`upper-ℝ` relative to `𝒰`, `upper-ℝ 𝒰`. Given a larger universe `𝒱`, then we may
{{#concept "raise" Disambiguation="upper Dedekind real number" Agda=raise-upper-ℝ}}
a real number `x` from the universe `𝒰` to a
[similar](real-numbers.similarity-upper-dedekind-real-numbers.md) upper Dedekind
real number in the universe `𝒱`.

## Definition

### Raising upper Dedekind real numbers

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
    pr1 (is-rounded-cut-raise-upper-ℝ q) (map-raise q<x) =
      map-tot-exists
        (λ _ → map-product id map-raise)
        ( forward-implication (is-rounded-cut-upper-ℝ x q) q<x)
    pr2 (is-rounded-cut-raise-upper-ℝ q) ∃r =
      map-raise
        ( backward-implication
          ( is-rounded-cut-upper-ℝ x q)
          ( map-tot-exists (λ _ → map-product id map-inv-raise) ∃r))

  raise-upper-ℝ : upper-ℝ (l0 ⊔ l)
  raise-upper-ℝ =
    cut-raise-upper-ℝ ,
    is-inhabited-cut-raise-upper-ℝ ,
    is-rounded-cut-raise-upper-ℝ
```

## Properties

### upper Dedekind reals are similar to their raised-universe equivalents

```agda
opaque
  unfolding sim-upper-ℝ

  sim-raise-upper-ℝ :
    {l0 : Level} → (l : Level) → (x : upper-ℝ l0) →
    sim-upper-ℝ x (raise-upper-ℝ l x)
  pr1 (sim-raise-upper-ℝ l x) _ = map-raise
  pr2 (sim-raise-upper-ℝ l x) _ = map-inv-raise
```

### Raising a real to its own level is the identity

```agda
eq-raise-upper-ℝ : {l : Level} → (x : upper-ℝ l) → x ＝ raise-upper-ℝ l x
eq-raise-upper-ℝ {l} x = eq-sim-upper-ℝ (sim-raise-upper-ℝ l x)
```
