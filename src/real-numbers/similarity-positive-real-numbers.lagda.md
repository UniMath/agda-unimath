# Similarity of positive real numbers

```agda
module real-numbers.similarity-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-sets
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.large-equivalence-relations
open import foundation.large-similarity-relations
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

Two [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="positive real numbers" Agda=sim-ℝ⁺}} if
they are [similar](real-numbers.similarity-real-numbers.md) as real numbers.

## Definition

```agda
sim-prop-ℝ⁺ : Large-Relation-Prop (_⊔_) ℝ⁺
sim-prop-ℝ⁺ = sim-prop-Cumulative-Large-Set cumulative-large-set-ℝ⁺

sim-ℝ⁺ : Large-Relation (_⊔_) ℝ⁺
sim-ℝ⁺ = sim-Cumulative-Large-Set cumulative-large-set-ℝ⁺
```

## Properties

### Transitivity of similarity

```agda
abstract
  transitive-sim-ℝ⁺ : is-transitive-Large-Relation ℝ⁺ sim-ℝ⁺
  transitive-sim-ℝ⁺ =
    transitive-sim-Cumulative-Large-Set cumulative-large-set-ℝ⁺
```

### Similarity characterizes equality

```agda
abstract
  eq-sim-ℝ⁺ : {l : Level} (x y : ℝ⁺ l) → sim-ℝ⁺ x y → x ＝ y
  eq-sim-ℝ⁺ = eq-sim-Cumulative-Large-Set cumulative-large-set-ℝ⁺
```

### Positive real numbers are similar to their raised universe level counterparts

```agda
abstract
  sim-raise-ℝ⁺ : {l0 : Level} (l : Level) (x : ℝ⁺ l0) → sim-ℝ⁺ x (raise-ℝ⁺ l x)
  sim-raise-ℝ⁺ =
    sim-raise-Cumulative-Large-Set cumulative-large-set-ℝ⁺
```
