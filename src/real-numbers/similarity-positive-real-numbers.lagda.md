# Similarity of positive real numbers

```agda
module real-numbers.similarity-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.propositions
open import real-numbers.positive-real-numbers
open import real-numbers.similarity-real-numbers
open import foundation.dependent-pair-types
```

</details>

## Idea

Two [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md) are
{{#concept "similar" Disambiguation="positive real numbers" Agda=sim-ℝ⁺}} if
they are [similar](real-numbers.similarity-real-numbers.md) as real numbers.

## Definition

```agda
sim-prop-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → Prop (l1 ⊔ l2)
sim-prop-ℝ⁺ (x , _) (y , _) = sim-prop-ℝ x y

sim-ℝ⁺ : {l1 l2 : Level} → ℝ⁺ l1 → ℝ⁺ l2 → UU (l1 ⊔ l2)
sim-ℝ⁺ (x , _) (y , _) = sim-ℝ x y
```
