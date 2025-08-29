# Subsets of the real numbers

```agda
module real-numbers.subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.images-subtypes
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
```

</details>

## Idea

A subset of the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[subtype](foundation.subtypes.md).

## Definition

```agda
subset-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subset-ℝ l1 l2 = subtype l1 (ℝ l2)

type-subset-ℝ : {l1 l2 : Level} → subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
type-subset-ℝ = type-subtype

inclusion-subset-ℝ :
  {l1 l2 : Level} → (S : subset-ℝ l1 l2) → type-subset-ℝ S → ℝ l2
inclusion-subset-ℝ = inclusion-subtype
```

## Properties

### Subsets of the real numbers are sets

```agda
abstract
  is-set-subset-ℝ :
    {l1 l2 : Level} → (S : subset-ℝ l1 l2) → is-set (type-subset-ℝ S)
  is-set-subset-ℝ S = is-set-type-subtype S (is-set-type-Set (ℝ-Set _))
```
