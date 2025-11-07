# The W-type of the type of propositions

```agda
module trees.w-type-of-propositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import trees.extensional-w-types
open import trees.w-types
```

</details>

## Idea

The {{#concept "W-type of the type of propositions" Agda=𝕎-Prop}} is defined
using the type of [propositions](foundation-core.propositions.md) and the
canonical type family over it.

## Definition

```agda
𝕎-Prop : (l : Level) → UU (lsuc l)
𝕎-Prop l = 𝕎 (Prop l) type-Prop

zero-𝕎-Prop : {l : Level} → 𝕎-Prop l
zero-𝕎-Prop {l} = constant-𝕎 (raise-empty-Prop l) is-empty-raise-empty

succ-𝕎-Prop : {l : Level} → 𝕎-Prop l → 𝕎-Prop l
succ-𝕎-Prop {l} P = tree-𝕎 (raise-unit-Prop l) (λ x → P)
```

### Standard subfinite types(?)

```agda
standard-subfinite-type : {l : Level} → 𝕎-Prop l → UU l
standard-subfinite-type (tree-𝕎 P α) =
  Σ (type-Prop P) (λ p → standard-subfinite-type (α p)) + type-Prop P
```

## Properties

### 𝕎-Prop is extensional

```agda
is-extensional-𝕎-Prop : {l : Level} → is-extensional-𝕎 (Prop l) type-Prop
is-extensional-𝕎-Prop = is-extensional-is-univalent-𝕎 is-univalent-type-Prop
```

### 𝕎-Prop is a set

```agda
is-set-𝕎-Prop : {l : Level} → is-set (𝕎-Prop l)
is-set-𝕎-Prop = is-set-𝕎 is-set-type-Prop
```
