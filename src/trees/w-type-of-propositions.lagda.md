# The W-type of the type of propositions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.w-type-of-propositions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.propositional-extensionality funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.raising-universe-levels-unit-type
open import foundation.sets funext univalence
open import foundation.unit-type
open import foundation.universe-levels

open import trees.extensional-w-types funext univalence truncations
open import trees.w-types funext univalence truncations
```

</details>

## Idea

The W-type of the type of propositions is defined using the type of propositions
and the canonical type family over it.

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
