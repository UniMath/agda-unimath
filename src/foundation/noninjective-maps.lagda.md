# Noninjective maps

```agda
module foundation.noninjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.repetitions-of-values
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.negation
open import foundation-core.propositions
```

</details>

## Idea

_Noninjectivity_ is a positive way of stating that a map is
[not](foundation.negation.md) [injective](foundation-core.injective-maps.md). A
map `f : A → B` is
{{#concept "noninjective" Disambiguation="map of types" Agda=is-noninjective}}
if there [exists](foundation.existential-quantifications.md) a
[pair of distinct elements](foundation.pairs-of-distinct-elements.md) `x ≠ y` of
`A` that are mapped to the [same](foundation-core.identity-types.md) value in
`B`, `f x ＝ f y`. In other words, if `f`
[repeats a value](foundation.repetitions-of-values.md).

## Definitions

### Not injective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-not-injective : (A → B) → UU (l1 ⊔ l2)
  is-not-injective f = ¬ (is-injective f)
```

### Noninjective maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-noninjective-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-noninjective-Prop f = trunc-Prop (repetition-of-values f)

  is-noninjective : (A → B) → UU (l1 ⊔ l2)
  is-noninjective f = type-Prop (is-noninjective-Prop f)

  is-prop-is-noninjective : {f : A → B} → is-prop (is-noninjective f)
  is-prop-is-noninjective {f} = is-prop-type-Prop (is-noninjective-Prop f)
```
