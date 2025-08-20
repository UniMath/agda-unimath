# Noninjective maps

```agda
module foundation.noninjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.repetitions-of-values
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
```

</details>

## Idea

_Noninjectivity_ is a positive way of stating that a map is
[not](foundation.negation.md) [injective](foundation-core.injective-maps.md). A
map `f : A → B` is
{{#concept "noninjective" Disambiguation="map of types" Agda=is-noninjective}}
if there [exists](foundation.existential-quantification.md) a
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

  is-prop-is-not-injective : {f : A → B} → is-prop (is-not-injective f)
  is-prop-is-not-injective = is-prop-neg

  is-not-injective-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-not-injective-Prop f = (is-not-injective f , is-prop-is-not-injective)
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

### The type of noninjective maps

```agda
noninjective-map : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
noninjective-map A B = Σ (A → B) is-noninjective

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : noninjective-map A B)
  where

  map-noninjective-map : A → B
  map-noninjective-map = pr1 f

  is-noninjective-map-noninjective-map : is-noninjective map-noninjective-map
  is-noninjective-map-noninjective-map = pr2 f
```

## Properties

### Noninjective maps are not injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-not-injective-is-noninjective : is-noninjective f → is-not-injective f
    is-not-injective-is-noninjective =
      rec-trunc-Prop
        ( is-not-injective-Prop f)
        ( λ ((x , y , x≠y) , p) H → x≠y (H p))
```

### Noninjectivity of composites

Given maps `f : A → B` and `g : B → C`, then

- if `f` is noninjective then `g ∘ f` is noninjective.
- if `g` is injective and `g ∘ f` is noninjective then `f` is noninjective.

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {f : A → B} {g : B → C}
  where

  is-noninjective-comp :
    is-noninjective f → is-noninjective (g ∘ f)
  is-noninjective-comp =
    map-trunc-Prop (repetition-of-values-comp {g = g} {f})

  is-noninjective-right-factor :
    is-injective g → is-noninjective (g ∘ f) → is-noninjective f
  is-noninjective-right-factor G =
    map-trunc-Prop (repetition-of-values-right-factor' G)
```

## See also

- [Noncontractible types](foundation.noncontractible-types.md)
