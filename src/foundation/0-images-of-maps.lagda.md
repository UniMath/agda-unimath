# `0`-Images of maps

```agda
module foundation.0-images-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.truncation-images-of-maps
open import foundation.universe-levels

open import foundation-core.truncation-levels
```

</details>

## Idea

The {{#concept "0-image" Disambiguation="of a map of types" Agda=0-im}} of a map
`f : A → B` is the type

```text
  0-im f := Σ (b : B), type-trunc-Set (fiber f b).
```

The map `A → 0-im f` is 0-[connected](foundation.connected-maps.md) and the map
`0-im f → B` is 0-[truncated](foundation.truncated-maps.md).

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  0-im : UU (l1 ⊔ l2)
  0-im = trunc-im zero-𝕋 f

  unit-0-im : A → 0-im
  unit-0-im = unit-trunc-im zero-𝕋 f

  projection-0-im : 0-im → B
  projection-0-im = projection-trunc-im zero-𝕋 f
```

## Properties

### Characterization of the identity type of `0-im f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  Eq-unit-0-im : A → A → UU (l1 ⊔ l2)
  Eq-unit-0-im = Eq-unit-trunc-im neg-one-𝕋 f
```
