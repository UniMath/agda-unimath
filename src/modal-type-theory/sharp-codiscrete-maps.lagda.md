# Sharp codiscrete maps

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-codiscrete-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels

open import modal-type-theory.sharp-codiscrete-types
```

</details>

## Idea

A map is said to be
{{#concept "sharp codiscrete" Disambiguation="map" Agda=is-sharp-codiscrete-map}}
if its [fibers](foundation-core.fibers-of-maps.md) are
[sharp codiscrete](modal-type-theory.sharp-codiscrete-types.md).

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-sharp-codiscrete-map : UU (l1 ⊔ l2)
  is-sharp-codiscrete-map = is-sharp-codiscrete-family (fiber f)

  is-sharp-codiscrete-map-Prop : Prop (l1 ⊔ l2)
  is-sharp-codiscrete-map-Prop = is-sharp-codiscrete-family-Prop (fiber f)

  is-prop-is-sharp-codiscrete-map : is-prop is-sharp-codiscrete-map
  is-prop-is-sharp-codiscrete-map =
    is-prop-type-Prop is-sharp-codiscrete-map-Prop
```
