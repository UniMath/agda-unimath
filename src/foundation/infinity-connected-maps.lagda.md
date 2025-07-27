# ∞-connected maps

```agda
module foundation.infinity-connected-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.infinity-connected-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A map `f : X → Y` is said to be
{{#concept "∞-connected" Disambiguation="map of types" Agda=is-∞-connected-map}}
if it is `k`-[connected](foundation.connected-maps.md) for all
[truncation levels](foundation-core.truncation-levels.md) `k`.

In particular, since [equivalences](foundation-core.equivalences.md) have
[contractible](foundation-core.contractible-types.md)
[fibers](foundation-core.fibers-of-maps.md), equivalences are ∞-connected.

## Definition

### ∞-connected maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-∞-connected-map-Prop : Prop (l1 ⊔ l2)
  is-∞-connected-map-Prop = Π-Prop Y (λ y → is-∞-connected-Prop (fiber f y))

  is-∞-connected-map : UU (l1 ⊔ l2)
  is-∞-connected-map = type-Prop is-∞-connected-map-Prop

  is-prop-is-∞-connected-map : is-prop is-∞-connected-map
  is-prop-is-∞-connected-map = is-prop-type-Prop is-∞-connected-map-Prop
```

### Equivalences are ∞-connected

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-∞-connected-map-is-equiv : is-equiv f → is-∞-connected-map f
  is-∞-connected-map-is-equiv is-equiv-f k x = is-connected-map-is-equiv is-equiv-f k
```
