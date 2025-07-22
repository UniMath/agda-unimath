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

A map `f : X → Y` is said to be **∞-connected** if it is `k`-connected for all
`k : 𝕋`.

By the equivalence between equivalences and contractible maps, equivalences are
∞-connected.

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

### A map is ∞-connected iff its fibers are [∞-connected](synthetic-homotopy-theory.whitehead-principle-types.md)

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-∞-connected-map-fibers-are-∞-connected :
    is-∞-connected-map f → (y : Y) → is-∞-connected (fiber f y)
  is-∞-connected-map-fibers-are-∞-connected f-∞-conn y k = f-∞-conn y k

  fibers-are-∞-connected-is-∞-connected-map :
    ((y : Y) → is-∞-connected (fiber f y)) → is-∞-connected-map f
  fibers-are-∞-connected-is-∞-connected-map fib-∞-conn k y = fib-∞-conn k y
```

### Equivalences are ∞-connected

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-equiv-is-∞-connected : is-equiv f → is-∞-connected-map f
  is-equiv-is-∞-connected f-equiv k x = is-connected-map-is-equiv f-equiv k
```
