# The Whitehead principle for maps

```agda
module logic.whitehead-principle-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions

open import logic.whitehead-principle-types
```

</details>

## Idea

A map `f : X → Y` is said to be **∞-connected** if it is `k`-connected for all
`k : 𝕋`.

By the equivalence between equivalences and contractible maps, equivalences are
∞-connected.

The **Whitehead principle for maps** asserts the converse, that ∞-connected maps
are equivalences.

## Definition

### ∞-connected maps

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-∞-connected-map-Prop : Prop (l1 ⊔ l2)
  is-∞-connected-map-Prop = Π-Prop 𝕋 (λ k → is-connected-map-Prop k f)

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

  is-equiv-is-∞-connected : is-equiv f → is-∞-connected-map f
  is-equiv-is-∞-connected f-equiv k = is-connected-map-is-equiv f-equiv
```

### The Whitehead principle for maps

```agda
Whitehead-Principle-Map : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Whitehead-Principle-Map l1 l2 = (X : UU l1) → (Y : UU l2) → (f : X → Y) → is-∞-connected-map f → is-equiv f
```
