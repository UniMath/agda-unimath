# The Whitehead principle for maps

```agda
module synthetic-homotopy-theory.whitehead-principle-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions

open import synthetic-homotopy-theory.whitehead-principle-types
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

### A map is ∞-connected iff its fibers are [∞-connected](synthetic-homotopy-theory.whitehead-principle-types.md)

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  is-∞-connected-map-fibers-are-∞-connected :
    is-∞-connected-map f → (y : Y) → is-∞-connected (fiber f y)
  is-∞-connected-map-fibers-are-∞-connected f-∞-conn y k = f-∞-conn k y

  fibers-are-∞-connected-is-∞-connected-map :
    ((y : Y) → is-∞-connected (fiber f y)) → is-∞-connected-map f
  fibers-are-∞-connected-is-∞-connected-map fib-∞-conn k y = fib-∞-conn y k
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
Whitehead-Principle-Map-Level : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Whitehead-Principle-Map-Level l1 l2 =
  ( X : UU l1) → (Y : UU l2) → (f : X → Y) → is-∞-connected-map f → is-equiv f

Whitehead-Principle-Map : UUω
Whitehead-Principle-Map = {l1 l2 : Level} → Whitehead-Principle-Map-Level l1 l2
```

## Properties

### The Whitehead principle for maps implies the Whitehead principle for types

```agda
Whitehead-Principle-Maps-implies-Types :
  Whitehead-Principle-Map → Whitehead-Principle
Whitehead-Principle-Maps-implies-Types WP X X-∞-conn =
  is-contr-equiv-unit eq where
  eq : X ≃ unit
  pr1 eq = λ _ → star
  pr2 eq =
    WP X unit (λ _ → star) (fibers-are-∞-connected-is-∞-connected-map
    ( λ _ → star)
    λ y → is-∞-connected-equiv (equiv-fiber-terminal-map star) X-∞-conn)
```

### The Whitehead principle for types implies the Whitehead principle for maps

```agda
Whitehead-Principle-Types-implies-Maps :
  Whitehead-Principle → Whitehead-Principle-Map
Whitehead-Principle-Types-implies-Maps WP X Y f f-∞-conn =
  is-equiv-is-contr-map f-ctr where
  f-ctr : is-contr-map f
  f-ctr y = WP (fiber f y) (λ x → f-∞-conn x y)
```

## External links

For the equivalent concept in the ∞-categorical semantics of homotopy type
theory, cf.
[§ 6.5.2 of Lurie's _Higher Topos Theory_](https://www.math.ias.edu/~lurie/papers/highertopoi.pdf)
