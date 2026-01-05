# Weakly anodyne maps

```agda
module orthogonal-factorization-systems.weakly-anodyne-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences-arrows
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.retracts-of-arrows
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.anodyne-maps
open import orthogonal-factorization-systems.maps-local-at-maps
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.types-local-at-maps

open import synthetic-homotopy-theory.cocartesian-morphisms-arrows
```

</details>

## Idea

A map $j : C → D$ is said to be
{{#concept "weakly anodyne" Disambiguation="map of types" Agda=is-weakly-anodyne-map}}
with respect to a map $f : A → B$, or **weakly $f$-anodyne**, if every map that
is local at $f$ is also local at $j$.

## Definitions

### The predicate of being weakly anodyne with respect to a map

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (j : C → D)
  where

  is-weakly-anodyne-map-Level :
    (l5 l6 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l5 ⊔ lsuc l6)
  is-weakly-anodyne-map-Level l5 l6 =
    {X : UU l5} {Y : UU l6} (g : X → Y) → is-local-map f g → is-local-map j g

  is-weakly-anodyne-map : UUω
  is-weakly-anodyne-map = {l5 l6 : Level} → is-weakly-anodyne-map-Level l5 l6
```

## Properties

### Anodyne maps are weakly anodyne

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) {j : C → D}
  where

  is-weakly-anodyne-map-is-anodyne-map :
    is-anodyne-map f j → is-weakly-anodyne-map f j
  is-weakly-anodyne-map-is-anodyne-map J g G x =
    is-local-is-orthogonal-terminal-map j
      ( J ( terminal-map (fiber g x))
          ( is-orthogonal-terminal-map-is-local f (G x)))
```

### Weakly anodyne maps are closed under retracts of arrows

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4} {C' : UU l5} {D' : UU l6}
  (f : A → B) {j : C → D} {j' : C' → D'}
  where

  is-weakly-anodyne-map-retract-arrow :
    retract-arrow j j' → is-weakly-anodyne-map f j → is-weakly-anodyne-map f j'
  is-weakly-anodyne-map-retract-arrow α J g G x =
    is-local-retract-arrow-is-local j' j α (fiber g x) (J g G x)
```
