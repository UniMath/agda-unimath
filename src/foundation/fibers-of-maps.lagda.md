# Fibers of maps

```agda
module foundation.fibers-of-maps where

open import foundation-core.fibers-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Properties

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  square-fiber :
    f ∘ pr1 ~ const unit B b ∘ const (fiber f b) unit star
  square-fiber = pr2

  cone-fiber : cone f (const unit B b) (fiber f b)
  pr1 cone-fiber = pr1
  pr1 (pr2 cone-fiber) = const (fiber f b) unit star
  pr2 (pr2 cone-fiber) = square-fiber

  abstract
    is-pullback-cone-fiber : is-pullback f (const unit B b) cone-fiber
    is-pullback-cone-fiber =
      is-equiv-tot-is-fiberwise-equiv
        ( λ a → is-equiv-map-inv-left-unit-law-prod)

  abstract
    universal-property-pullback-cone-fiber :
      {l : Level} → universal-property-pullback l f (const unit B b) cone-fiber
    universal-property-pullback-cone-fiber =
      universal-property-pullback-is-pullback f
        ( const unit B b)
        ( cone-fiber)
        ( is-pullback-cone-fiber)
```

### The fiber of the terminal map at any point is equivalent to its domain

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-fiber-terminal-map :
    (u : unit) → fiber (terminal-map {A = A}) u ≃ A
  equiv-fiber-terminal-map u =
    right-unit-law-Σ-is-contr
      ( λ a → is-prop-is-contr is-contr-unit (terminal-map a) u)

  inv-equiv-fiber-terminal-map :
    (u : unit) → A ≃ fiber (terminal-map {A = A}) u
  inv-equiv-fiber-terminal-map u =
    inv-equiv (equiv-fiber-terminal-map u)

  equiv-fiber-terminal-map-star :
    fiber (terminal-map {A = A}) star ≃ A
  equiv-fiber-terminal-map-star = equiv-fiber-terminal-map star

  inv-equiv-fiber-terminal-map-star :
    A ≃ fiber (terminal-map {A = A}) star
  inv-equiv-fiber-terminal-map-star =
    inv-equiv equiv-fiber-terminal-map-star
```

### The total space of the fibers of the terminal map is equivalent to its domain

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-total-fiber-terminal-map :
    Σ unit (fiber (terminal-map {A = A})) ≃ A
  equiv-total-fiber-terminal-map =
    ( left-unit-law-Σ-is-contr is-contr-unit star) ∘e
    ( equiv-tot equiv-fiber-terminal-map)

  inv-equiv-total-fiber-terminal-map :
    A ≃ Σ unit (fiber (terminal-map {A = A}))
  inv-equiv-total-fiber-terminal-map =
    inv-equiv equiv-total-fiber-terminal-map
```

## Table of files about fibers of maps

The following table lists files that are about fibers of maps as a general
concept.

{{#include tables/fibers-of-maps.md}}
