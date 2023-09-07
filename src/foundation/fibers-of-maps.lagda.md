# Fibers of maps

```agda
module foundation.fibers-of-maps where

open import foundation-core.fibers-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
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
    ( f ∘ (pr1 {B = λ x → Id (f x) b})) ~
    ( (const unit B b) ∘ (const (fiber f b) unit star))
  square-fiber = pr2

  cone-fiber : cone f (const unit B b) (fiber f b)
  pr1 cone-fiber = pr1
  pr1 (pr2 cone-fiber) = const (fiber f b) unit star
  pr2 (pr2 cone-fiber) = square-fiber

  abstract
    is-pullback-cone-fiber : is-pullback f (const unit B b) cone-fiber
    is-pullback-cone-fiber =
      is-equiv-tot-is-fiberwise-equiv
        (λ a → is-equiv-map-inv-left-unit-law-prod)

  abstract
    universal-property-pullback-cone-fiber :
      {l : Level} → universal-property-pullback l f (const unit B b) cone-fiber
    universal-property-pullback-cone-fiber =
      universal-property-pullback-is-pullback f
        ( const unit B b)
        ( cone-fiber)
        ( is-pullback-cone-fiber)
```
