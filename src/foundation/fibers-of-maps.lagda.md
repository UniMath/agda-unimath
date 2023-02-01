---
title: Fibers of maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.fibers-of-maps where

open import foundation-core.fibers-of-maps public

open import foundation-core.cones-pullbacks
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality using (eq-htpy)
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.type-arithmetic-cartesian-product-types
open import foundation-core.type-arithmetic-dependent-pair-types
open import foundation-core.universal-property-pullbacks
open import foundation-core.universe-levels

open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
```

## Properties

### The fibers of a composition

```agda
fib-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  (c : C) → fib (g ∘ f) c ≃ Σ (fib g c) (λ t → fib f (pr1 t))
fib-comp {A = A} {B} {C} g f c =
  ( equiv-left-swap-Σ) ∘e
  ( equiv-tot
    ( λ a →
      ( inv-assoc-Σ B (λ b → g b ＝ c) (λ u → f a ＝ pr1 u)) ∘e
      ( ( equiv-tot (λ b → commutative-prod)) ∘e
        ( ( assoc-Σ B (Id (f a)) ( λ u → g (pr1 u) ＝ c)) ∘e
          ( inv-equiv
            ( left-unit-law-Σ-is-contr
              ( is-contr-total-path (f a))
              ( pair (f a) refl)))))))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (b : B)
  where

  square-fiber :
    ( f ∘ (pr1 {B = λ x → Id (f x) b})) ~
    ( (const unit B b) ∘ (const (fib f b) unit star))
  square-fiber = pr2

  cone-fiber : cone f (const unit B b) (fib f b)
  pr1 cone-fiber = pr1
  pr1 (pr2 cone-fiber) = const (fib f b) unit star
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
