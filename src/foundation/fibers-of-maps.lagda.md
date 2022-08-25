---
title: Fibers of maps
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.fibers-of-maps where

open import foundation-core.fibers-of-maps public

open import foundation-core.cones-pullbacks using (cone)
open import foundation-core.constant-maps using (const)
open import foundation-core.contractible-types using (is-contr-total-path)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; _∘e_; inv-equiv)
open import foundation-core.function-extensionality using (eq-htpy)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.functoriality-dependent-pair-types using
  ( equiv-tot; is-equiv-tot-is-fiberwise-equiv)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (Id; _＝_; refl)
open import foundation-core.pullbacks using
  ( is-pullback; universal-property-pullback-is-pullback)
open import foundation-core.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation-core.type-arithmetic-dependent-pair-types using
  ( equiv-left-swap-Σ; inv-assoc-Σ; assoc-Σ; left-unit-law-Σ-is-contr)
open import foundation-core.universal-property-pullbacks using
  ( universal-property-pullback)
open import foundation-core.universe-levels using (Level; UU)

-- open import foundation.pullbacks
open import foundation.type-arithmetic-unit-type using
  ( is-equiv-map-inv-left-unit-law-prod)
open import foundation.unit-type using (unit; star)
-- open import foundation.universal-property-pullbacks using
--   ( cone; universal-property-pullback)
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
