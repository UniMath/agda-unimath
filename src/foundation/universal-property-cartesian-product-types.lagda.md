---
title: The universal propert of cartesian product types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-cartesian-product-types where

open import foundation.cartesian-product-types using (_×_)
open import foundation.cones-pullbacks using (cone)
open import foundation.constant-maps using (const)
open import foundation.contractible-types using (eq-is-contr; is-prop-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (is-equiv-has-inverse)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (refl-htpy; _~_)
open import foundation.identity-types using (refl)
open import foundation.pullbacks using
  ( canonical-pullback; gap; map-extensionality-canonical-pullback; is-pullback;
    universal-property-pullback-is-pullback)
open import foundation.unit-type using (unit; star; is-contr-unit)
open import foundation.universal-property-pullbacks using
  ( universal-property-pullback)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The universal property of cartesian products characterizes maps into a cartesian product

## Theorems

### The universal property of cartesian products as pullbacks

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  {- We construct the cone for two maps into the unit type. -}

  cone-prod : cone (const A unit star) (const B unit star) (A × B)
  pr1 cone-prod = pr1
  pr1 (pr2 cone-prod) = pr2
  pr2 (pr2 cone-prod) = refl-htpy

  {- Cartesian products are a special case of pullbacks. -}

  gap-prod : A × B → canonical-pullback (const A unit star) (const B unit star)
  gap-prod = gap (const A unit star) (const B unit star) cone-prod

  inv-gap-prod :
    canonical-pullback (const A unit star) (const B unit star) → A × B
  pr1 (inv-gap-prod (pair a (pair b p))) = a
  pr2 (inv-gap-prod (pair a (pair b p))) = b

  abstract
    issec-inv-gap-prod : (gap-prod ∘ inv-gap-prod) ~ id
    issec-inv-gap-prod (pair a (pair b p)) =
      map-extensionality-canonical-pullback
        ( const A unit star)
        ( const B unit star)
        ( refl)
        ( refl)
        ( eq-is-contr (is-prop-is-contr is-contr-unit star star))

  abstract
    isretr-inv-gap-prod : (inv-gap-prod ∘ gap-prod) ~ id
    isretr-inv-gap-prod (pair a b) = eq-pair-Σ refl refl

  abstract
    is-pullback-prod :
      is-pullback (const A unit star) (const B unit star) cone-prod
    is-pullback-prod =
      is-equiv-has-inverse
        inv-gap-prod
        issec-inv-gap-prod
        isretr-inv-gap-prod

  {- We conclude that cartesian products satisfy the universal property of 
     pullbacks. -}

  abstract
    universal-property-pullback-prod :
      {l : Level} →
      universal-property-pullback l
        ( const A unit star)
        ( const B unit star)
        ( cone-prod)
    universal-property-pullback-prod =
      universal-property-pullback-is-pullback
        ( const A unit star)
        ( const B unit star)
        ( cone-prod)
        ( is-pullback-prod)
```
