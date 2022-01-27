---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.path-split-maps where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coherently-invertible-maps using
  ( is-coherently-invertible)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb-is-equiv)
open import foundation.equivalences using
  ( sec; is-equiv; is-equiv-has-inverse)
open import foundation.functions using (_∘_)
open import foundation.identity-types using (ap; inv)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

# Path-split maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-path-split : UU (l1 ⊔ l2)
  is-path-split = sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

  abstract
    is-path-split-is-equiv : is-equiv f → is-path-split
    pr1 (is-path-split-is-equiv is-equiv-f) = pr1 is-equiv-f
    pr2 (is-path-split-is-equiv is-equiv-f) x y =
      pr1 (is-emb-is-equiv is-equiv-f x y)

  abstract
    is-coherently-invertible-is-path-split :
      is-path-split → is-coherently-invertible f
    pr1
      ( is-coherently-invertible-is-path-split
        ( pair (pair g issec-g) sec-ap-f)) = g
    pr1
      ( pr2
        ( is-coherently-invertible-is-path-split
          ( pair (pair g issec-g) sec-ap-f))) = issec-g
    pr1
      ( pr2
        ( pr2
          ( is-coherently-invertible-is-path-split
            ( pair (pair g issec-g) sec-ap-f)))) x =
      pr1 (sec-ap-f (g (f x)) x) (issec-g (f x))
    pr2
      ( pr2
        ( pr2
          ( is-coherently-invertible-is-path-split
            ( pair (pair g issec-g) sec-ap-f)))) x =
      inv (pr2 (sec-ap-f (g (f x)) x) (issec-g (f x)))
         
  abstract
    is-equiv-is-coherently-invertible :
      is-coherently-invertible f → is-equiv f
    is-equiv-is-coherently-invertible (pair g (pair G (pair H K))) =
      is-equiv-has-inverse g G H

  abstract
    is-equiv-is-path-split : is-path-split → is-equiv f
    is-equiv-is-path-split =
      is-equiv-is-coherently-invertible ∘ is-coherently-invertible-is-path-split
```
