---
title: Path-split maps
---

```agda
module foundation-core.path-split-maps where

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.universe-levels
```

## Idea

A map `f : A → B` is said to be path split if it has a section and its action on identity types `Id x y → Id (f x) (f y)` has a section for each `x y : A`. By the fundamental theorem for identity types, it follows that a map is path-split if and only if it is an equivalence.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-path-split : UU (l1 ⊔ l2)
  is-path-split = sec f × ((x y : A) → sec (ap f {x = x} {y = y}))
```

## Properties

### A map is path-split if and only if it is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-path-split-is-equiv : is-equiv f → is-path-split f
    is-path-split-is-equiv is-equiv-f =
      pair (pr1 is-equiv-f) (λ x y → pr1 (is-emb-is-equiv is-equiv-f x y))

  abstract
    is-coherently-invertible-is-path-split :
      is-path-split f → is-coherently-invertible f
    is-coherently-invertible-is-path-split (pair (pair g issec-g) sec-ap-f) =
      ( pair
        ( g)
        ( pair
          ( issec-g)
          ( pair
            ( λ x → pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
            ( λ x → inv (pr2 (sec-ap-f (g (f x)) x) (issec-g (f x)))))))

  abstract
    is-equiv-is-path-split : is-path-split f → is-equiv f
    is-equiv-is-path-split =
      is-equiv-is-coherently-invertible ∘
      is-coherently-invertible-is-path-split
```

## See also

- For the notion of biinvertible maps see
  [foundation.equivalences](foundation.equivalences.html).
- For the notions of inverses and coherently invertible maps, also known as half-adjoint equivalences, see
  [foundation.coherently-invertible-maps](foundation.coherently-invertible-maps.html).
- For the notion of maps with contractible fibers see
  [foundation.contractible-maps](foundation.contractible-maps.html).
