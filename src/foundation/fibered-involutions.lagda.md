---
title: Fibered involutions
---

```agda
module foundation.fibered-involutions where

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.involutions
open import foundation-core.universe-levels

open import foundation.fibered-maps
```

## Idea

A fibered involution is a fibered map

```md
       h
  A -------> A
  |          |
 f|          |g
  |          |
  V          V
  X -------> X
       i
```

such that both `i` and `h` are involutions.

## Definition

```agda
involution-over :
  {l1 l2 l3 : Level} {A : UU l1} {X : UU l2} {Y : UU l3} →
  (A → X) → (A → Y) → (X → Y) → UU (l1 ⊔ l3)
involution-over {A = A} f g i = Σ (involution A) (is-map-over f g i ∘ map-involution)

fibered-involution :
  {l1 l2 : Level} {A : UU l1} {X : UU l2} →
  (A → X) → (A → X) → UU (l1 ⊔ l2)
fibered-involution {X = X} f g = Σ (involution X) (involution-over f g ∘ map-involution)

is-fiberwise-involution : 
  {l1 l2 : Level} {X : UU l1} {P : X → UU l2} →
  ((x : X) → P x → P x) → UU (l1 ⊔ l2)
is-fiberwise-involution {X = X} f = (x : X) → is-involution (f x)

fam-involution : 
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) → UU (l1 ⊔ l2)
fam-involution {X = X} P = (x : X) → involution (P x)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {X : UU l2}
  (f g : A → X)
  where

  is-fibered-involution-fibered-map : fibered-map f g → UU (l1 ⊔ l2)
  is-fibered-involution-fibered-map (i , h , H) = is-involution i × is-involution h

  map-Σ-is-fibered-involution-fibered-map-fibered-involution :
    (fibered-involution f g) → Σ (fibered-map f g) (is-fibered-involution-fibered-map)
  map-Σ-is-fibered-involution-fibered-map-fibered-involution
    ((i , is-involution-i) , (h , is-involution-h) , H) = (i , h , H) , is-involution-i , is-involution-h

  map-fibered-involution-Σ-is-fibered-involution-fibered-map :
    (Σ (fibered-map f g) (is-fibered-involution-fibered-map)) → (fibered-involution f g)
  map-fibered-involution-Σ-is-fibered-involution-fibered-map
    ((i , h , H) , is-involution-i , is-involution-h) = ((i , is-involution-i) , (h , is-involution-h), H)

  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involution :
    is-equiv (map-Σ-is-fibered-involution-fibered-map-fibered-involution)
  is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involution =
    is-equiv-has-inverse
      ( map-fibered-involution-Σ-is-fibered-involution-fibered-map)
      ( refl-htpy)
      ( refl-htpy)

  equiv-Σ-is-fibered-involution-fibered-map-fibered-involution :
    (fibered-involution f g) ≃ Σ (fibered-map f g) (is-fibered-involution-fibered-map)
  equiv-Σ-is-fibered-involution-fibered-map-fibered-involution =
    pair
      map-Σ-is-fibered-involution-fibered-map-fibered-involution 
      is-equiv-map-Σ-is-fibered-involution-fibered-map-fibered-involution

  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-map :
    is-equiv (map-fibered-involution-Σ-is-fibered-involution-fibered-map)
  is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-map =
    is-equiv-has-inverse
      ( map-Σ-is-fibered-involution-fibered-map-fibered-involution)
      ( refl-htpy)
      ( refl-htpy)

  equiv-fibered-involution-Σ-is-fibered-involution-fibered-map :
    Σ (fibered-map f g) (is-fibered-involution-fibered-map) ≃ (fibered-involution f g)
  equiv-fibered-involution-Σ-is-fibered-involution-fibered-map =
    pair
      map-fibered-involution-Σ-is-fibered-involution-fibered-map 
      is-equiv-map-fibered-involution-Σ-is-fibered-involution-fibered-map
```
