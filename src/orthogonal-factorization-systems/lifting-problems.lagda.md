---
title: Lifts of maps
---

```agda
module orthogonal-factorization-systems.lifting-problems where

open import foundation.cartesian-product-types
open import foundation.commuting-squares
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.unit-type


open import orthogonal-factorization-systems.extensions-of-maps
open import orthogonal-factorization-systems.lifts-of-maps
```

## Idea

A _lifting problem_ is the question of whether a given
commutative square

```md
       h
  A ------> B
  |         |
 f|         |g
  |         |
  V         V
  X ------> Y
       i
```

has a diagonal map `j : X → B` such that the complete
diagram

```md
       h
  A ------> B
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  X ------> Y
       i
```

commutes. This we phrase as `j` being a simultaneous
extension of `h` along `f` and lift of `i` along `g`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (h : A → B) (f : A → X) (g : B → Y) (i : X → Y) (H : coherence-square h f g i)
  where

  is-lifting-square : (j : X → B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lifting-square j = is-extension f h j × is-lift g i j

  lifting-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  lifting-square = Σ (X → B) (is-lifting-square)

  is-extension-is-lifting-square :
    (j : X → B) → is-lifting-square j → is-extension f h j
  is-extension-is-lifting-square j = pr1

  map-extension-lifting-square : lifting-square → extension f (λ _ → B) h
  pr1 (map-extension-lifting-square L) = pr1 L
  pr2 (map-extension-lifting-square L) = pr1 (pr2 L)

  is-lift-is-lifting-square :
    (j : X → B) → is-lifting-square j → is-lift g i j
  is-lift-is-lifting-square j = pr2

  map-lift-lifting-square : lifting-square → lift g i
  pr1 (map-lift-lifting-square L) = pr1 L
  pr2 (map-lift-lifting-square L) = pr2 (pr2 L)
```

## Properties

```md
       h
  A ------> B
  |       ^ |
 f|   j  /  |g
  |    /    |
  V  /      V
  X ------> Y
       i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-lifting-square-diagonal : (j : X → B) → is-lifting-square (j ∘ f) f g (g ∘ j) refl-htpy j
  pr1 (is-lifting-square-diagonal j) = refl-htpy
  pr2 (is-lifting-square-diagonal j) = refl-htpy



```

### Extensions as a retract of lifting squares

Extensions can be canonically interpreted as lifting squares where the terminal vertex is the terminal type.

```md
       h
  A ------> B
  |       ^ |
 f|   j  /  |
  |    /    |
  V  /      V
  X ----> unit
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (h : A → B) (f : A → X)
  where

  map-lifting-square-extension : extension f (λ _ → B) h → lifting-square h f (λ _ → star) (λ _ → star) refl-htpy
  pr1 (map-lifting-square-extension (j , H)) = j
  pr1 (pr2 (map-lifting-square-extension (j , H))) = H
  pr2 (pr2 (map-lifting-square-extension _)) = refl-htpy

  isretr-map-lifting-square-extension :
    ((map-extension-lifting-square h f (λ _ → star) (λ _ → star) refl-htpy) ∘ map-lifting-square-extension) ~ id
  isretr-map-lifting-square-extension = refl-htpy
```

### Lifts as a retract of lifting squares

Lifts can be canonically interpreted as lifting squares where the initial vertex is the initial type.

```md
 empty ---> B
  |       ^ |
  |   j  /  |g
  |    /    |
  V  /      V
  X ------> Y
       i
```

```agda
module _
  {l2 l3 l4 : Level} {B : UU l2} {X : UU l3} {Y : UU l4}
  (g : B → Y) (i : X → Y)
  where

  map-lifting-square-lift : lift g i → lifting-square ex-falso ex-falso g i ind-empty
  pr1 (map-lifting-square-lift (j , H)) = j
  pr1 (pr2 (map-lifting-square-lift H)) = ind-empty
  pr2 (pr2 (map-lifting-square-lift (j , H))) = H

  isretr-map-lifting-square-lift :
    ((map-lift-lifting-square ex-falso ex-falso g i ind-empty) ∘ map-lifting-square-lift) ~ id
  isretr-map-lifting-square-lift = refl-htpy
```
