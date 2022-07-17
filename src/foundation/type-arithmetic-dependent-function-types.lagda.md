---
title: Type arithmetic with dependent function types
---

```agda
module foundation.type-arithmetic-dependent-function-types where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.universe-levels
```

## Properties

### The swap function `((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where
  
  swap-Π : ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
  swap-Π f y x = f x y

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  is-equiv-swap-Π : is-equiv (swap-Π {C = C})
  is-equiv-swap-Π = is-equiv-has-inverse swap-Π refl-htpy refl-htpy

  equiv-swap-Π : ((x : A) (y : B) → C x y) ≃ ((y : B) (x : A) → C x y)
  pr1 equiv-swap-Π = swap-Π
  pr2 equiv-swap-Π = is-equiv-swap-Π
```
