# Decidable maps

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.decidable-maps where

open import foundation.decidable-types using (is-decidable)
open import foundation.fibers-of-maps using (fib)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Definition

A map is said to be decidable if its fibers are decidable types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)
```
