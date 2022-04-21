---
title: Double powersets
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.double-powersets where

open import foundation.powersets
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.posets
```

## Definitions

```agda
module _
  {l1 : Level} (l2 : Level)
  where
  
  double-powerset-Large-Poset :
    UU l1 →
    Large-Poset
      ( λ l3 → l1 ⊔ lsuc l2 ⊔ lsuc l3)
      ( λ l3 l4 → l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
  double-powerset-Large-Poset A = powerset-Large-Poset (subtype l2 A)

  double-powerset-Poset :
    (l : Level) → UU l1 → Poset (l1 ⊔ lsuc l2 ⊔ lsuc l) (l1 ⊔ lsuc l2 ⊔ l)
  double-powerset-Poset l A =
    poset-Large-Poset (double-powerset-Large-Poset A) l

  double-powerset : (l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
  double-powerset l3 A = element-Poset (double-powerset-Poset l3 A)
```
