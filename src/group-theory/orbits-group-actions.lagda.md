# Orbits of group actions

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.orbits-group-actions where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import group-theory.group-actions using
  ( Abstract-Group-Action; type-Abstract-Group-Action;
    mul-Abstract-Group-Action)
open import group-theory.groups using (Group; type-Group)
```

## Idea

The orbit of an element `x` in a G-set `X` is the set of elements of the form `gx`.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : Abstract-Group-Action G l2)
  where

  hom-orbit-Abstract-Group-Action :
    (x y : type-Abstract-Group-Action G X) → UU (l1 ⊔ l2)
  hom-orbit-Abstract-Group-Action x y =
    Σ (type-Group G) (λ g → Id (mul-Abstract-Group-Action G X g x) y)
```

