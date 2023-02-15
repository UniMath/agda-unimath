# Commuting triangles of homotopies

```agda
{-# OPTIONS --safe #-}

module foundation-core.commuting-triangles-of-homotopies where

open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.universe-levels
```

## Idea

A triangle of homotopies of maps

```md
 f ----> g
  \     /
   \   /
    V V
     h
```

is said to commute if there is a homotopy between the homotopy on the left and the composite homotopy.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  where

  coherence-triangle-htpy :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-htpy left right top = left ~ (top ∙h right)

  coherence-triangle-htpy' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-htpy' left right top = (top ∙h right) ~ left
```
