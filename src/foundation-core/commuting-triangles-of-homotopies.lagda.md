# Commuting triangles of homotopies

```agda
{-# OPTIONS --safe #-}

module foundation-core.commuting-triangles-of-homotopies where

open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
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
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  where

  coherence-triangle-htpy :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-htpy left right top = left ~ (top ∙h right)

  coherence-triangle-htpy' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-htpy' left right top = (top ∙h right) ~ left
```

## Operations

### Left whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x}
  {left : f ~ h} {right : g ~ h} {top : f ~ g}
  where

  left-whisk-coherence-triangle-htpy :
    (H : h ~ i) (T : coherence-triangle-htpy left right top) →
    coherence-triangle-htpy {h = i} (left ∙h H) (right ∙h H) top
  left-whisk-coherence-triangle-htpy H T =
    (λ x → ap (_∙ H x) (T x)) ∙h assoc-htpy top right H
```

### Right whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x}
  {left : f ~ h} {right : g ~ h} {top : f ~ g}
  where

  right-whisk-coherence-triangle-htpy :
    (T : coherence-triangle-htpy left right top) (H : i ~ f) →
    coherence-triangle-htpy {f = i} (H ∙h left) right (H ∙h top)
  right-whisk-coherence-triangle-htpy T H =
    (λ x → ap (H x ∙_) (T x)) ∙h (inv-htpy-assoc-htpy H top right)
```
