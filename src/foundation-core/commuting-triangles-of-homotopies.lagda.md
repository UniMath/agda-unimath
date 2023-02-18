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

  htpy-coherence-triangle :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  htpy-coherence-triangle left right top = left ~ (top ∙h right)

  htpy-coherence-triangle' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  htpy-coherence-triangle' left right top = (top ∙h right) ~ left
```

## Properties

### Distributive law for left whiskering

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {l3 : Level} {X : UU l3} (i : B → X)
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  distributivity-left-whisk :
    htpy-coherence-triangle left right top →
    (i ·l left) ~ ((i ·l top) ∙h (i ·l right))
  distributivity-left-whisk T x =
    ap-concat-eq i (top x) (right x) (left x) (T x)
```

### Left whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  left-whisk-htpy-htpy-coherence-triangle :
    {i : (x : A) → B x}
    (H : h ~ i) (T : htpy-coherence-triangle left right top) →
    htpy-coherence-triangle {h = i} (left ∙h H) (right ∙h H) top
  left-whisk-htpy-htpy-coherence-triangle H T =
    (λ x → ap (_∙ H x) (T x)) ∙h assoc-htpy top right H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  left-whisk-htpy-coherence-triangle :
    {l3 : Level} {X : UU l3} (i : B → X) (T : htpy-coherence-triangle left right top) →
    htpy-coherence-triangle {f = i ∘ f} {i ∘ g} {i ∘ h} (i ·l left) (i ·l right) (i ·l top)
  left-whisk-htpy-coherence-triangle i =
    distributivity-left-whisk i left right top
```

### Right whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  right-whisk-htpy-htpy-coherence-triangle :
    {i : (x : A) → B x}
    (T : htpy-coherence-triangle left right top) (H : i ~ f) →
    htpy-coherence-triangle {f = i} (H ∙h left) right (H ∙h top)
  right-whisk-htpy-htpy-coherence-triangle T H =
    (λ x → ap (H x ∙_) (T x)) ∙h (inv-htpy-assoc-htpy H top right)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  right-whisk-htpy-coherence-triangle :
    {l3 : Level} {X : UU l3} (T : htpy-coherence-triangle left right top) (i : X → A) →
    htpy-coherence-triangle {f = f ∘ i} {g ∘ i} {h ∘ i} (left ·r i) (right ·r i) (top ·r i)
  right-whisk-htpy-coherence-triangle T i = T ∘ i
```
