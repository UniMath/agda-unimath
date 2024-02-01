# Commuting triangles of homotopies

```agda
module foundation.commuting-triangles-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.universe-levels
open import foundation.whiskering-identifications

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A triangle of [homotopies](foundation-core.homotopies.md) of dependent functions

```text
      top
    f ----> g
     \     /
 left \   / right
       ∨ ∨
        h
```

is said to commute if there is a homotopy `left ~ top ∙h right`.

## Definitions

### Coherences of commuting triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  where

  coherence-triangle-homotopies :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies left right top = left ~ top ∙h right

  coherence-triangle-homotopies' :
    (left : f ~ h) (right : g ~ h) (top : f ~ g) → UU (l1 ⊔ l2)
  coherence-triangle-homotopies' left right top = top ∙h right ~ left
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

  distributivity-left-whisker :
    coherence-triangle-homotopies left right top →
    (i ·l left) ~ ((i ·l top) ∙h (i ·l right))
  distributivity-left-whisker T x =
    map-coherence-triangle-identifications i (left x) (right x) (top x) (T x)
```

### Left whiskering triangles of homotopies

```agda
{-
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  right-whisker-coherence-triangle-homotopies :
    {i : (x : A) → B x} (H : h ~ i) →
    coherence-triangle-homotopies left right top →
    coherence-triangle-homotopies (left ∙h H) (right ∙h H) top
  right-whisker-coherence-triangle-homotopies H T x =
    right-whisker-coherence-triangle-identifications
      ( left x)
      ( right x)
      ( top x)
      ( H x)
      ( T x)
-}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  right-whisker-coherence-triangle-homotopies :
    {l3 : Level} {X : UU l3} (i : B → X)
    (T : coherence-triangle-homotopies left right top) →
    coherence-triangle-homotopies
      {f = i ∘ f} {i ∘ g} {i ∘ h}
      (i ·l left) (i ·l right) (i ·l top)
  right-whisker-coherence-triangle-homotopies i =
    distributivity-left-whisker i left right top
```

### Right whiskering triangles of homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x} (H : i ~ f) 
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  left-whisker-coherence-triangle-homotopies :
    (T : coherence-triangle-homotopies left right top)→
    coherence-triangle-homotopies {f = i} (H ∙h left) right (H ∙h top)
  left-whisker-coherence-triangle-homotopies T x =
    left-whisker-coherence-triangle-identifications
      ( H x)
      ( left x)
      ( right x)
      ( top x)
      ( T x)

{-
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g h : A → B}
  {left : f ~ h} (right : g ~ h) {top : f ~ g}
  where

  left-whisker-coherence-triangle-homotopies :
    {l3 : Level} {X : UU l3}
    (T : coherence-triangle-homotopies left right top) (i : X → A) →
    coherence-triangle-homotopies
      {f = f ∘ i} {g ∘ i} {h ∘ i}
      (left ·r i) (right ·r i) (top ·r i)
  left-whisker-coherence-triangle-homotopies T i = T ∘ i
-}
```
