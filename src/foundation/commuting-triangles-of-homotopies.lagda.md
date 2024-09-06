# Commuting triangles of homotopies

```agda
module foundation.commuting-triangles-of-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
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

is said to
{{#concept "commute" Disambiguation="triangle of homotopies" Agda=coherence-triangle-homotopies}}
if there is a homotopy `left ~ top ∙h right`.

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

### Left whiskering commuting triangles of homotopies with respect to concatenation of homotopies

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f g h : (x : A) → B x`, and consider a homotopy `H : i ~ f` for a fourth
dependent function `i : (x : A) → B x`. Then the triangle of homotopies

```text
           H ∙h top
         i --------> g
           \       /
  H ∙h left \     / right
             \   /
              ∨ ∨
               h
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h i : (x : A) → B x} (H : i ~ f)
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  left-whisker-concat-coherence-triangle-homotopies :
    (T : coherence-triangle-homotopies left right top) →
    coherence-triangle-homotopies (H ∙h left) right (H ∙h top)
  left-whisker-concat-coherence-triangle-homotopies T x =
    left-whisker-concat-coherence-triangle-identifications
      ( H x)
      ( left x)
      ( right x)
      ( top x)
      ( T x)
```

### Right whiskering triangles of homotopies with respect to concatenation of homotopies

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f g h : (x : A) → B x`, and consider a homotopy `H : h ~ i` for a fourth
dependent function `i : (x : A) → B x`. Then the triangle of homotopies

```text
              top
         f --------> g
           \       /
  left ∙h H \     / right ∙h H
             \   /
              ∨ ∨
               i
```

commutes.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {f g h : (x : A) → B x}
  (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  right-whisker-concat-coherence-triangle-homotopies :
    coherence-triangle-homotopies left right top →
    {i : (x : A) → B x} (H : h ~ i) →
    coherence-triangle-homotopies (left ∙h H) (right ∙h H) top
  right-whisker-concat-coherence-triangle-homotopies T H x =
    right-whisker-concat-coherence-triangle-identifications
      ( left x)
      ( right x)
      ( top x)
      ( H x)
      ( T x)
```

### Left whiskering of commuting triangles of homotopies with respect to composition

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f`, `g`, and `h` are maps `A → B`. Furthermore, consider a map
`i : B → X`. Then we obtain a commuting triangle of homotopies

```text
           i ·l top
     i ∘ f --------> i ∘ g
           \       /
  i ·l left \     / i ·l right
             \   /
              ∨ ∨
             i ∘ h.
```

This notion of whiskering should be compared to
[whiskering higher homotopies with respect to composition](foundation.whiskering-higher-homotopies-composition.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (i : B → X)
  {f g h : A → B} (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  left-whisker-comp-coherence-triangle-homotopies :
    (T : coherence-triangle-homotopies left right top) →
    coherence-triangle-homotopies (i ·l left) (i ·l right) (i ·l top)
  left-whisker-comp-coherence-triangle-homotopies T x =
    map-coherence-triangle-identifications i (left x) (right x) (top x) (T x)
```

### Right whiskering commuting triangles of homotopies with respect to composition

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f`, `g`, and `h` are maps `A → B`. Furthermore, consider a map
`i : X → A`. Then we obtain a commuting triangle of homotopies

```text
           top ·r i
     f ∘ i --------> g ∘ i
           \       /
  left ·r i \     / right ·r i
             \   /
              ∨ ∨
             h ∘ i.
```

This notion of whiskering should be compared to
[whiskering higher homotopies with respect to composition](foundation.whiskering-higher-homotopies-composition.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  {f g h : A → B} (left : f ~ h) (right : g ~ h) (top : f ~ g)
  where

  right-whisker-comp-coherence-triangle-homotopies :
    (T : coherence-triangle-homotopies left right top) (i : X → A) →
    coherence-triangle-homotopies (left ·r i) (right ·r i) (top ·r i)
  right-whisker-comp-coherence-triangle-homotopies T i = T ∘ i
```
