# Commuting triangles of maps

```agda
module foundation-core.commuting-triangles-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A triangle of maps

```text
      top
   A ----> B
    \     /
left \   / right
      V V
       X
```

is said to commute if there is a homotopy between the map on the left and the
composite map

```text
  left ~ right ∘ top.
```

## Definitions

### Commuting triangles of maps

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  coherence-triangle-maps :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps left right top = left ~ right ∘ top

  coherence-triangle-maps' :
    (left : A → X) (right : B → X) (top : A → B) → UU (l1 ⊔ l2)
  coherence-triangle-maps' left right top = right ∘ top ~ left
```

### Concatenation of commuting triangles of maps

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) (i : A → B) (j : B → C)
  where

  concat-coherence-triangle-maps :
    coherence-triangle-maps f g i →
    coherence-triangle-maps g h j →
    coherence-triangle-maps f h (j ∘ i)
  concat-coherence-triangle-maps H K =
    H ∙h (K ·r i)
```

### Any commuting triangle of maps induces a commuting triangle of function spaces

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  precomp-coherence-triangle-maps :
    coherence-triangle-maps left right top →
    ( W : UU l4) →
    coherence-triangle-maps
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps H W = htpy-precomp H W

  precomp-coherence-triangle-maps' :
    coherence-triangle-maps' left right top →
    ( W : UU l4) →
    coherence-triangle-maps'
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps' H W = htpy-precomp H W
```

### Coherences of commuting triangles of maps with fixed vertices

```agda
coherence-coherence-triangle-maps :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (top : A → B)
  (left' : A → X) (right' : B → X) (top' : A → B) →
  coherence-triangle-maps left right top →
  coherence-triangle-maps left' right' top' →
  left ~ left' → right ~ right' → top ~ top' → UU (l1 ⊔ l2)
coherence-coherence-triangle-maps left right top left' right' top' c c' L R T =
  c ∙h htpy-comp-horizontal T R ~ L ∙h c'
```
