# Commuting triangles of maps

```agda
module foundation.commuting-triangles-of-maps where

open import foundation-core.commuting-triangles-of-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

A triangle of maps

```text
 A ----> B
  \     /
   \   /
    ∨ ∨
     X
```

is said to **commute** if there is a [homotopy](foundation-core.homotopies.md)
between the map on the left and the composite map.

## Properties

### Top map is an equivalence

If the top map is an [equivalence](foundation-core.equivalences.md), then there
is an equivalence between the coherence triangle with the map of the equivalence
as with the inverse map of the equivalence.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (e : A ≃ B)
  where

  equiv-coherence-triangle-maps-inv-top' :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps' right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top' =
    equiv-Π
      ( λ b → left (map-inv-equiv e b) ＝ right b)
      ( e)
      ( λ a →
        equiv-concat
          ( ap left (is-retraction-map-inv-equiv e a))
          ( right (map-equiv e a)))

  equiv-coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) ≃
    coherence-triangle-maps right left (map-inv-equiv e)
  equiv-coherence-triangle-maps-inv-top =
    ( equiv-inv-htpy
      ( left ∘ (map-inv-equiv e))
      ( right)) ∘e
    ( equiv-coherence-triangle-maps-inv-top')

  coherence-triangle-maps-inv-top :
    coherence-triangle-maps left right (map-equiv e) →
    coherence-triangle-maps right left (map-inv-equiv e)
  coherence-triangle-maps-inv-top =
    map-equiv equiv-coherence-triangle-maps-inv-top
```

### Commuting triangles of maps induce commuting triangles of precomposition maps

Given a commuting triangle of maps

```text
       f
   A ----> B
    \  ⇗  /
   h \   / g
      ∨ ∨
       X
```

there is an induced commuting triangle of
[precomposition maps](foundation-core.precomposition-functions.md)

```text
         (- ∘ g)
  (X → S) ----> (B → S)
        \   ⇗  /
  (- ∘ h) \   / (- ∘ f)
           ∨ ∨
         (A → S).
```

Note the change of order of `f` and `g`.

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  precomp-coherence-triangle-maps :
    coherence-triangle-maps left right top →
    (S : UU l4) →
    coherence-triangle-maps
      ( precomp left S)
      ( precomp top S)
      ( precomp right S)
  precomp-coherence-triangle-maps = htpy-precomp

  precomp-coherence-triangle-maps' :
    coherence-triangle-maps' left right top →
    (S : UU l4) →
    coherence-triangle-maps'
      ( precomp left S)
      ( precomp top S)
      ( precomp right S)
  precomp-coherence-triangle-maps' = htpy-precomp
```

### Commuting triangles of maps induce commuting triangles of postcomposition maps

Given a commuting triangle of maps

```text
       f
   A ----> B
    \  ⇗  /
   h \   / g
      ∨ ∨
       X
```

there is an induced commuting triangle of
[postcomposition maps](foundation-core.postcomposition-functions.md)

```text
         (f ∘ -)
  (S → A) ----> (S → B)
        \   ⇗  /
  (h ∘ -) \   / (g ∘ -)
           ∨ ∨
         (S → X).
```

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  postcomp-coherence-triangle-maps :
    (S : UU l4) →
    coherence-triangle-maps left right top →
    coherence-triangle-maps
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S top)
  postcomp-coherence-triangle-maps S = htpy-postcomp S

  postcomp-coherence-triangle-maps' :
    (S : UU l4) →
    coherence-triangle-maps' left right top →
    coherence-triangle-maps'
      ( postcomp S left)
      ( postcomp S right)
      ( postcomp S top)
  postcomp-coherence-triangle-maps' S = htpy-postcomp S
```

### Coherences of commuting triangles of maps with fixed vertices

This or its opposite should be the coherence in the characterization of
identifications of commuting triangles of maps with fixed end vertices.

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (left : A → X) (right : B → X) (top : A → B)
  (left' : A → X) (right' : B → X) (top' : A → B)
  (c : coherence-triangle-maps left right top)
  (c' : coherence-triangle-maps left' right' top')
  where

  coherence-htpy-triangle-maps :
    left ~ left' → right ~ right' → top ~ top' → UU (l1 ⊔ l2)
  coherence-htpy-triangle-maps L R T =
    c ∙h horizontal-concat-htpy R T ~ L ∙h c'
```

### Pasting commuting triangles into commuting squares along homotopic diagonals

Two [commuting triangles](foundation-core.commuting-triangles-of-maps.md)

```text
   A         A --> X
  | \         \    |
  |  \ H  L  K \   |
  |   \         \  |
  ∨    ∨         ∨ ∨
  B --> Y         Y
```

with a [homotopic](foundation-core.homotopies.md) diagonal may be pasted into a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
  A -----> X
  |        |
  |        |
  ∨        ∨
  B -----> Y.
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  where

  horizontal-pasting-htpy-coherence-triangle-maps :
    {diagonal-left diagonal-right : A → Y} →
    diagonal-left ~ diagonal-right →
    coherence-triangle-maps' diagonal-left bottom left →
    coherence-triangle-maps diagonal-right right top →
    coherence-square-maps top left right bottom
  horizontal-pasting-htpy-coherence-triangle-maps L H K = (H ∙h L) ∙h K

  horizontal-pasting-htpy-coherence-triangle-maps' :
    {diagonal-left diagonal-right : A → Y} →
    diagonal-left ~ diagonal-right →
    coherence-triangle-maps' diagonal-left bottom left →
    coherence-triangle-maps diagonal-right right top →
    coherence-square-maps top left right bottom
  horizontal-pasting-htpy-coherence-triangle-maps' L H K = H ∙h (L ∙h K)

  horizontal-pasting-coherence-triangle-maps :
    (diagonal : A → Y) →
    coherence-triangle-maps' diagonal bottom left →
    coherence-triangle-maps diagonal right top →
    coherence-square-maps top left right bottom
  horizontal-pasting-coherence-triangle-maps diagonal H K = H ∙h K

  compute-refl-htpy-horizontal-pasting-coherence-triangle-maps :
    (diagonal : A → Y) →
    (H : coherence-triangle-maps' diagonal bottom left) →
    (K : coherence-triangle-maps diagonal right top) →
    horizontal-pasting-htpy-coherence-triangle-maps refl-htpy H K ~
    horizontal-pasting-coherence-triangle-maps diagonal H K
  compute-refl-htpy-horizontal-pasting-coherence-triangle-maps diagonal H K x =
    right-whisker-concat right-unit (K x)
```

We can also consider pasting triangles of the form

```text
  A --> X      X
  |    ∧     ∧ |
  | H /     /  |
  |  /     / K |
  ∨ /     /    ∨
  B      B --> Y .
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → X) (left : A → B) (right : X → Y) (bottom : B → Y)
  {diagonal : B → X}
  where

  horizontal-pasting-up-diagonal-coherence-triangle-maps :
    coherence-triangle-maps' top diagonal left →
    coherence-triangle-maps bottom right diagonal →
    coherence-square-maps top left right bottom
  horizontal-pasting-up-diagonal-coherence-triangle-maps H K =
    (K ·r left) ∙h (right ·l H)
```
