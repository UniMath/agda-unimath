# Cones in precategories

```agda
module category-theory.cones-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors
open import category-theory.right-extensions-precategories
open import category-theory.terminal-category

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "cone" Disambiguation="over a functor of precategories" Agda=cone-Precategory}}
over a [functor](category-theory.functors-precategories.md) `F` of
[precategories](category-theory.precategories.md) is a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from a [constant functor](category-theory.constant-functors.md) to `F`.

In this context, we usually think of (and refer to) the functor `F` as a
**diagram** in its codomain, A cone over such diagram then corresponds to an
element `d`, called the **vertex** of the cone, equipped with components
`d → F x` satisfying the naturality condition.

For example, if `F` corresponds to the diagram `F x → F y`, then a cone over `F`
corresponds to a commuting triangle as below.

```text
      d
    /   \
   /     \
  ∨       ∨
 Fx ----> Fy
```

Equivalently, we can see a cone over `F` as a
[right extension](category-theory.right-extensions-precategories.md) of `F`
along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

## Definitions

### The type of cones over a functor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  cone-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cone-Precategory =
    Σ ( obj-Precategory D)
      ( λ d →
        natural-transformation-Precategory C D
          ( constant-functor-Precategory C D d)
          ( F))

  vertex-cone-Precategory : cone-Precategory → obj-Precategory D
  vertex-cone-Precategory = pr1

  vertex-functor-cone-Precategory :
    cone-Precategory → functor-Precategory C D
  vertex-functor-cone-Precategory α =
    constant-functor-Precategory C D (vertex-cone-Precategory α)

  natural-transformation-cone-Precategory :
    (α : cone-Precategory) →
    natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
  natural-transformation-cone-Precategory = pr2

  component-cone-Precategory :
    (α : cone-Precategory) (x : obj-Precategory C) →
    hom-Precategory D
      ( vertex-cone-Precategory α)
      ( obj-functor-Precategory C D F x)
  component-cone-Precategory α =
    hom-family-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)

  naturality-cone-Precategory :
    (α : cone-Precategory) {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F f)
      ( component-cone-Precategory α x) ＝
    component-cone-Precategory α y
  naturality-cone-Precategory α {x} {y} f =
    naturality-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)
      ( f) ∙
    right-unit-law-comp-hom-Precategory D _
```

## Properties

### A cone is a right extension along the terminal map

```agda
  vertex-right-extension-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    obj-Precategory D
  vertex-right-extension-Precategory R =
    obj-functor-Precategory terminal-Precategory D
      ( extension-right-extension-Precategory C terminal-Precategory D
        ( terminal-functor-Precategory C) F R)
      ( star)

  cone-right-extension-Precategory :
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F → cone-Precategory
  pr1 (cone-right-extension-Precategory R) =
    vertex-right-extension-Precategory R
  pr1 (pr2 (cone-right-extension-Precategory R)) =
    hom-family-natural-transformation-Precategory C D
      ( comp-functor-Precategory C terminal-Precategory D
        ( extension-right-extension-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) F R)
        ( terminal-functor-Precategory C))
      ( F)
      ( natural-transformation-right-extension-Precategory
        C terminal-Precategory D
        ( terminal-functor-Precategory C) F R)
  pr2 (pr2 (cone-right-extension-Precategory R)) {x} {y} f =
    naturality-natural-transformation-Precategory C D
      ( comp-functor-Precategory C terminal-Precategory D
        ( extension-right-extension-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) F R)
        ( terminal-functor-Precategory C))
      ( F)
      ( natural-transformation-right-extension-Precategory
        C terminal-Precategory D
        ( terminal-functor-Precategory C) F R) f ∙
          ap
            ( comp-hom-Precategory D
              ( hom-family-right-extension-Precategory C terminal-Precategory D
                ( terminal-functor-Precategory C) F R y))
            ( preserves-id-functor-Precategory terminal-Precategory D
              ( extension-right-extension-Precategory C terminal-Precategory D
                ( terminal-functor-Precategory C) F R)
                ( star))

  right-extension-cone-Precategory :
    cone-Precategory →
    right-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  pr1 (right-extension-cone-Precategory τ) =
    constant-functor-Precategory
      terminal-Precategory D (vertex-cone-Precategory τ)
  pr1 (pr2 (right-extension-cone-Precategory τ)) =
    component-cone-Precategory τ
  pr2 (pr2 (right-extension-cone-Precategory τ)) f =
    naturality-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory τ)
      ( F)
      ( natural-transformation-cone-Precategory τ)
      ( f)
```
