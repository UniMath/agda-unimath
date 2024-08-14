# Right extensions in precategories

```agda
module category-theory.right-extensions-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "right extension" Disambiguation="of a functor between precategories" Agda=right-extension-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is a functor `G : C' → D` together with a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
`φ : G ∘ p → F`.

```text
  C
  |  \
  p    F
  |      \
  ∨        ∨
  C' - G -> D
```

We note that this is not a standard definition, but it inspired by the notion of
a [right kan extension](category-theory.right-kan-extensions-precategories.md).

## Definition

### Right extensions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  where

  right-extension-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  right-extension-Precategory =
    Σ ( functor-Precategory C' D)
      ( λ G →
        natural-transformation-Precategory C D
          ( comp-functor-Precategory C C' D G p)
          ( F))

  module _
    (R : right-extension-Precategory)
    where

    extension-right-extension-Precategory : functor-Precategory C' D
    extension-right-extension-Precategory = pr1 R

    natural-transformation-right-extension-Precategory :
      natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
    natural-transformation-right-extension-Precategory = pr2 R

    hom-family-right-extension-Precategory :
      hom-family-functor-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
    hom-family-right-extension-Precategory =
      hom-family-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( natural-transformation-right-extension-Precategory)

    naturality-right-extension-Precategory :
      is-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( hom-family-right-extension-Precategory)
    naturality-right-extension-Precategory =
      naturality-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D
          ( extension-right-extension-Precategory)
          ( p))
        ( F)
        ( natural-transformation-right-extension-Precategory)
```

### Precomposing right extensions

```agda
    right-extension-map-Precategory :
      ( G : functor-Precategory C' D) →
      ( natural-transformation-Precategory C' D
        G extension-right-extension-Precategory) →
      ( natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D G p) F)
    right-extension-map-Precategory G φ =
      comp-natural-transformation-Precategory C D
        ( comp-functor-Precategory C C' D G p)
        ( comp-functor-Precategory C C' D
          extension-right-extension-Precategory p)
        ( F)
        ( natural-transformation-right-extension-Precategory)
        ( right-whisker-natural-transformation-Precategory C' D C
          ( G)
          ( extension-right-extension-Precategory)
          ( φ)
          ( p))
```
