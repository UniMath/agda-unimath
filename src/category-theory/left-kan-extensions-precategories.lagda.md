# Left Kan extensions in precategories

```agda
module category-theory.left-kan-extensions-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.left-extensions-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "left Kan extension" Disambiguation="of a functor between precategories" Agda=is-left-kan-extension-Precategory}}
of [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is the universal
[left extension](category-theory.left-extensions-precategories.md) of `F` along
`p`. That is, `(L, α)` is a left Kan extension if for every other left extension
`(G, β)` there is a unique natural transformation `γ : L ⇒ G` such that
`γ ∘ α = β`. In particular, `(L, α)` is initial in the category of left
extensions of `F` along `p`.

More concretely, we require the function `left-extension-map-Precategory` to be
an equivalence.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  (R : left-extension-Precategory C C' D p F)
  where

  is-left-kan-extension-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-left-kan-extension-Precategory =
    ( G : functor-Precategory C' D) →
      is-equiv (left-extension-map-Precategory C C' D p F R G)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  where

  left-kan-extension-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  left-kan-extension-Precategory =
    Σ ( left-extension-Precategory C C' D p F)
      ( is-left-kan-extension-Precategory C C' D p F)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  (R : left-kan-extension-Precategory C C' D p F)
  where

  left-extension-left-kan-extension-Precategory :
    left-extension-Precategory C C' D p F
  left-extension-left-kan-extension-Precategory = pr1 R

  is-left-kan-extension-left-kan-extension-Precategory :
    is-left-kan-extension-Precategory C C' D p F (pr1 R)
  is-left-kan-extension-left-kan-extension-Precategory = pr2 R

  extension-left-kan-extension-Precategory :
    functor-Precategory C' D
  extension-left-kan-extension-Precategory =
    extension-left-extension-Precategory C C' D p F
      left-extension-left-kan-extension-Precategory

  natural-transformation-left-kan-extension-Precategory :
    natural-transformation-Precategory C D
      ( F)
      ( comp-functor-Precategory C C' D
        ( extension-left-extension-Precategory C C' D p F
          left-extension-left-kan-extension-Precategory)
        ( p))
  natural-transformation-left-kan-extension-Precategory =
    natural-transformation-left-extension-Precategory C C' D p F
      left-extension-left-kan-extension-Precategory
```

## See also

- [Right Kan extensions](category-theory.right-kan-extensions-precategories.md)
  for the dual concept.
