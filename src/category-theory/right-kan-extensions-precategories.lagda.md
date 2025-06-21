# Right Kan extensions in precategories

```agda
module category-theory.right-kan-extensions-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.right-extensions-precategories

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "right Kan extension" Disambiguation="of a functor between precategories" Agda=is-right-kan-extension-Precategory}}
of [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) along another functor
`p : C → C'` is the universal
[right extension](category-theory.right-extensions-precategories.md) of `F`
along `p`. That is, `(R, α)` is a right Kan extension if for every other right
extension `(G, β)` there is a unique natural transformation `γ : G ⇒ R` such
that `α ∘ γ = β`. In particular, `(R, α)` is terminal in the category of right
extensions of `F` along `p`.

More concretely, we require the function `right-extension-map-Precategory` to be
an equivalence.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  (R : right-extension-Precategory C C' D p F)
  where

  is-right-kan-extension-Precategory :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-right-kan-extension-Precategory =
    ( G : functor-Precategory C' D) →
      is-equiv (right-extension-map-Precategory C C' D p F R G)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  where

  right-kan-extension-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  right-kan-extension-Precategory =
    Σ ( right-extension-Precategory C C' D p F)
      ( is-right-kan-extension-Precategory C C' D p F)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (C : Precategory l1 l2) (C' : Precategory l3 l4) (D : Precategory l5 l6)
  (p : functor-Precategory C C') (F : functor-Precategory C D)
  (R : right-kan-extension-Precategory C C' D p F)
  where

  right-extension-right-kan-extension-Precategory :
    right-extension-Precategory C C' D p F
  right-extension-right-kan-extension-Precategory = pr1 R

  is-right-kan-extension-right-kan-extension-Precategory :
    is-right-kan-extension-Precategory C C' D p F (pr1 R)
  is-right-kan-extension-right-kan-extension-Precategory = pr2 R

  extension-right-kan-extension-Precategory :
    functor-Precategory C' D
  extension-right-kan-extension-Precategory =
    extension-right-extension-Precategory C C' D p F
      right-extension-right-kan-extension-Precategory

  natural-transformation-right-kan-extension-Precategory :
    natural-transformation-Precategory C D
      ( comp-functor-Precategory C C' D
        ( extension-right-extension-Precategory C C' D p F
          right-extension-right-kan-extension-Precategory)
        ( p))
      ( F)
  natural-transformation-right-kan-extension-Precategory =
    natural-transformation-right-extension-Precategory C C' D p F
      right-extension-right-kan-extension-Precategory
```

## See also

- [Left Kan extensions](category-theory.left-kan-extensions-precategories.md)
  for the dual concept.
