# Equivalences between precategories

```agda
module category-theory.equivalences-of-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-isomorphisms-precategories
open import category-theory.precategories

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A functor `F : C → D` is an equivalence of categories if there is a functor
`G : D → C` such that:

- `G ∘ F` is naturally isomorphic to the identity functor on `C`,
- `F ∘ G` is naturally isomorphic to the identity functor on `D`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  is-equiv-functor-Precategory :
    functor-Precategory C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Precategory F =
    Σ ( functor-Precategory D C)
      ( λ G →
        ( natural-isomorphism-Precategory C C
          ( comp-functor-Precategory C D C G F)
          ( id-functor-Precategory C))) ×
    Σ ( functor-Precategory D C)
      ( λ G →
        ( natural-isomorphism-Precategory D D
          ( comp-functor-Precategory D C D F G)
          ( id-functor-Precategory D)))

  equiv-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Precategory = Σ (functor-Precategory C D) is-equiv-functor-Precategory
```
