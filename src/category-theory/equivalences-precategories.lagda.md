# Equivalences between precategories

```agda
module category-theory.equivalences-precategories where
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

A functor `F : C → D` is an equivalence of categories if there is a functor `G : D → C` such that:
- `comp G F` is naturally isomorphic to the identity functor on `C`,
- `comp F G` is naturally isomorphic to the identity functor on `D`.

## Definition

```agda
module _ {l1 l2 l3 l4}
  (C : Precat l1 l2)
  (D : Precat l3 l4) where

  is-equiv-functor-Precat : functor-Precat C D → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-equiv-functor-Precat F =
    Σ ( functor-Precat D C)
      ( λ G →
        ( nat-iso-Precat C C
          ( comp-functor-Precat C D C G F)
          ( id-functor-Precat C))) ×
    Σ ( functor-Precat D C)
      ( λ G →
        ( nat-iso-Precat D D
          ( comp-functor-Precat D C D F G)
          ( id-functor-Precat D)))

  equiv-Precat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Precat = Σ (functor-Precat C D) is-equiv-functor-Precat
```
