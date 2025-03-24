# Equivalences between precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.equivalences-of-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories funext univalence truncations
open import category-theory.natural-isomorphisms-functors-precategories funext univalence truncations
open import category-theory.precategories funext univalence truncations

open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` is an
**equivalence** of [precategories](category-theory.precategories.md) if there is

1. a functor `G : D → C` such that `G ∘ F` is
   [naturally isomorphic](category-theory.natural-isomorphisms-functors-precategories.md)
   to the identity functor on `C`,
2. a functor `H : D → C` such that `F ∘ H` is naturally isomorphic to the
   identity functor on `D`.

## Definition

### The predicate on functors of being an equivalence of precategories

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
      ( λ H →
        ( natural-isomorphism-Precategory D D
          ( comp-functor-Precategory D C D F H)
          ( id-functor-Precategory D)))
```

### The type of equivalences of precategories

```agda
  equiv-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-Precategory = Σ (functor-Precategory C D) (is-equiv-functor-Precategory)
```
