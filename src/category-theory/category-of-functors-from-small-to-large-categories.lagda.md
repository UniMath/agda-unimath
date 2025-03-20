# The category of functors and natural transformations from small to large categories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.category-of-functors-from-small-to-large-categories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories funext
open import category-theory.category-of-functors funext
open import category-theory.functors-from-small-to-large-categories funext
open import category-theory.functors-from-small-to-large-precategories funext
open import category-theory.isomorphisms-in-large-precategories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.large-categories funext
open import category-theory.large-precategories funext
open import category-theory.natural-isomorphisms-functors-categories funext
open import category-theory.natural-isomorphisms-functors-precategories funext
open import category-theory.precategories funext
open import category-theory.precategory-of-functors-from-small-to-large-precategories funext

open import foundation.equivalences funext
open import foundation.identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

[Functors](category-theory.functors-from-small-to-large-categories.md) from
small [categories](category-theory.categories.md) to
[large categories](category-theory.large-categories.md) and
[natural transformations](category-theory.natural-transformations-functors-from-small-to-large-precategories.md)
between them form a large category whose identity map and composition structure
are inherited pointwise from the codomain category. This is called the
**category of functors from small to large categories**.

## Lemmas

### Extensionality of functors from small precategories to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (is-large-category-D : is-large-category-Large-Precategory D)
  where

  equiv-natural-isomorphism-htpy-functor-is-large-category-Small-Large-Precategory :
    {γ : Level}
    (F G : functor-Small-Large-Precategory C D γ) →
    ( htpy-functor-Small-Large-Precategory C D F G) ≃
    ( natural-isomorphism-Precategory C (precategory-Large-Precategory D γ)
      ( F)
      ( G))
  equiv-natural-isomorphism-htpy-functor-is-large-category-Small-Large-Precategory
    { γ} F G =
    equiv-natural-isomorphism-htpy-functor-is-category-Precategory
      ( C)
      ( precategory-Large-Precategory D γ)
      ( is-category-is-large-category-Large-Precategory D is-large-category-D γ)
      ( F)
      ( G)

  extensionality-functor-is-category-Small-Large-Precategory :
    {γ : Level}
    (F G : functor-Small-Large-Precategory C D γ) →
    ( F ＝ G) ≃
    ( natural-isomorphism-Precategory C (precategory-Large-Precategory D γ)
      ( F)
      ( G))
  extensionality-functor-is-category-Small-Large-Precategory F G =
    ( equiv-natural-isomorphism-htpy-functor-is-large-category-Small-Large-Precategory
      ( F)
      ( G)) ∘e
    ( equiv-htpy-eq-functor-Small-Large-Precategory C D F G)
```

### When the codomain is a large category the functor large precategory is a large category

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Precategory l1 l2)
  (D : Large-Precategory α β)
  (is-large-category-D : is-large-category-Large-Precategory D)
  where

  abstract
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory :
      is-large-category-Large-Precategory
        ( functor-large-precategory-Small-Large-Precategory C D)
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory
      { γ} F G =
      is-equiv-htpy'
        ( iso-eq-Precategory
          ( functor-precategory-Small-Large-Precategory C D γ)
          ( F)
          ( G))
        ( compute-iso-eq-Large-Precategory
          ( functor-large-precategory-Small-Large-Precategory C D)
          ( F)
          ( G))
        ( is-category-functor-precategory-is-category-Precategory
          ( C)
          ( precategory-Large-Precategory D γ)
          ( is-category-is-large-category-Large-Precategory
            ( D)
            ( is-large-category-D)
            ( γ))
          ( F)
          ( G))
```

## Definition

### The large category of functors from small to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  functor-large-category-Small-Large-Category :
    Large-Category (λ l → l1 ⊔ l2 ⊔ α l ⊔ β l l) (λ l l' → l1 ⊔ l2 ⊔ β l l')
  large-precategory-Large-Category functor-large-category-Small-Large-Category =
    functor-large-precategory-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
  is-large-category-Large-Category functor-large-category-Small-Large-Category =
    is-large-category-functor-large-precategory-is-large-category-Small-Large-Precategory
      ( precategory-Category C)
      ( large-precategory-Large-Category D)
      ( is-large-category-Large-Category D)

  extensionality-functor-Small-Large-Category :
    {γ : Level} (F G : functor-Small-Large-Category C D γ) →
    (F ＝ G) ≃
    natural-isomorphism-Category C (category-Large-Category D γ) F G
  extensionality-functor-Small-Large-Category {γ} =
    extensionality-functor-Category C (category-Large-Category D γ)

  eq-natural-isomorphism-Small-Large-Category :
    {γ : Level} (F G : functor-Small-Large-Category C D γ) →
    natural-isomorphism-Category C (category-Large-Category D γ) F G → F ＝ G
  eq-natural-isomorphism-Small-Large-Category F G =
    map-inv-equiv (extensionality-functor-Small-Large-Category F G)
```

### The small categories of functors and natural transformations from small to large categories

```agda
module _
  {l1 l2 : Level} {α : Level → Level} {β : Level → Level → Level}
  (C : Category l1 l2)
  (D : Large-Category α β)
  where

  functor-category-Small-Large-Category :
    (l : Level) → Category (l1 ⊔ l2 ⊔ α l ⊔ β l l) (l1 ⊔ l2 ⊔ β l l)
  functor-category-Small-Large-Category =
    category-Large-Category (functor-large-category-Small-Large-Category C D)
```
