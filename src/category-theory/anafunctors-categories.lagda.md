# Anafunctors between categories

```agda
module category-theory.anafunctors-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.anafunctors-precategories
open import category-theory.categories
open import category-theory.functors-categories

open import foundation.dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

An **anafunctor** is a [functor](category-theory.functors-categories.md) that is
only defined up to [isomorphism](category-theory.isomorphisms-in-categories.md).

## Definition

```agda
anafunctor-Category :
  {l1 l2 l3 l4 : Level} (l : Level) →
  Category l1 l2 → Category l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
anafunctor-Category l C D =
  anafunctor-Precategory l (precategory-Category C) (precategory-Category D)

module _
  {l1 l2 l3 l4 l5 : Level} (C : Category l1 l2) (D : Category l3 l4)
  (F : anafunctor-Category l5 C D)
  where

  object-anafunctor-Category : obj-Category C → obj-Category D → UU l5
  object-anafunctor-Category =
    object-anafunctor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)

  hom-anafunctor-Category :
    (X Y : obj-Category C) (U : obj-Category D)
    (u : object-anafunctor-Category X U)
    (V : obj-Category D) (v : object-anafunctor-Category Y V) →
    type-hom-Category C X Y → type-hom-Category D U V
  hom-anafunctor-Category =
    hom-anafunctor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
      ( F)
```

## Properties

### Any functor between categories induces an anafunctor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Category l1 l2) (D : Category l3 l4)
  where

  anafunctor-functor-Category :
    functor-Category C D → anafunctor-Category l4 C D
  anafunctor-functor-Category =
    anafunctor-functor-Precategory
      ( precategory-Category C)
      ( precategory-Category D)
```

### The action on objects of an anafunctor between categories

```agda
image-object-anafunctor-Category :
  {l1 l2 l3 l4 l5 : Level} (C : Category l1 l2) (D : Category l3 l4) →
  anafunctor-Category l5 C D → obj-Category C → UU (l3 ⊔ l5)
image-object-anafunctor-Category C D F X =
  Σ ( obj-Category D)
    ( λ U → type-trunc-Prop (object-anafunctor-Category C D F X U))
```
