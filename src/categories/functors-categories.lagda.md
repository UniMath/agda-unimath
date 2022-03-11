# Functors on categories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.functors-categories where

open import categories.categories using
  ( Cat; precat-Cat; obj-Cat; type-hom-Cat; comp-Cat; id-Cat)
open import categories.functors-precategories using
  ( functor-Precat; respects-comp-functor-Precat;
    respects-id-functor-Precat; id-functor-Precat;
    comp-functor-Precat)
open import foundation.dependent-pair-types using (pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A functor between two categories is a functor between the underlying precategories.

## Definition

```agda
module _ {l1 l2 l3 l4 : Level}
  (C : Cat l1 l2)
  (D : Cat l3 l4) where

  functor-Cat : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Cat = functor-Precat (precat-Cat C) (precat-Cat D)

  obj-functor-Cat : functor-Cat → obj-Cat C → obj-Cat D
  obj-functor-Cat = pr1

  hom-functor-Cat :
    (F : functor-Cat) →
    {x y : obj-Cat C} →
    (f : type-hom-Cat C x y) →
    type-hom-Cat D (obj-functor-Cat F x) (obj-functor-Cat F y)
  hom-functor-Cat F = pr1 (pr2 F)

  respects-comp-functor-Cat :
    (F : functor-Cat) →
    {x y z : obj-Cat C} (g : type-hom-Cat C y z) (f : type-hom-Cat C x y) →
    Id (hom-functor-Cat F (comp-Cat C g f)) (comp-Cat D (hom-functor-Cat F g) (hom-functor-Cat F f))
  respects-comp-functor-Cat F = respects-comp-functor-Precat (precat-Cat C) (precat-Cat D) F

  respects-id-functor-Cat :
    (F : functor-Cat) →
    (x : obj-Cat C) →
    Id (hom-functor-Cat F (id-Cat C {x})) (id-Cat D {obj-functor-Cat F x})
  respects-id-functor-Cat F = respects-id-functor-Precat (precat-Cat C) (precat-Cat D) F
```

## Examples

### The identity functor

There is an identity functor on any category.

```agda
id-functor-Cat : ∀ {l1 l2} (C : Cat l1 l2) → functor-Cat C C
id-functor-Cat C = id-functor-Precat (precat-Cat C)
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Cat : ∀ {l1 l2 l3 l4 l5 l6}
                 → (C : Cat l1 l2)
                 → (D : Cat l3 l4)
                 → (E : Cat l5 l6)
                 → (G : functor-Cat D E)
                 → (F : functor-Cat C D)
                 → functor-Cat C E
comp-functor-Cat C D E G F =
  comp-functor-Precat (precat-Cat C) (precat-Cat D) (precat-Cat E) G F
```
