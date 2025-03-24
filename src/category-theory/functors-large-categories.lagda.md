# Functors between large categories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.functors-large-categories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories funext univalence truncations
open import category-theory.large-categories funext univalence truncations

open import foundation.identity-types funext
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [large category](category-theory.large-categories.md) `C`
to a large category `D` is a
[functor](category-theory.functors-large-precategories.md) between the
underlying [large precategories](category-theory.large-precategories.md) of `C`
and `D`. In other words, functors of large categories consist of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F id_x = id_(F x)`,
- `F (g ∘ f) = F g ∘ F f`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} (γ : Level → Level)
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  where

  functor-Large-Category : UUω
  functor-Large-Category =
    functor-Large-Precategory γ
      ( large-precategory-Large-Category C)
      ( large-precategory-Large-Category D)

module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level} {γ : Level → Level}
  (C : Large-Category αC βC) (D : Large-Category αD βD)
  (F : functor-Large-Category γ C D)
  where

  obj-functor-Large-Category :
    {l1 : Level} → obj-Large-Category C l1 → obj-Large-Category D (γ l1)
  obj-functor-Large-Category =
    obj-functor-Large-Precategory F

  hom-functor-Large-Category :
    {l1 l2 : Level}
    {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2} →
    hom-Large-Category C X Y →
    hom-Large-Category D
      ( obj-functor-Large-Category X)
      ( obj-functor-Large-Category Y)
  hom-functor-Large-Category =
    hom-functor-Large-Precategory F

  preserves-id-functor-Large-Category :
    {l1 : Level} {X : obj-Large-Category C l1} →
    hom-functor-Large-Category (id-hom-Large-Category C {X = X}) ＝
    id-hom-Large-Category D
  preserves-id-functor-Large-Category =
    preserves-id-functor-Large-Precategory F

  preserves-comp-functor-Large-Category :
    {l1 l2 l3 : Level}
    {X : obj-Large-Category C l1} {Y : obj-Large-Category C l2}
    {Z : obj-Large-Category C l3}
    (g : hom-Large-Category C Y Z) (f : hom-Large-Category C X Y) →
    hom-functor-Large-Category (comp-hom-Large-Category C g f) ＝
    comp-hom-Large-Category D
      ( hom-functor-Large-Category g)
      ( hom-functor-Large-Category f)
  preserves-comp-functor-Large-Category =
    preserves-comp-functor-Large-Precategory F
```

### The identity functor

There is an identity functor on any large category.

```agda
id-functor-Large-Category :
  {αC : Level → Level} {βC : Level → Level → Level} →
  (C : Large-Category αC βC) →
  functor-Large-Category (λ l → l) C C
id-functor-Large-Category C =
  id-functor-Large-Precategory (large-precategory-Large-Category C)
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
comp-functor-Large-Category :
  {αC αD αE γG γF : Level → Level}
  {βC βD βE : Level → Level → Level} →
  (C : Large-Category αC βC)
  (D : Large-Category αD βD)
  (E : Large-Category αE βE) →
  functor-Large-Category γG D E →
  functor-Large-Category γF C D →
  functor-Large-Category (λ l → γG (γF l)) C E
comp-functor-Large-Category C D E =
  comp-functor-Large-Precategory
    ( large-precategory-Large-Category C)
    ( large-precategory-Large-Category D)
    ( large-precategory-Large-Category E)
```
