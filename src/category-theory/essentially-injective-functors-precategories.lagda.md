# Essentially injective functors between precategories

```agda
open import foundation.function-extensionality-axiom

module
  category-theory.essentially-injective-functors-precategories
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories funext
open import category-theory.isomorphisms-in-precategories funext
open import category-theory.precategories funext

open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) is **essentially injective**
if every pair of objects that are mapped to
[isomorphic](category-theory.isomorphisms-in-precategories.md) objects in `D`
are isomorphic in `C`.

## Definitions

### The type of proofs of being essentially injective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-essentially-injective-functor-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-essentially-injective-functor-Precategory =
    (x y : obj-Precategory C) →
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y) →
    iso-Precategory C x y
```

### The type of essentially injective functors

```agda
essentially-injective-functor-Precategory :
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
essentially-injective-functor-Precategory C D =
  Σ ( functor-Precategory C D)
    ( is-essentially-injective-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : essentially-injective-functor-Precategory C D)
  where

  functor-essentially-injective-functor-Precategory :
    functor-Precategory C D
  functor-essentially-injective-functor-Precategory = pr1 F

  is-essentially-injective-essentially-injective-functor-Precategory :
    is-essentially-injective-functor-Precategory C D
      ( functor-essentially-injective-functor-Precategory)
  is-essentially-injective-essentially-injective-functor-Precategory = pr2 F

  obj-essentially-injective-functor-Precategory :
    obj-Precategory C → obj-Precategory D
  obj-essentially-injective-functor-Precategory =
    obj-functor-Precategory C D
      ( functor-essentially-injective-functor-Precategory)

  hom-essentially-injective-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-essentially-injective-functor-Precategory x)
      ( obj-essentially-injective-functor-Precategory y)
  hom-essentially-injective-functor-Precategory =
    hom-functor-Precategory C D
      ( functor-essentially-injective-functor-Precategory)
```

## See also

- [Injective maps](foundation-core.injective-maps.md)

## External links

- [essentially injective functor](https://ncatlab.org/nlab/show/essentially+injective+functor)
  at $n$Lab
