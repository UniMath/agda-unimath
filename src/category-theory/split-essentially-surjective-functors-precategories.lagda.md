# Split essentially surjective functors between precategories

```agda
module category-theory.split-essentially-surjective-functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.essential-fibers-of-functors-precategories
open import category-theory.essentially-surjective-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

A [functor](category-theory.functors-precategories.md) `F : C → D` between
[precategories](category-theory.precategories.md) is **split essentially
surjective** if there is a section of the
[essential fiber](category-theory.essential-fibers-of-functors-precategories.md)
over every object of `D`.

## Definitions

### The type of proofs that a functor is split essentially surjective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-split-essentially-surjective-functor-Precategory : UU (l1 ⊔ l3 ⊔ l4)
  is-split-essentially-surjective-functor-Precategory =
    (y : obj-Precategory D) → essential-fiber-functor-Precategory C D F y

  obj-is-split-essentially-surjective-functor-Precategory :
    is-split-essentially-surjective-functor-Precategory →
    obj-Precategory D → obj-Precategory C
  obj-is-split-essentially-surjective-functor-Precategory
    is-split-ess-surj-F y =
    pr1 (is-split-ess-surj-F y)

  iso-is-split-essentially-surjective-functor-Precategory :
    ( is-split-ess-surj-F :
        is-split-essentially-surjective-functor-Precategory) →
    (y : obj-Precategory D) →
    iso-Precategory D
      ( obj-functor-Precategory C D F
        ( obj-is-split-essentially-surjective-functor-Precategory
          ( is-split-ess-surj-F)
          ( y)))
      ( y)
  iso-is-split-essentially-surjective-functor-Precategory
    is-split-ess-surj-F y =
    pr2 (is-split-ess-surj-F y)
```

We also record a variant with the opposite variance:

```agda
  is-split-essentially-surjective-functor-Precategory' : UU (l1 ⊔ l3 ⊔ l4)
  is-split-essentially-surjective-functor-Precategory' =
    (y : obj-Precategory D) → essential-fiber-functor-Precategory' C D F y

  obj-is-split-essentially-surjective-functor-Precategory' :
    is-split-essentially-surjective-functor-Precategory' →
    obj-Precategory D → obj-Precategory C
  obj-is-split-essentially-surjective-functor-Precategory'
    is-split-ess-surj-F' y =
    pr1 (is-split-ess-surj-F' y)

  iso-is-split-essentially-surjective-functor-Precategory' :
    ( is-split-ess-surj-F' :
        is-split-essentially-surjective-functor-Precategory') →
    (y : obj-Precategory D) →
    iso-Precategory D
      ( y)
      ( obj-functor-Precategory C D F
        ( obj-is-split-essentially-surjective-functor-Precategory'
          ( is-split-ess-surj-F')
          ( y)))
  iso-is-split-essentially-surjective-functor-Precategory'
    is-split-ess-surj-F' y =
    pr2 (is-split-ess-surj-F' y)
```

### The type of split essentially surjective functors

```agda
split-essentially-surjective-functor-Precategory :
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
split-essentially-surjective-functor-Precategory C D =
  Σ ( functor-Precategory C D)
    ( is-split-essentially-surjective-functor-Precategory C D)

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : split-essentially-surjective-functor-Precategory C D)
  where

  functor-split-essentially-surjective-functor-Precategory :
    functor-Precategory C D
  functor-split-essentially-surjective-functor-Precategory = pr1 F

  is-split-essentially-surjective-split-essentially-surjective-functor-Precategory :
    is-split-essentially-surjective-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)
  is-split-essentially-surjective-split-essentially-surjective-functor-Precategory =
    pr2 F

  obj-split-essentially-surjective-functor-Precategory :
    obj-Precategory C → obj-Precategory D
  obj-split-essentially-surjective-functor-Precategory =
    obj-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)

  hom-split-essentially-surjective-functor-Precategory :
    {x y : obj-Precategory C} →
    hom-Precategory C x y →
    hom-Precategory D
      ( obj-split-essentially-surjective-functor-Precategory x)
      ( obj-split-essentially-surjective-functor-Precategory y)
  hom-split-essentially-surjective-functor-Precategory =
    hom-functor-Precategory C D
      ( functor-split-essentially-surjective-functor-Precategory)
```

## Properties

### Split essentially surjective functors are essentially surjective

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  where

  is-essentially-surjective-is-split-essentially-surjective-functor-Precategory :
    (F : functor-Precategory C D) →
    is-split-essentially-surjective-functor-Precategory C D F →
    is-essentially-surjective-functor-Precategory C D F
  is-essentially-surjective-is-split-essentially-surjective-functor-Precategory
    F is-split-ess-surj-F =
    unit-trunc-Prop ∘ is-split-ess-surj-F

  essentially-surjective-functor-split-essentially-surjective-functor-Precategory :
    split-essentially-surjective-functor-Precategory C D →
    essentially-surjective-functor-Precategory C D
  essentially-surjective-functor-split-essentially-surjective-functor-Precategory =
    tot
      ( is-essentially-surjective-is-split-essentially-surjective-functor-Precategory)
```

### Being split essentially surjective is a property of fully faithful functors when the codomain is a category

This remains to be shown. This is Lemma 6.8 of _Univalent Categories and the
Rezk completion_.

## References

{{#bibliography}} {{#reference AKS15}}

## External links

- [Essential Fibres](https://1lab.dev/Cat.Functor.Properties.html#essential-fibres)
  at 1lab
- [split essentially surjective functor](https://ncatlab.org/nlab/show/split+essentially+surjective+functor)
  at $n$Lab

A wikidata identifier was not available for this concept.
