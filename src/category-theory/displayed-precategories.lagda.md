# Displayed precategories

```agda
module category-theory.displayed-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.nonunital-precategories
open import category-theory.precategories
open import category-theory.dependent-composition-operations-over-precategories
open import category-theory.set-magmoids

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.iterated-dependent-product-types
open import foundation.identity-types
open import foundation.dependent-identifications
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Idea

Given a [precategory](category-theory.precategories.md) `C`, a **displayed
precategory** over `C` is an associative and unital
[dependent composition structure](category-theory.dependent-composition-operations-over-precategories.md)
over it.

Thus, a displayed precategory `D` over `C` consists of

- a family of objects `ob D` indexed by `ob C`,
- a family of hom-[sets](foundation-core.sets.md)

  ```text
  hom D : hom C x y → ob D x → ob D y → Set,
  ```

  for every pair `x y : ob C`, and

- a dependent composition operation

  ```text
    comp D : hom D g y' z' → hom D f x' y' → hom D (g ∘ f) x' z'
  ```

  such that

- The dependent associativity condition

  ```text
  comp D (comp D h' g') f' ＝ comp D h' (comp D g' f')
  ```

  over the associativity witness `(h ∘ g) ∘ f ＝ h ∘ (g ∘ f)` in `C` holds, and

- the composition operation is dependent unital, meaning there is a family of
  identity morphisms

  ```text
    id D : (x : ob C) (x' : ob D x) → hom D (id C x) x' x'
  ```

  which is a dependent left and right unit in the sense that the dependent
  identities `comp D (id D) f ＝ f` and `comp D f (id D) ＝ f` hold over the
  respective witnesses of left and right unitality in `C`.

## Definitions

### The predicate of being a displayed precategory

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  ( obj-D : obj-Precategory C → UU l3)
  ( hom-set-D :
    {x y : obj-Precategory C}
    (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
  ( comp-hom-D : dependent-composition-operation-Precategory C obj-D hom-set-D)
  where

  is-displayed-precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-displayed-precategory =
    ( is-associative-dependent-composition-operation-Precategory C
        obj-D hom-set-D comp-hom-D) ×
    ( is-unital-dependent-composition-operation-Precategory C
        obj-D hom-set-D comp-hom-D)
```

### The type of displayed precategories over a precategory

```agda
module _
  {l1 l2 : Level} (l3 l4 : Level) (C : Precategory l1 l2)
  where

  Displayed-Precategory : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Displayed-Precategory =
    Σ ( obj-Precategory C → UU l3)
      ( λ obj-D →
        Σ ( {x y : obj-Precategory C}
            (f : hom-Precategory C x y) (x' : obj-D x) (y' : obj-D y) → Set l4)
          ( λ hom-set-D →
            Σ ( dependent-composition-operation-Precategory C obj-D hom-set-D)
              ( is-displayed-precategory C obj-D hom-set-D)))

module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Displayed-Precategory l3 l4 C)
  where

  obj-Displayed-Precategory : obj-Precategory C → UU l3
  obj-Displayed-Precategory = pr1 D

  hom-set-Displayed-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    Set l4
  hom-set-Displayed-Precategory = pr1 (pr2 D)

  hom-Displayed-Precategory :
    {x y : obj-Precategory C} (f : hom-Precategory C x y)
    (x' : obj-Displayed-Precategory x) (y' : obj-Displayed-Precategory y) →
    UU l4
  hom-Displayed-Precategory f x' y' =
    type-Set (hom-set-Displayed-Precategory f x' y')

  comp-hom-Displayed-Precategory :
    dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
  comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 D))

  associative-comp-hom-Displayed-Precategory :
    is-associative-dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  associative-comp-hom-Displayed-Precategory = pr1 (pr2 (pr2 (pr2 D)))

  is-unital-comp-hom-Displayed-Precategory :
    is-unital-dependent-composition-operation-Precategory C
      ( obj-Displayed-Precategory)
      ( hom-set-Displayed-Precategory)
      ( comp-hom-Displayed-Precategory)
  is-unital-comp-hom-Displayed-Precategory = pr2 (pr2 (pr2 (pr2 D)))

  id-hom-Displayed-Precategory :
    {x : obj-Precategory C} (x' : obj-Displayed-Precategory x) →
    hom-Displayed-Precategory (id-hom-Precategory C) x' x'
  id-hom-Displayed-Precategory = pr1 is-unital-comp-hom-Displayed-Precategory

  left-unit-law-comp-hom-Displayed-Precategory :
    is-left-unit-dependent-composition-operation-Precategory C
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  left-unit-law-comp-hom-Displayed-Precategory =
    pr1 (pr2 is-unital-comp-hom-Displayed-Precategory)

  right-unit-law-comp-hom-Displayed-Precategory :
    is-right-unit-dependent-composition-operation-Precategory C
      obj-Displayed-Precategory
      hom-set-Displayed-Precategory
      comp-hom-Displayed-Precategory
      id-hom-Displayed-Precategory
  right-unit-law-comp-hom-Displayed-Precategory =
    pr2 (pr2 is-unital-comp-hom-Displayed-Precategory)
```

## References

1. Benedikt Ahrens and Peter LeFanu Lumsdaine, _Displayed Categories_ (2019)
   ([arXiv:1705.04296](https://arxiv.org/abs/1705.04296))

## External links

- [Displayed Categories](https://1lab.dev/Cat.Displayed.Base.html) at 1lab
- [displayed category](https://ncatlab.org/nlab/show/displayed+category) at
  $n$Lab
- [Displayed categories](https://www.epatters.org/wiki/algebra/displayed-categories)
  at Evan Patterson's blog

A wikidata identifier was not available for this concept.
