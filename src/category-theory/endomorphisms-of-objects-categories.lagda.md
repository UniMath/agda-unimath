# Endomorphisms of objects in categories

```agda
module category-theory.endomorphisms-of-objects-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.categories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids
open import group-theory.semigroups
```

</details>

## Definition

### The monoid of endomorphisms on an object in a category

```agda
module _
  {l1 l2 : Level} (C : Cat l1 l2) (X : obj-Cat C)
  where

  endo-Cat : UU l2
  endo-Cat = type-hom-Cat C X X

  comp-endo-Cat : endo-Cat → endo-Cat → endo-Cat
  comp-endo-Cat g f = comp-hom-Cat C g f

  id-endo-Cat : endo-Cat
  id-endo-Cat = id-hom-Cat C

  assoc-comp-endo-Cat :
    (h g f : endo-Cat) →
    (comp-endo-Cat (comp-endo-Cat h g) f) ＝ comp-endo-Cat h (comp-endo-Cat g f)
  assoc-comp-endo-Cat = assoc-comp-hom-Cat C

  left-unit-law-comp-endo-Cat :
    (f : endo-Cat) → comp-endo-Cat id-endo-Cat f ＝ f
  left-unit-law-comp-endo-Cat = left-unit-law-comp-hom-Cat C

  right-unit-law-comp-endo-Cat :
    (f : endo-Cat) → comp-endo-Cat f id-endo-Cat ＝ f
  right-unit-law-comp-endo-Cat = right-unit-law-comp-hom-Cat C

  set-endo-Cat : Set l2
  set-endo-Cat = hom-Cat C X X

  semigroup-endo-Cat : Semigroup l2
  pr1 semigroup-endo-Cat = set-endo-Cat
  pr1 (pr2 semigroup-endo-Cat) = comp-endo-Cat
  pr2 (pr2 semigroup-endo-Cat) = assoc-comp-endo-Cat

  monoid-endo-Cat : Monoid l2
  pr1 monoid-endo-Cat = semigroup-endo-Cat
  pr1 (pr2 monoid-endo-Cat) = id-endo-Cat
  pr1 (pr2 (pr2 monoid-endo-Cat)) = left-unit-law-comp-endo-Cat
  pr2 (pr2 (pr2 monoid-endo-Cat)) = right-unit-law-comp-endo-Cat
```
