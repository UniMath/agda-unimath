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

  compose-endo-Cat : endo-Cat → endo-Cat → endo-Cat
  compose-endo-Cat g f = compose-hom-Cat C g f

  id-endo-Cat : endo-Cat
  id-endo-Cat = id-hom-Cat C

  associative-compose-endo-Cat :
    (h g f : endo-Cat) →
    ( compose-endo-Cat (compose-endo-Cat h g) f) ＝
    ( compose-endo-Cat h (compose-endo-Cat g f))
  associative-compose-endo-Cat = associative-compose-hom-Cat C

  left-unit-law-compose-endo-Cat :
    (f : endo-Cat) → compose-endo-Cat id-endo-Cat f ＝ f
  left-unit-law-compose-endo-Cat = left-unit-law-compose-hom-Cat C

  right-unit-law-compose-endo-Cat :
    (f : endo-Cat) → compose-endo-Cat f id-endo-Cat ＝ f
  right-unit-law-compose-endo-Cat = right-unit-law-compose-hom-Cat C

  set-endo-Cat : Set l2
  set-endo-Cat = hom-Cat C X X

  semigroup-endo-Cat : Semigroup l2
  pr1 semigroup-endo-Cat = set-endo-Cat
  pr1 (pr2 semigroup-endo-Cat) = compose-endo-Cat
  pr2 (pr2 semigroup-endo-Cat) = associative-compose-endo-Cat

  monoid-endo-Cat : Monoid l2
  pr1 monoid-endo-Cat = semigroup-endo-Cat
  pr1 (pr2 monoid-endo-Cat) = id-endo-Cat
  pr1 (pr2 (pr2 monoid-endo-Cat)) = left-unit-law-compose-endo-Cat
  pr2 (pr2 (pr2 monoid-endo-Cat)) = right-unit-law-compose-endo-Cat
```
