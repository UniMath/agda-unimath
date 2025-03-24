# Endomorphisms in precategories

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module category-theory.endomorphisms-in-precategories
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.monoids funext univalence truncations
open import group-theory.semigroups funext univalence
```

</details>

## Definition

### The monoid of endomorphisms on an object in a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2) (X : obj-Precategory C)
  where

  type-endo-Precategory : UU l2
  type-endo-Precategory = hom-Precategory C X X

  comp-endo-Precategory :
    type-endo-Precategory → type-endo-Precategory → type-endo-Precategory
  comp-endo-Precategory g f = comp-hom-Precategory C g f

  id-endo-Precategory : type-endo-Precategory
  id-endo-Precategory = id-hom-Precategory C

  associative-comp-endo-Precategory :
    (h g f : type-endo-Precategory) →
    ( comp-endo-Precategory (comp-endo-Precategory h g) f) ＝
    ( comp-endo-Precategory h (comp-endo-Precategory g f))
  associative-comp-endo-Precategory = associative-comp-hom-Precategory C

  left-unit-law-comp-endo-Precategory :
    (f : type-endo-Precategory) →
    comp-endo-Precategory id-endo-Precategory f ＝ f
  left-unit-law-comp-endo-Precategory = left-unit-law-comp-hom-Precategory C

  right-unit-law-comp-endo-Precategory :
    (f : type-endo-Precategory) →
    comp-endo-Precategory f id-endo-Precategory ＝ f
  right-unit-law-comp-endo-Precategory = right-unit-law-comp-hom-Precategory C

  set-endo-Precategory : Set l2
  set-endo-Precategory = hom-set-Precategory C X X

  semigroup-endo-Precategory : Semigroup l2
  pr1 semigroup-endo-Precategory = set-endo-Precategory
  pr1 (pr2 semigroup-endo-Precategory) = comp-endo-Precategory
  pr2 (pr2 semigroup-endo-Precategory) = associative-comp-endo-Precategory

  monoid-endo-Precategory : Monoid l2
  pr1 monoid-endo-Precategory = semigroup-endo-Precategory
  pr1 (pr2 monoid-endo-Precategory) = id-endo-Precategory
  pr1 (pr2 (pr2 monoid-endo-Precategory)) = left-unit-law-comp-endo-Precategory
  pr2 (pr2 (pr2 monoid-endo-Precategory)) = right-unit-law-comp-endo-Precategory
```
