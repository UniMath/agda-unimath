# Discrete categories

```agda
module category-theory.discrete-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

### Discrete precategories

Any set induces a discrete category whose objects are elements of the set and
which contains no-nonidentity morphisms.

```agda
module _
  {l : Level} (X : Set l)
  where

  discrete-precategory-Set : Precategory l l
  pr1 discrete-precategory-Set = type-Set X
  pr1 (pr2 discrete-precategory-Set) x y =
    set-Prop (x ＝ y , is-set-type-Set X x y)
  pr1 (pr1 (pr2 (pr2 discrete-precategory-Set))) = concat' _
  pr2 (pr1 (pr2 (pr2 discrete-precategory-Set))) refl refl refl = refl
  pr1 (pr2 (pr2 (pr2 discrete-precategory-Set))) x = refl
  pr1 (pr2 (pr2 (pr2 (pr2 discrete-precategory-Set)))) _ = right-unit
  pr2 (pr2 (pr2 (pr2 (pr2 discrete-precategory-Set)))) _ = left-unit
```
