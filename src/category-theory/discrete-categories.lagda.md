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
  discrete-precategory-Set =
    type-Set X , disc-Hom , composition-structure , id-structure
      where
      disc-Hom : type-Set X → type-Set X → Set l
      disc-Hom x y = set-Prop (x ＝ y , is-set-type-Set X x y)

      composition-structure : associative-composition-structure-Set disc-Hom
      pr1 composition-structure refl refl = refl
      pr2 composition-structure refl refl refl = refl

      id-structure :
        is-unital-composition-structure-Set disc-Hom composition-structure
      pr1 id-structure x = refl
      pr1 (pr2 id-structure) refl = refl
      pr2 (pr2 id-structure) refl = refl
```
