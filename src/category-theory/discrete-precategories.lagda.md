# The discrete precategory introduced by any hSet

```agda
module category-theory.discrete-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

### Discrete precategories

Any set induces a discrete category whose objects are elements of the set and which contains
no-nonidentity morphisms.

```agda

module _
  {l : Level} (X : Set l)
  where

  Discrete-Precat : Precat _ _
  Discrete-Precat = type-Set X , disc-Hom , comp-struct , id-struct
    where
      disc-Hom : type-Set X → type-Set X → Set l
      disc-Hom x y = set-Prop (x ＝ y , is-set-type-Set X x y )

      comp-struct : associative-composition-structure-Set disc-Hom
      pr1 comp-struct refl refl = refl
      pr2 comp-struct refl refl refl = refl

      id-struct : is-unital-composition-structure-Set disc-Hom comp-struct
      pr1 id-struct x = refl
      pr1 (pr2 id-struct) refl = refl
      pr2 (pr2 id-struct) refl = refl

```
