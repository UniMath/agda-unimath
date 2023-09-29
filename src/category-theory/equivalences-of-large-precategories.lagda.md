# Equivalences between large precategories

```agda
module category-theory.equivalences-of-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-isomorphisms-functors-large-precategories

open import foundation.universe-levels
```

</details>

## Idea

The large precategories `C` and `D` are equivalent if there are functors
`F : C → D` and `G : D → C` such that

- `G ∘ F` is naturally isomorphic to the identity functor on `C`,
- `F ∘ G` is naturally isomorphic to the identity functor on `D`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precategory αC βC) (D : Large-Precategory αD βD)
  where

  record
    equivalence-Large-Precategory (γ-there γ-back : Level → Level) : UUω where
    constructor
      make-equivalence-Large-Precategory
    field
      functor-equivalence-Large-Precategory :
        functor-Large-Precategory C D γ-there
      functor-inv-equivalence-Large-Precategory :
        functor-Large-Precategory D C γ-back
      is-section-functor-inv-equivalence-Large-Precategory :
        natural-isomorphism-Large-Precategory
          ( comp-functor-Large-Precategory
            functor-equivalence-Large-Precategory
            functor-inv-equivalence-Large-Precategory)
          ( id-functor-Large-Precategory)
      is-retraction-functor-inv-equivalence-Large-Precategory :
        natural-isomorphism-Large-Precategory
          ( comp-functor-Large-Precategory
            functor-inv-equivalence-Large-Precategory
            functor-equivalence-Large-Precategory)
          ( id-functor-Large-Precategory)
```
