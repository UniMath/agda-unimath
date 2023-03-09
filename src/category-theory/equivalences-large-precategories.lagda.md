# Equivalences between large precategories

```agda
module category-theory.equivalences-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import Agda.Primitive using (Setω)

open import category-theory.functors-large-precategories
open import category-theory.large-precategories
open import category-theory.natural-isomorphisms-large-precategories

open import foundation.universe-levels
```

</details>

## Idea

The large precategories `C` and `D` are equivalent if there are functors `F : C → D` and `G : D → C` such that
- `comp G F` is naturally isomorphic to the identity functor on `C`,
- `comp F G` is naturally isomorphic to the identity functor on `D`.

## Definition

```agda
module _
  {αC αD : Level → Level} {βC βD : Level → Level → Level}
  (C : Large-Precat αC βC) (D : Large-Precat αD βD)
  where

  record equivalence-Large-Precat (γ-there γ-back : Level → Level) : Setω where
    constructor make-equivalence-Large-Precat
    field
      functor-equivalence-Large-Precat : functor-Large-Precat C D γ-there
      functor-inv-equivalence-Large-Precat : functor-Large-Precat D C γ-back
      issec-functor-inv-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat
          ( comp-functor-Large-Precat
            functor-equivalence-Large-Precat
            functor-inv-equivalence-Large-Precat)
          (id-functor-Large-Precat)
      isretr-functor-inv-equivalence-Large-Precat :
        natural-isomorphism-Large-Precat
          ( comp-functor-Large-Precat
            functor-inv-equivalence-Large-Precat
            functor-equivalence-Large-Precat)
          (id-functor-Large-Precat)
```
