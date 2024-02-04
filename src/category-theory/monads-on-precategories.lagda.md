# Monads on precategories

```agda
module category-theory.monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
```

</details>

## Definitions

### The type of monads on precategories

```agda
monad-Precategory :
  (l : Level) (C : Precategory l l) → UU l
monad-Precategory l C =
  Σ ( functor-Precategory C C)
    ( λ T →
      Σ ( natural-transformation-Precategory C C (id-functor-Precategory C) T)
        ( λ eta →
          Σ ( natural-transformation-Precategory
              ( C)
              ( C)
              ( comp-functor-Precategory C C C T T) T)
            ( λ mu →
              Σ ( comp-natural-transformation-Precategory
                    ( C)
                    ( C)
                    ( comp-functor-Precategory
                      ( C)
                      ( C)
                      ( C)
                      ( T)
                      ( comp-functor-Precategory C C C T T))
                    ( comp-functor-Precategory C C C T T)
                    ( T)
                    ( mu)
                    ( whiskering-functor-natural-transformation-Precategory
                      {C = C}
                      {D = C}
                      {E = C}
                      ( comp-functor-Precategory C C C T T)
                      ( T)
                      ( T)
                      ( mu))
                  ＝
                    comp-natural-transformation-Precategory
                      ( C)
                      ( C)
                      (comp-functor-Precategory
                        ( C)
                        ( C)
                        ( C)
                        ( comp-functor-Precategory C C C T T) T)
                      ( comp-functor-Precategory C C C T T)
                      ( T)
                      ( mu)
                      ( whiskering-natural-transformation-functor-Precategory
                        {C = C}
                        {D = C}
                        {E = C}
                        ( comp-functor-Precategory C C C T T)
                        ( T)
                        ( mu)
                        ( T)))
                  ( λ _ →
                    prod
                      ( comp-natural-transformation-Precategory
                          ( C)
                          ( C)
                          ( T)
                          ( comp-functor-Precategory C C C T T)
                          ( T)
                          ( mu)
                          ( whiskering-functor-natural-transformation-Precategory
                            {C = C}
                            {D = C}
                            {E = C}
                            ( id-functor-Precategory C)
                            ( T)
                            ( T)
                            ( eta))
                      ＝
                        id-natural-transformation-Precategory C C T)
                      ( comp-natural-transformation-Precategory
                          ( C)
                          ( C)
                          ( T)
                          ( comp-functor-Precategory C C C T T)
                          ( T)
                          ( mu)
                          ( whiskering-natural-transformation-functor-Precategory
                            {C = C}
                            {D = C}
                            {E = C}
                            ( id-functor-Precategory C)
                            ( T)
                            ( eta)
                            ( T))
                      ＝
                        id-natural-transformation-Precategory C C T)))))
```
