# Monads on precategories

```agda
module category-theory.monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation-core.cartesian-product-types
open import foundation.identity-types
```

```agda
Monad-Precategory :
  (l : Level) (C : Precategory l l) → UU l
Monad-Precategory l C =
  Σ ( functor-Precategory C C)
    ( λ T →
      Σ ( natural-transformation-Precategory C C (id-functor-Precategory C) T)
        ( λ eta →
          Σ ( natural-transformation-Precategory C C (comp-functor-Precategory C C C T T) T)
            ( λ mu →
              Σ ( comp-natural-transformation-Precategory
                    ( C)
                    ( C)
                    (comp-functor-Precategory C C C T (comp-functor-Precategory C C C T T))
                    ( comp-functor-Precategory C C C T T)
                    ( T)
                    ( mu)
                    ( horizontal-comp-natural-transformation-Precategory
                      ( C)
                      ( C)
                      ( C)
                      ( comp-functor-Precategory C C C T T)
                      ( T)
                      ( T)
                      ( T)
                      ( id-natural-transformation-Precategory C C T)
                      ( mu))
                  ＝
                    comp-natural-transformation-Precategory
                      ( C)
                      ( C)
                      (comp-functor-Precategory C C C (comp-functor-Precategory C C C T T) T)
                      ( comp-functor-Precategory C C C T T)
                      ( T)
                      ( mu)
                      ( horizontal-comp-natural-transformation-Precategory
                        ( C)
                        ( C)
                        ( C)
                        ( T)
                        ( T)
                        ( comp-functor-Precategory C C C T T)
                        ( T)
                        ( mu)
                        ( id-natural-transformation-Precategory C C T)))
                  ( λ _ →
                    prod
                      ( comp-natural-transformation-Precategory
                          ( C)
                          ( C)
                          ( T)
                          ( comp-functor-Precategory C C C T T)
                          ( T)
                          ( mu)
                          ( horizontal-comp-natural-transformation-Precategory
                            ( C)
                            ( C)
                            ( C)
                            ( id-functor-Precategory C)
                            ( T)
                            ( T)
                            ( T)
                            ( id-natural-transformation-Precategory C C T)
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
                          ( horizontal-comp-natural-transformation-Precategory
                            ( C)
                            ( C)
                            ( C)
                            ( T)
                            ( T)
                            ( id-functor-Precategory C)
                            ( T)
                            ( eta)
                            ( id-natural-transformation-Precategory C C T))
                      ＝
                        id-natural-transformation-Precategory C C T)))))
```
