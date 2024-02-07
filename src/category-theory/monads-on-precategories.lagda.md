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

## Idea

A monad on a precategory `C` consists of an
endo[functor](category-theory.functors-precategories.md) `T : C → C` together
with two
[natural transformations](category-theory.natural-transformations-functors-precategories.md):
`η : 1_C ⇒ T` and `μ : T² ⇒ T` (where `1_C : C → C` is the identity functor for
`C`, and `T²` is the functor `T ∘ T : C → C`).

These must fulfill the _coherence conditions_:

- `μ ∘ (T • μ) = μ ∘ (μ • T)`, and
- `μ ∘ (T • η) = μ ∘ (η • T) = 1_T`.

Here, `•` denotes
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering),
and `1_T : T ⇒ T` denotes the identity natural transformation for `T`.

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
                    product
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
