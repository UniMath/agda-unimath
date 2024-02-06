# Monads on precategories

```agda
module category-theory.monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.pointed-endofunctors-precategories
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

### Multiplication structure on a pointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : pointed-endofunctor-Precategory C)
  where

  structure-multiplication-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-multiplication-pointed-endofunctor-Precategory =
    natural-transformation-Precategory C C
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T))
      ( functor-pointed-endofunctor-Precategory C T)
```

### Associativity of multiplication on a pointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : pointed-endofunctor-Precategory C)
  (μ : structure-multiplication-pointed-endofunctor-Precategory C T)
  where

  associative-mul-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-mul-pointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( functor-pointed-endofunctor-Precategory C T)))
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T))
      ( functor-pointed-endofunctor-Precategory C T)
      ( μ)
      ( left-whisker-natural-transformation-Precategory C C C
        ( comp-functor-Precategory C C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( functor-pointed-endofunctor-Precategory C T))
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T)
        ( μ)) ＝
    comp-natural-transformation-Precategory C C
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( functor-pointed-endofunctor-Precategory C T)))
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T))
      ( functor-pointed-endofunctor-Precategory C T)
      ( μ)
      ( right-whisker-natural-transformation-Precategory C C C
        ( comp-functor-Precategory C C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( functor-pointed-endofunctor-Precategory C T))
```

### The left unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : pointed-endofunctor-Precategory C)
  (μ : structure-multiplication-pointed-endofunctor-Precategory C T)
  where

  left-unit-law-mul-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  left-unit-law-mul-pointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-pointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T))
      ( functor-pointed-endofunctor-Precategory C T)
      ( μ)
      ( left-whisker-natural-transformation-Precategory C C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T)
        ( pointing-pointed-endofunctor-Precategory C T)) ＝
    id-natural-transformation-Precategory C C
      ( functor-pointed-endofunctor-Precategory C T)
```

### The right unit law on a multiplication on a pointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : pointed-endofunctor-Precategory C)
  (μ : structure-multiplication-pointed-endofunctor-Precategory C T)
  where

  right-unit-law-mul-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  right-unit-law-mul-pointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-pointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T))
      ( functor-pointed-endofunctor-Precategory C T)
      ( μ)
      ( right-whisker-natural-transformation-Precategory C C C
        ( id-functor-Precategory C)
        ( functor-pointed-endofunctor-Precategory C T)
        ( pointing-pointed-endofunctor-Precategory C T)
        ( functor-pointed-endofunctor-Precategory C T)) ＝
    id-natural-transformation-Precategory C C
      ( functor-pointed-endofunctor-Precategory C T)
```

### The structure of a monad on a pointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : pointed-endofunctor-Precategory C)
  where

  structure-monad-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-monad-pointed-endofunctor-Precategory =
    Σ ( structure-multiplication-pointed-endofunctor-Precategory C T)
      ( λ μ →
        associative-mul-pointed-endofunctor-Precategory C T μ ×
        left-unit-law-mul-pointed-endofunctor-Precategory C T μ ×
        right-unit-law-mul-pointed-endofunctor-Precategory C T μ)
```

### The type of monads on precategories

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  monad-Precategory : UU (l1 ⊔ l2)
  monad-Precategory =
    Σ ( pointed-endofunctor-Precategory C)
      ( structure-monad-pointed-endofunctor-Precategory C)
```
