# Monads on precategories

```agda
module category-theory.monads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.pointed-endofunctors-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

A {{#concept "monad" Disambiguation="on a precategory" Agda=monad-Precategory}}
on a [precategory](category-theory.precategories.md) `C` consists of an
[endofunctor](category-theory.functors-precategories.md) `T : C → C` together
with two
[natural transformations](category-theory.natural-transformations-functors-precategories.md):
`η : 1_C ⇒ T` and `μ : T² ⇒ T`, where `1_C : C → C` is the identity functor for
`C`, and `T²` is the functor `T ∘ T : C → C`. These must satisfy the following
{{#concept "monad laws" Disambiguation="monad on a precategory"}}:

- **Associativity:** `μ ∘ (T • μ) = μ ∘ (μ • T)`
- The **left unit law:** `μ ∘ (T • η) = 1_T`
- The **right unit law:** `μ ∘ (η • T) = 1_T`.

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

  associative-mul-hom-family-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-mul-hom-family-pointed-endofunctor-Precategory =
    ( λ x →
      ( comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( comp-functor-Precategory C C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( x))
        ( hom-functor-Precategory C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( hom-family-natural-transformation-Precategory C C
            ( comp-functor-Precategory C C C
              ( functor-pointed-endofunctor-Precategory C T)
              ( functor-pointed-endofunctor-Precategory C T))
            ( functor-pointed-endofunctor-Precategory C T)
            ( μ)
            ( x))))) ~
    ( λ x →
      ( comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( comp-functor-Precategory C C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( x))
        ( hom-family-natural-transformation-Precategory C C
          ( comp-functor-Precategory C C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( obj-functor-Precategory C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( x)))))
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

  left-unit-law-mul-hom-family-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  left-unit-law-mul-hom-family-pointed-endofunctor-Precategory =
    ( λ x →
      comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( comp-functor-Precategory C C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( x))
        ( hom-functor-Precategory C C
          ( functor-pointed-endofunctor-Precategory C T)
          ( hom-family-natural-transformation-Precategory C C
            ( id-functor-Precategory C)
            ( functor-pointed-endofunctor-Precategory C T)
            ( pointing-pointed-endofunctor-Precategory C T)
            ( x)))) ~
    ( λ x → id-hom-Precategory C)
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

  right-unit-law-mul-hom-family-pointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  right-unit-law-mul-hom-family-pointed-endofunctor-Precategory =
    ( λ x →
      comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( comp-functor-Precategory C C C
            ( functor-pointed-endofunctor-Precategory C T)
            ( functor-pointed-endofunctor-Precategory C T))
          ( functor-pointed-endofunctor-Precategory C T)
          ( μ)
          ( x))
        ( hom-family-natural-transformation-Precategory C C
          ( id-functor-Precategory C)
          ( functor-pointed-endofunctor-Precategory C T)
          ( pointing-pointed-endofunctor-Precategory C T)
          ( obj-functor-Precategory C C
            ( functor-pointed-endofunctor-Precategory C T) x))) ~
    ( λ x → id-hom-Precategory C)
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

  module _
    (T : monad-Precategory)
    where

    pointed-endofunctor-monad-Precategory :
      pointed-endofunctor-Precategory C
    pointed-endofunctor-monad-Precategory = pr1 T

    endofunctor-monad-Precategory :
      functor-Precategory C C
    endofunctor-monad-Precategory =
      functor-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)

    obj-endofunctor-monad-Precategory :
      obj-Precategory C → obj-Precategory C
    obj-endofunctor-monad-Precategory =
      obj-functor-Precategory C C endofunctor-monad-Precategory

    hom-endofunctor-monad-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      hom-Precategory C
        ( obj-endofunctor-monad-Precategory X)
        ( obj-endofunctor-monad-Precategory Y)
    hom-endofunctor-monad-Precategory =
      hom-functor-Precategory C C endofunctor-monad-Precategory

    preserves-id-endofunctor-monad-Precategory :
      (X : obj-Precategory C) →
      hom-endofunctor-monad-Precategory (id-hom-Precategory C {X}) ＝
      id-hom-Precategory C
    preserves-id-endofunctor-monad-Precategory =
      preserves-id-functor-Precategory C C endofunctor-monad-Precategory

    preserves-comp-endofunctor-monad-Precategory :
      {X Y Z : obj-Precategory C} →
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      hom-endofunctor-monad-Precategory (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( hom-endofunctor-monad-Precategory g)
        ( hom-endofunctor-monad-Precategory f)
    preserves-comp-endofunctor-monad-Precategory =
      preserves-comp-functor-Precategory C C
        ( endofunctor-monad-Precategory)

    unit-monad-Precategory :
      pointing-endofunctor-Precategory C endofunctor-monad-Precategory
    unit-monad-Precategory =
      pointing-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)

    hom-unit-monad-Precategory :
      hom-family-functor-Precategory C C
        ( id-functor-Precategory C)
        ( endofunctor-monad-Precategory)
    hom-unit-monad-Precategory =
      hom-family-pointing-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)

    naturality-unit-monad-Precategory :
      is-natural-transformation-Precategory C C
        ( id-functor-Precategory C)
        ( endofunctor-monad-Precategory)
        ( hom-unit-monad-Precategory)
    naturality-unit-monad-Precategory =
      naturality-pointing-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)

    mul-monad-Precategory :
      structure-multiplication-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
    mul-monad-Precategory = pr1 (pr2 T)

    hom-mul-monad-Precategory :
      hom-family-functor-Precategory C C
        ( comp-functor-Precategory C C C
          ( endofunctor-monad-Precategory)
          ( endofunctor-monad-Precategory))
        ( endofunctor-monad-Precategory)
    hom-mul-monad-Precategory =
      hom-family-natural-transformation-Precategory C C
        ( comp-functor-Precategory C C C
          ( endofunctor-monad-Precategory)
          ( endofunctor-monad-Precategory))
        ( endofunctor-monad-Precategory)
        ( mul-monad-Precategory)

    naturality-mul-monad-Precategory :
      is-natural-transformation-Precategory C C
        ( comp-functor-Precategory C C C
          ( endofunctor-monad-Precategory)
          ( endofunctor-monad-Precategory))
        ( endofunctor-monad-Precategory)
        ( hom-mul-monad-Precategory)
    naturality-mul-monad-Precategory =
      naturality-natural-transformation-Precategory C C
        ( comp-functor-Precategory C C C
          ( endofunctor-monad-Precategory)
          ( endofunctor-monad-Precategory))
        ( endofunctor-monad-Precategory)
        ( mul-monad-Precategory)

    associative-mul-monad-Precategory :
      associative-mul-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    associative-mul-monad-Precategory =
      pr1 (pr2 (pr2 T))

    associative-mul-hom-family-monad-Precategory :
      associative-mul-hom-family-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    associative-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( comp-functor-Precategory C C C
          ( endofunctor-monad-Precategory)
          ( comp-functor-Precategory C C C
            ( endofunctor-monad-Precategory)
            ( endofunctor-monad-Precategory)))
        ( endofunctor-monad-Precategory)
        ( associative-mul-monad-Precategory)

    left-unit-law-mul-monad-Precategory :
      left-unit-law-mul-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    left-unit-law-mul-monad-Precategory =
      pr1 (pr2 (pr2 (pr2 T)))

    left-unit-law-mul-hom-family-monad-Precategory :
      left-unit-law-mul-hom-family-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    left-unit-law-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( endofunctor-monad-Precategory)
        ( endofunctor-monad-Precategory)
        ( left-unit-law-mul-monad-Precategory)

    right-unit-law-mul-monad-Precategory :
      right-unit-law-mul-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    right-unit-law-mul-monad-Precategory =
      pr2 (pr2 (pr2 (pr2 T)))

    right-unit-law-mul-hom-family-monad-Precategory :
      right-unit-law-mul-hom-family-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    right-unit-law-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( endofunctor-monad-Precategory)
        ( endofunctor-monad-Precategory)
        ( right-unit-law-mul-monad-Precategory)
```

## See also

- [Comonads](category-theory.comonads-on-precategories.md) for the dual concept.
