# Comonads on precategories

```agda
module category-theory.comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.copointed-endofunctors-precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
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

A
{{#concept "comonad" Disambiguation="on a precategory" Agda=comonad-Precategory}}
on a [precategory](category-theory.precategories.md) `C` consists of an
[endofunctor](category-theory.functors-precategories.md) `T : C → C` together
with two
[natural transformations](category-theory.natural-transformations-functors-precategories.md):
`ε : T ⇒ 1_C` and `δ : T ⇒ T²`, where `1_C : C → C` is the identity functor for
`C`, and `T²` is the functor `T ∘ T : C → C`. These must satisfy the following
{{#concept "comonad laws" Disambiguation="comonad on a precategory"}}:

- **Associativity:** `(T • δ) ∘ δ = (δ • T) ∘ δ`
- The **left counit law:** `(T • ε) ∘ δ = 1_T`
- The **right counit law:** `(ε • T) ∘ δ = 1_T`.

Here, `•` denotes
[whiskering](category-theory.natural-transformations-functors-precategories.md#whiskering),
and `1_T : T ⇒ T` denotes the identity natural transformation for `T`.

See also the dual notion of a
[monad on a precategory](category-theory.monads-on-precategories.md).

## Definitions

### Comultiplication structure on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  where

  structure-comultiplication-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-comultiplication-copointed-endofunctor-Precategory =
    natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
```

### Associativity of comultiplication on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  associative-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T)))
      ( left-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T))
        ( functor-copointed-endofunctor-Precategory C T)
        ( μ))
      ( μ) ＝
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T)))
      ( right-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T))
        ( μ)
        ( functor-copointed-endofunctor-Precategory C T))
      ( μ)

  associative-comul-hom-family-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-comul-hom-family-copointed-endofunctor-Precategory =
    ( λ x →
      ( comp-hom-Precategory C
        ( hom-functor-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( hom-family-natural-transformation-Precategory C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( comp-functor-Precategory C C C
              ( functor-copointed-endofunctor-Precategory C T)
              ( functor-copointed-endofunctor-Precategory C T))
            ( μ)
            ( x)))
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( comp-functor-Precategory C C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( functor-copointed-endofunctor-Precategory C T))
          ( μ)
          ( x)))) ~
    ( λ x →
      ( comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( comp-functor-Precategory C C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( functor-copointed-endofunctor-Precategory C T))
          ( μ)
          ( obj-functor-Precategory C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( x)))
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( comp-functor-Precategory C C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( functor-copointed-endofunctor-Precategory C T))
          ( μ)
          ( x))))
```

### The left counit law on a comultiplication on a copointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  left-counit-law-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  left-counit-law-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( functor-copointed-endofunctor-Precategory C T)
      ( left-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( id-functor-Precategory C)
        ( functor-copointed-endofunctor-Precategory C T)
        ( copointing-copointed-endofunctor-Precategory C T))
      ( μ) ＝
    id-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)

  left-counit-law-comul-hom-family-copointed-endofunctor-Precategory :
    UU (l1 ⊔ l2)
  left-counit-law-comul-hom-family-copointed-endofunctor-Precategory =
    ( λ x →
      comp-hom-Precategory C
        ( hom-functor-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( hom-family-natural-transformation-Precategory C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( id-functor-Precategory C)
            ( copointing-copointed-endofunctor-Precategory C T)
            ( x)))
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( comp-functor-Precategory C C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( functor-copointed-endofunctor-Precategory C T))
          ( μ)
          ( x))) ~
    ( λ x → id-hom-Precategory C)
```

### The right counit law on a comultiplication on a copointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  right-counit-law-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  right-counit-law-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( functor-copointed-endofunctor-Precategory C T)
      ( right-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( id-functor-Precategory C)
        ( copointing-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( μ) ＝
    id-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)

  right-counit-law-comul-hom-family-copointed-endofunctor-Precategory :
    UU (l1 ⊔ l2)
  right-counit-law-comul-hom-family-copointed-endofunctor-Precategory =
    ( λ x →
      comp-hom-Precategory C
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( id-functor-Precategory C)
          ( copointing-copointed-endofunctor-Precategory C T)
          ( obj-functor-Precategory C C
            ( functor-copointed-endofunctor-Precategory C T) x))
        ( hom-family-natural-transformation-Precategory C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( comp-functor-Precategory C C C
            ( functor-copointed-endofunctor-Precategory C T)
            ( functor-copointed-endofunctor-Precategory C T))
          ( μ)
          ( x))) ~
    ( λ x → id-hom-Precategory C)
```

### The structure of a comonad on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  where

  structure-comonad-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-comonad-copointed-endofunctor-Precategory =
    Σ ( structure-comultiplication-copointed-endofunctor-Precategory C T)
      ( λ μ →
        associative-comul-copointed-endofunctor-Precategory C T μ ×
        left-counit-law-comul-copointed-endofunctor-Precategory C T μ ×
        right-counit-law-comul-copointed-endofunctor-Precategory C T μ)
```

### The type of comonads on precategories

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  comonad-Precategory : UU (l1 ⊔ l2)
  comonad-Precategory =
    Σ ( copointed-endofunctor-Precategory C)
      ( structure-comonad-copointed-endofunctor-Precategory C)

  module _
    (T : comonad-Precategory)
    where

    copointed-endofunctor-comonad-Precategory :
      copointed-endofunctor-Precategory C
    copointed-endofunctor-comonad-Precategory = pr1 T

    endofunctor-comonad-Precategory :
      functor-Precategory C C
    endofunctor-comonad-Precategory =
      functor-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    obj-endofunctor-comonad-Precategory :
      obj-Precategory C → obj-Precategory C
    obj-endofunctor-comonad-Precategory =
      obj-functor-Precategory C C endofunctor-comonad-Precategory

    hom-endofunctor-comonad-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      hom-Precategory C
        ( obj-endofunctor-comonad-Precategory X)
        ( obj-endofunctor-comonad-Precategory Y)
    hom-endofunctor-comonad-Precategory =
      hom-functor-Precategory C C endofunctor-comonad-Precategory

    preserves-id-endofunctor-comonad-Precategory :
      (X : obj-Precategory C) →
      hom-endofunctor-comonad-Precategory (id-hom-Precategory C {X}) ＝
      id-hom-Precategory C
    preserves-id-endofunctor-comonad-Precategory =
      preserves-id-functor-Precategory C C endofunctor-comonad-Precategory

    preserves-comp-endofunctor-comonad-Precategory :
      {X Y Z : obj-Precategory C} →
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      hom-endofunctor-comonad-Precategory (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( hom-endofunctor-comonad-Precategory g)
        ( hom-endofunctor-comonad-Precategory f)
    preserves-comp-endofunctor-comonad-Precategory =
      preserves-comp-functor-Precategory C C
        ( endofunctor-comonad-Precategory)

    counit-comonad-Precategory :
      copointing-endofunctor-Precategory C endofunctor-comonad-Precategory
    counit-comonad-Precategory =
      copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    hom-counit-comonad-Precategory :
      hom-family-functor-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( id-functor-Precategory C)
    hom-counit-comonad-Precategory =
      hom-family-copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    naturality-counit-comonad-Precategory :
      is-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( id-functor-Precategory C)
        ( hom-counit-comonad-Precategory)
    naturality-counit-comonad-Precategory =
      naturality-copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    comul-comonad-Precategory :
      structure-comultiplication-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
    comul-comonad-Precategory = pr1 (pr2 T)

    hom-comul-comonad-Precategory :
      hom-family-functor-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
    hom-comul-comonad-Precategory =
      hom-family-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( comul-comonad-Precategory)

    naturality-comul-comonad-Precategory :
      is-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( hom-comul-comonad-Precategory)
    naturality-comul-comonad-Precategory =
      naturality-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( comul-comonad-Precategory)

    associative-comul-comonad-Precategory :
      associative-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    associative-comul-comonad-Precategory =
      pr1 (pr2 (pr2 T))

    associative-comul-hom-family-comonad-Precategory :
      associative-comul-hom-family-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    associative-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( comp-functor-Precategory C C C
            ( endofunctor-comonad-Precategory)
            ( endofunctor-comonad-Precategory)))
        ( associative-comul-comonad-Precategory)

    left-counit-law-comul-comonad-Precategory :
      left-counit-law-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    left-counit-law-comul-comonad-Precategory =
      pr1 (pr2 (pr2 (pr2 T)))

    left-counit-law-comul-hom-family-comonad-Precategory :
      left-counit-law-comul-hom-family-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    left-counit-law-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( endofunctor-comonad-Precategory)
        ( left-counit-law-comul-comonad-Precategory)

    right-counit-law-comul-comonad-Precategory :
      right-counit-law-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    right-counit-law-comul-comonad-Precategory =
      pr2 (pr2 (pr2 (pr2 T)))

    right-counit-law-comul-hom-family-comonad-Precategory :
      right-counit-law-comul-hom-family-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( comul-comonad-Precategory)
    right-counit-law-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( endofunctor-comonad-Precategory)
        ( right-counit-law-comul-comonad-Precategory)
```

## See also

- [Monads](category-theory.monads-on-precategories.md) for the dual concept.
