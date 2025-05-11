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
    (λ x →
      (comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (comp-functor-Precategory C C C
            (functor-pointed-endofunctor-Precategory C T)
            (functor-pointed-endofunctor-Precategory C T))
          (functor-pointed-endofunctor-Precategory C T)
          μ
          x)
        (hom-functor-Precategory C C
          (functor-pointed-endofunctor-Precategory C T)
          (hom-family-natural-transformation-Precategory C C
            (comp-functor-Precategory C C C
              (functor-pointed-endofunctor-Precategory C T)
              (functor-pointed-endofunctor-Precategory C T))
            (functor-pointed-endofunctor-Precategory C T)
            μ
            x)))) ~
    (λ x →
      (comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (comp-functor-Precategory C C C
            (functor-pointed-endofunctor-Precategory C T)
            (functor-pointed-endofunctor-Precategory C T))
          (functor-pointed-endofunctor-Precategory C T)
          μ
          x)
        (hom-family-natural-transformation-Precategory C C
          (comp-functor-Precategory C C C
            (functor-pointed-endofunctor-Precategory C T)
            (functor-pointed-endofunctor-Precategory C T))
          (functor-pointed-endofunctor-Precategory C T)
          μ
          (obj-functor-Precategory C C
            (functor-pointed-endofunctor-Precategory C T)
            x))))
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
    (λ x →
      comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (comp-functor-Precategory C C C
            (functor-pointed-endofunctor-Precategory C T)
            (functor-pointed-endofunctor-Precategory C T))
          (functor-pointed-endofunctor-Precategory C T)
          μ
          x)
        (hom-functor-Precategory C C
          (functor-pointed-endofunctor-Precategory C T)
          (hom-family-natural-transformation-Precategory C C
            (id-functor-Precategory C)
            (functor-pointed-endofunctor-Precategory C T)
            (pointing-pointed-endofunctor-Precategory C T)
            x))) ~
    (λ x → id-hom-Precategory C)
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
    (λ x →
      comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (comp-functor-Precategory C C C
            (functor-pointed-endofunctor-Precategory C T)
            (functor-pointed-endofunctor-Precategory C T))
          (functor-pointed-endofunctor-Precategory C T)
          μ
          x)
        (hom-family-natural-transformation-Precategory C C
          (id-functor-Precategory C)
          (functor-pointed-endofunctor-Precategory C T)
          (pointing-pointed-endofunctor-Precategory C T)
          (obj-functor-Precategory C C
            (functor-pointed-endofunctor-Precategory C T) x))) ~
    (λ x → id-hom-Precategory C)
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
        (pointed-endofunctor-monad-Precategory)
        (mul-monad-Precategory)
    associative-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        (comp-functor-Precategory C C C
          endofunctor-monad-Precategory
          (comp-functor-Precategory C C C
            endofunctor-monad-Precategory
            endofunctor-monad-Precategory))
        endofunctor-monad-Precategory
        associative-mul-monad-Precategory

    left-unit-law-mul-monad-Precategory :
      left-unit-law-mul-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    left-unit-law-mul-monad-Precategory =
      pr1 (pr2 (pr2 (pr2 T)))

    left-unit-law-mul-hom-family-monad-Precategory :
      left-unit-law-mul-hom-family-pointed-endofunctor-Precategory C
        (pointed-endofunctor-monad-Precategory)
        (mul-monad-Precategory)
    left-unit-law-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        endofunctor-monad-Precategory endofunctor-monad-Precategory
        left-unit-law-mul-monad-Precategory

    right-unit-law-mul-monad-Precategory :
      right-unit-law-mul-pointed-endofunctor-Precategory C
        ( pointed-endofunctor-monad-Precategory)
        ( mul-monad-Precategory)
    right-unit-law-mul-monad-Precategory =
      pr2 (pr2 (pr2 (pr2 T)))

    right-unit-law-mul-hom-family-monad-Precategory :
      right-unit-law-mul-hom-family-pointed-endofunctor-Precategory C
        (pointed-endofunctor-monad-Precategory)
        (mul-monad-Precategory)
    right-unit-law-mul-hom-family-monad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        endofunctor-monad-Precategory endofunctor-monad-Precategory
        right-unit-law-mul-monad-Precategory
```

## Algebras over a monad

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  module _
    {A : obj-Precategory C}
    (a : hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
    where

    has-unit-law-monad-algebra-Precategory : UU l2
    has-unit-law-monad-algebra-Precategory =
        comp-hom-Precategory C a (hom-unit-monad-Precategory C T A) ＝
        id-hom-Precategory C

    has-mul-law-monad-algebra-Precategory : UU l2
    has-mul-law-monad-algebra-Precategory =
        comp-hom-Precategory C a (hom-endofunctor-monad-Precategory C T a) ＝
        comp-hom-Precategory C a (hom-mul-monad-Precategory C T A)

    is-monad-algebra-Precategory : UU l2
    is-monad-algebra-Precategory =
        has-unit-law-monad-algebra-Precategory ×
        has-mul-law-monad-algebra-Precategory

  monad-algebra-Precategory : UU (l1 ⊔ l2)
  monad-algebra-Precategory =
    Σ (obj-Precategory C)
      (λ A →
      Σ (hom-Precategory C (obj-endofunctor-monad-Precategory C T A) A)
        (λ a -> is-monad-algebra-Precategory a))

  obj-monad-algebra-Precategory : monad-algebra-Precategory → obj-Precategory C
  obj-monad-algebra-Precategory = pr1

  hom-monad-algebra-Precategory : (f : monad-algebra-Precategory) →
    hom-Precategory C
      (obj-endofunctor-monad-Precategory C T (obj-monad-algebra-Precategory f))
      (obj-monad-algebra-Precategory f)
  hom-monad-algebra-Precategory f = pr1 (pr2 f)

  comm-monad-algebra-Precategory : (f : monad-algebra-Precategory) →
    is-monad-algebra-Precategory (hom-monad-algebra-Precategory f)
  comm-monad-algebra-Precategory f = pr2 (pr2 f)

  unit-law-monad-algebra-Precategory : (f : monad-algebra-Precategory) →
    has-unit-law-monad-algebra-Precategory (hom-monad-algebra-Precategory f)
  unit-law-monad-algebra-Precategory f = pr1 (pr2 (pr2 f))

  mul-law-monad-algebra-Precategory : (f : monad-algebra-Precategory) →
    has-mul-law-monad-algebra-Precategory (hom-monad-algebra-Precategory f)
  mul-law-monad-algebra-Precategory f = pr2 (pr2 (pr2 f))

  monad-algebra-morphism-Precategory : (f g : monad-algebra-Precategory) → UU l2
  monad-algebra-morphism-Precategory f g =
    Σ (hom-Precategory C
        (obj-monad-algebra-Precategory f)
        (obj-monad-algebra-Precategory g))
      (λ h →
        coherence-square-hom-Precategory C
          (hom-endofunctor-monad-Precategory C T h)
          (hom-monad-algebra-Precategory f)
          (hom-monad-algebra-Precategory g)
          h)

  hom-monad-algebra-morphism-Precategory :
    (f g : monad-algebra-Precategory)
    (h : monad-algebra-morphism-Precategory f g) →
    hom-Precategory C
      (obj-monad-algebra-Precategory f)
      (obj-monad-algebra-Precategory g)
  hom-monad-algebra-morphism-Precategory f g h = pr1 h

  top-hom-monad-algebra-morphism-Precategory :
    (f g : monad-algebra-Precategory)
    (h : monad-algebra-morphism-Precategory f g) →
    hom-Precategory C
      (obj-endofunctor-monad-Precategory C T (obj-monad-algebra-Precategory f))
      (obj-endofunctor-monad-Precategory C T (obj-monad-algebra-Precategory g))
  top-hom-monad-algebra-morphism-Precategory f g h =
    hom-endofunctor-monad-Precategory C T
      (hom-monad-algebra-morphism-Precategory f g h)

  comm-hom-monad-algebra-morphism-Precategory :
    (f g : monad-algebra-Precategory)
    (h : monad-algebra-morphism-Precategory f g) →
    coherence-square-hom-Precategory C
      (top-hom-monad-algebra-morphism-Precategory f g h)
      (hom-monad-algebra-Precategory f)
      (hom-monad-algebra-Precategory g)
      (hom-monad-algebra-morphism-Precategory f g h)
  comm-hom-monad-algebra-morphism-Precategory f g h = pr2 h

  comp-monad-algebra-morphism-Precategory :
    (a b c : monad-algebra-Precategory)
    (g : monad-algebra-morphism-Precategory b c) →
    (f : monad-algebra-morphism-Precategory a b) →
    monad-algebra-morphism-Precategory a c
  comp-monad-algebra-morphism-Precategory a b c g f =
    (comp-hom-Precategory C
      (hom-monad-algebra-morphism-Precategory b c g)
      (hom-monad-algebra-morphism-Precategory a b f)) ,
    (comp-coherence-square-hom-Precategory C
      (top-hom-monad-algebra-morphism-Precategory a b f)
      (hom-monad-algebra-Precategory a)
      (hom-monad-algebra-Precategory b)
      (hom-monad-algebra-morphism-Precategory a b f)
      (top-hom-monad-algebra-morphism-Precategory b c g)
      (hom-monad-algebra-Precategory c)
      (hom-monad-algebra-morphism-Precategory b c g)
      (comm-hom-monad-algebra-morphism-Precategory a b f)
      (comm-hom-monad-algebra-morphism-Precategory b c g)) ∙
    (ap
      (postcomp-hom-Precategory C (hom-monad-algebra-Precategory c) _)
      (inv (preserves-comp-endofunctor-monad-Precategory C T _ _)))

  is-set-monad-algebra-morphism-Precategory :
    (f g : monad-algebra-Precategory) →
    is-set (monad-algebra-morphism-Precategory f g)
  is-set-monad-algebra-morphism-Precategory f g =
    is-set-Σ
      (is-set-hom-Precategory C _ _)
      (λ hk → is-set-is-prop (is-set-hom-Precategory C _ _ _ _))
```

## The Kleisli precategory of a monad

This is the precategory of free `T`-algebras and their morphisms; we view it as
the precategory with the same objects as `C` but different types of morphisms.
It comes with functors to and from `C`.

```agda
module _
  {l1 l2 : Level} {C : Precategory l1 l2}
  (T : monad-Precategory C)
  where

  private
    Tf = endofunctor-monad-Precategory C T
    μ = hom-mul-monad-Precategory C T
    η = hom-unit-monad-Precategory C T
    T₀ = obj-endofunctor-monad-Precategory C T
    T₁ = hom-endofunctor-monad-Precategory C T

  kleisli-monad-Precategory : Precategory l1 l2
  kleisli-monad-Precategory =
    make-Precategory
      (obj-Precategory C)
      (λ x y → hom-set-Precategory C x (T₀ y))
      (λ g f → comp-hom-Precategory C (comp-hom-Precategory C (μ _) (T₁ g)) f)
      (λ x → hom-unit-monad-Precategory C T x)
      (λ h g f →
        (ap
          (precomp-hom-Precategory C f _)
          ( (ap
              (postcomp-hom-Precategory C (μ _) _)
              ( (preserves-comp-endofunctor-monad-Precategory C T _ g) ∙
                (ap
                  (precomp-hom-Precategory C (T₁ g) _)
                  (preserves-comp-endofunctor-monad-Precategory C T _ _)) ∙
                (associative-comp-hom-Precategory C _ _ _))) ∙
            (inv (associative-comp-hom-Precategory C _ _ _)) ∙
            (ap
              (precomp-hom-Precategory C _ _)
              (associative-mul-hom-family-monad-Precategory C T _)) ∙
            (associative-comp-hom-Precategory C _ _ _) ∙
            (ap
              (postcomp-hom-Precategory C (μ _) _)
              ( (inv (associative-comp-hom-Precategory C _ _ _)) ∙
                (ap
                  (precomp-hom-Precategory C (T₁ g) _)
                  (inv (naturality-mul-monad-Precategory C T h))) ∙
                (associative-comp-hom-Precategory C _ _ _))) ∙
            (inv (associative-comp-hom-Precategory C _ _ _))) ∙
        (associative-comp-hom-Precategory C _ _ _)))
      (λ f →
        (ap
          (precomp-hom-Precategory C _ _)
          (left-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
        (left-unit-law-comp-hom-Precategory C f))
      (λ f →
        (associative-comp-hom-Precategory C _ _ _) ∙
        (ap
          (postcomp-hom-Precategory C _ _)
          (naturality-unit-monad-Precategory C T f)) ∙
        (inv (associative-comp-hom-Precategory C _ _ _)) ∙
        (ap
          (precomp-hom-Precategory C f _)
          (right-unit-law-mul-hom-family-monad-Precategory C T _)) ∙
        (left-unit-law-comp-hom-Precategory C f))

  functor-to-kleisli-monad-Precategory :
    functor-Precategory C kleisli-monad-Precategory
  functor-to-kleisli-monad-Precategory =
    id ,
    (λ {x} {y} f →
      comp-hom-Precategory C (T₁ f) (hom-unit-monad-Precategory C T x)) ,
    (λ {x} {y} {z} g f →
      (ap
        (precomp-hom-Precategory C (η x) _)
        ( (preserves-comp-endofunctor-monad-Precategory C T g f) ∙
          (ap
            (precomp-hom-Precategory C (T₁ f) _)
            ( (inv (left-unit-law-comp-hom-Precategory C _)) ∙
              (ap
                (precomp-hom-Precategory C (T₁ g) _)
                (inv (left-unit-law-mul-hom-family-monad-Precategory C T z))) ∙
              (associative-comp-hom-Precategory C _ _ _) ∙
              (ap
                (postcomp-hom-Precategory C (μ z) _)
                ( (inv
                    (preserves-comp-endofunctor-monad-Precategory C T
                      (η z) g)) ∙
                  (ap
                    T₁
                    (inv (naturality-unit-monad-Precategory C T g))))))))) ∙
      (associative-comp-hom-Precategory C _ _ _)) ,
    (λ x →
      (ap
        (precomp-hom-Precategory C _ _)
        (preserves-id-endofunctor-monad-Precategory C T x)) ∙
      (left-unit-law-comp-hom-Precategory C _))

  functor-from-kleisli-monad-Precategory :
    functor-Precategory kleisli-monad-Precategory C
  functor-from-kleisli-monad-Precategory =
    T₀ ,
    (λ {x} {y} f →
      comp-hom-Precategory C (hom-mul-monad-Precategory C T y) (T₁ f)) ,
    (λ {x} {y} {z} g f →
      (ap
        (postcomp-hom-Precategory C (μ z) _)
        ( (preserves-comp-endofunctor-monad-Precategory C T _ f) ∙
          (ap
            (precomp-hom-Precategory C (T₁ f) _)
            (preserves-comp-endofunctor-monad-Precategory C T (μ z) (T₁ g))) ∙
          (associative-comp-hom-Precategory C _ _ _))) ∙
      (inv (associative-comp-hom-Precategory C _ _ _)) ∙
      (ap
        (precomp-hom-Precategory C _ _)
        (associative-mul-hom-family-monad-Precategory C T z)) ∙
      (associative-comp-hom-Precategory C _ _ _) ∙
      (ap
        (postcomp-hom-Precategory C (μ z) _)
        ( (inv (associative-comp-hom-Precategory C _ _ _)) ∙
          (ap
            (precomp-hom-Precategory C (T₁ f) _)
            (inv (naturality-mul-monad-Precategory C T g))) ∙
          (associative-comp-hom-Precategory C _ _ _))) ∙
      (inv (associative-comp-hom-Precategory C _ _ _))) ,
    (left-unit-law-mul-hom-family-monad-Precategory C T)
```

## The Eilenberg-Moore precategory of a monad

The Eilenberg-Moore category `EM(T)` consists of all `T`-algebras and
`T`-algebra morphisms. It comes with an adjunction `C : ⇄ EM(T)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : monad-Precategory C)
  where

  private
    Tf = endofunctor-monad-Precategory C T
    T₁ = hom-endofunctor-monad-Precategory C T
    T₀ = obj-endofunctor-monad-Precategory C T

  em-monad-Precategory : Precategory (l1 ⊔ l2) l2
  em-monad-Precategory = make-Precategory
    (monad-algebra-Precategory C T)
    (λ f g →
      (monad-algebra-morphism-Precategory C T f g) ,
      (is-set-monad-algebra-morphism-Precategory C T f g))
    (λ {a} {b} {c} g f → comp-monad-algebra-morphism-Precategory C T a b c g f)
    (λ x →
      (id-hom-Precategory C) ,
      (left-unit-law-comp-hom-Precategory C
        (hom-monad-algebra-Precategory C T x)) ∙
      (inv
        (right-unit-law-comp-hom-Precategory C
          (hom-monad-algebra-Precategory C T x))) ∙
      (ap
        (postcomp-hom-Precategory C _ _)
        (inv (preserves-id-endofunctor-monad-Precategory C T _))))
    (λ h g f →
      eq-pair-Σ
        (associative-comp-hom-Precategory C _ _ _)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))
    (λ {a} {b} f →
      eq-pair-Σ
        (left-unit-law-comp-hom-Precategory C
          (hom-monad-algebra-morphism-Precategory C T a b f))
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))
    λ {a} {b} f →
      eq-pair-Σ
        (right-unit-law-comp-hom-Precategory C
          (hom-monad-algebra-morphism-Precategory C T a b f))
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  obj-functor-to-em-monad-Precategory :
    obj-Precategory C → obj-Precategory em-monad-Precategory
  obj-functor-to-em-monad-Precategory x =
    (obj-endofunctor-monad-Precategory C T x) ,
    ((hom-mul-monad-Precategory C T x) ,
      right-unit-law-mul-hom-family-monad-Precategory C T x ,
      associative-mul-hom-family-monad-Precategory C T x)

  hom-functor-to-em-monad-Precategory : {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-Precategory em-monad-Precategory
      (obj-functor-to-em-monad-Precategory x)
      (obj-functor-to-em-monad-Precategory y)
  hom-functor-to-em-monad-Precategory f =
    (T₁ f) , naturality-mul-monad-Precategory C T f

  functor-to-em-monad-Precategory : functor-Precategory C em-monad-Precategory
  functor-to-em-monad-Precategory =
    obj-functor-to-em-monad-Precategory ,
    hom-functor-to-em-monad-Precategory ,
    (λ g f →
      eq-pair-Σ
        (preserves-comp-endofunctor-monad-Precategory C T g f)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _))) ,
    (λ x →
      eq-pair-Σ
        (preserves-id-endofunctor-monad-Precategory C T x)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  functor-from-em-monad-Precategory : functor-Precategory em-monad-Precategory C
  functor-from-em-monad-Precategory =
    (obj-monad-algebra-Precategory C T) ,
    (λ {x} {y} f → hom-monad-algebra-morphism-Precategory C T x y f) ,
    (λ g f → refl) ,
    (λ x → refl)

  -- The unit x → Tx is exactly the unit of the monad
  unit-em-monad-Precategory :
    natural-transformation-Precategory C C
      (id-functor-Precategory C)
      (comp-functor-Precategory C em-monad-Precategory C
        functor-from-em-monad-Precategory
        functor-to-em-monad-Precategory)
  unit-em-monad-Precategory = unit-monad-Precategory C T

  -- The counit is the vertical map given by the structure map of the algebra
  --       μ
  --   T²x → Tx
  -- Ta ↓    ↓ a
  --   Tx  → x
  --       a
  counit-em-monad-Precategory :
    natural-transformation-Precategory em-monad-Precategory em-monad-Precategory
      (comp-functor-Precategory em-monad-Precategory C em-monad-Precategory
        functor-to-em-monad-Precategory functor-from-em-monad-Precategory)
      (id-functor-Precategory em-monad-Precategory)
  counit-em-monad-Precategory =
    (λ x →
      (hom-monad-algebra-Precategory C T x) ,
      inv (mul-law-monad-algebra-Precategory C T x)) ,
    (λ {x} {y} f → eq-pair-Σ
      (comm-hom-monad-algebra-morphism-Precategory C T x y f)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  private
    LR =
      comp-functor-Precategory em-monad-Precategory C em-monad-Precategory
        functor-to-em-monad-Precategory functor-from-em-monad-Precategory
    RL =
      comp-functor-Precategory C em-monad-Precategory C
        functor-from-em-monad-Precategory functor-to-em-monad-Precategory

  left-triangle-em-monad-Precategory :
    has-left-triangle-identity-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      unit-em-monad-Precategory
      counit-em-monad-Precategory
  left-triangle-em-monad-Precategory x =
    eq-pair-Σ
      (left-unit-law-mul-hom-family-monad-Precategory C T x)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  right-triangle-em-monad-Precategory :
    has-right-triangle-identity-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      unit-em-monad-Precategory
      counit-em-monad-Precategory
  right-triangle-em-monad-Precategory x =
    unit-law-monad-algebra-Precategory C T x

  adjunction-em-monad-Precategory :
    Adjunction-Precategory C em-monad-Precategory
  adjunction-em-monad-Precategory =
    make-Adjunction-Precategory C em-monad-Precategory
      functor-to-em-monad-Precategory
      functor-from-em-monad-Precategory
      (is-adjoint-pair-unit-counit-Precategory C em-monad-Precategory
        functor-to-em-monad-Precategory
        functor-from-em-monad-Precategory
        unit-em-monad-Precategory
        counit-em-monad-Precategory
        left-triangle-em-monad-Precategory
        right-triangle-em-monad-Precategory)
```
