# Indiscrete precategories

```agda
module category-theory.indiscrete-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.fully-faithful-functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.preunivalent-categories
open import category-theory.strict-categories
open import category-theory.terminal-category

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

Given a type `X`, we can define its associated **indiscrete precategory** as the
[precategory](category-theory.precategories.md) whose
hom-[sets](foundation-core.sets.md) are
[contractible](foundation-core.contractible-types.md) everywhere.

This construction demonstrates one essential aspect about precategories: While
it displays `obj-Precategory` as a [retraction](foundation-core.retractions.md),
up to weak categorical equivalence, every indiscrete precategory is subterminal.

## Definition

### The objects and hom-sets of an indiscrete category

```agda
module _
  {l : Level} (X : UU l)
  where

  obj-indiscrete-Precategory : UU l
  obj-indiscrete-Precategory = X

  hom-set-indiscrete-Precategory :
    obj-indiscrete-Precategory → obj-indiscrete-Precategory → Set lzero
  hom-set-indiscrete-Precategory _ _ = unit-Set

  hom-indiscrete-Precategory :
    obj-indiscrete-Precategory → obj-indiscrete-Precategory → UU lzero
  hom-indiscrete-Precategory x y = type-Set (hom-set-indiscrete-Precategory x y)
```

### The precategory structure of an indiscrete precategory

```agda
module _
  {l : Level} (X : UU l)
  where

  comp-hom-indiscrete-Precategory :
    {x y z : obj-indiscrete-Precategory X} →
    hom-indiscrete-Precategory X y z →
    hom-indiscrete-Precategory X x y →
    hom-indiscrete-Precategory X x z
  comp-hom-indiscrete-Precategory _ _ = star

  associative-comp-hom-indiscrete-Precategory :
    {x y z w : obj-indiscrete-Precategory X} →
    (h : hom-indiscrete-Precategory X z w)
    (g : hom-indiscrete-Precategory X y z)
    (f : hom-indiscrete-Precategory X x y) →
    comp-hom-indiscrete-Precategory {x} {y} {w}
      ( comp-hom-indiscrete-Precategory {y} {z} {w} h g)
      ( f) ＝
    comp-hom-indiscrete-Precategory {x} {z} {w}
      ( h)
      ( comp-hom-indiscrete-Precategory {x} {y} {z} g f)
  associative-comp-hom-indiscrete-Precategory h g f = refl

  associative-composition-operation-indiscrete-Precategory :
    associative-composition-operation-binary-family-Set
      ( hom-set-indiscrete-Precategory X)
  pr1 associative-composition-operation-indiscrete-Precategory {x} {y} {z} =
    comp-hom-indiscrete-Precategory {x} {y} {z}
  pr2 associative-composition-operation-indiscrete-Precategory {x} {y} {z} {w} =
    associative-comp-hom-indiscrete-Precategory {x} {y} {z} {w}

  id-hom-indiscrete-Precategory :
    {x : obj-indiscrete-Precategory X} → hom-indiscrete-Precategory X x x
  id-hom-indiscrete-Precategory = star

  left-unit-law-comp-hom-indiscrete-Precategory :
    {x y : obj-indiscrete-Precategory X} →
    (f : hom-indiscrete-Precategory X x y) →
    comp-hom-indiscrete-Precategory {x} {y} {y}
      ( id-hom-indiscrete-Precategory {y})
      ( f) ＝
    f
  left-unit-law-comp-hom-indiscrete-Precategory f = refl

  right-unit-law-comp-hom-indiscrete-Precategory :
    {x y : obj-indiscrete-Precategory X} →
    (f : hom-indiscrete-Precategory X x y) →
    comp-hom-indiscrete-Precategory {x} {x} {y}
      ( f) (id-hom-indiscrete-Precategory {x}) ＝
    f
  right-unit-law-comp-hom-indiscrete-Precategory f = refl

  is-unital-composition-operation-indiscrete-Precategory :
    is-unital-composition-operation-binary-family-Set
      ( hom-set-indiscrete-Precategory X)
      ( λ {x} {y} {z} → comp-hom-indiscrete-Precategory {x} {y} {z})
  pr1 is-unital-composition-operation-indiscrete-Precategory x =
    id-hom-indiscrete-Precategory {x}
  pr1 (pr2 is-unital-composition-operation-indiscrete-Precategory) {x} {y} =
    left-unit-law-comp-hom-indiscrete-Precategory {x} {y}
  pr2 (pr2 is-unital-composition-operation-indiscrete-Precategory) {x} {y} =
    right-unit-law-comp-hom-indiscrete-Precategory {x} {y}

  indiscrete-Precategory : Precategory l lzero
  pr1 indiscrete-Precategory = obj-indiscrete-Precategory X
  pr1 (pr2 indiscrete-Precategory) = hom-set-indiscrete-Precategory X
  pr1 (pr2 (pr2 indiscrete-Precategory)) =
    associative-composition-operation-indiscrete-Precategory
  pr2 (pr2 (pr2 indiscrete-Precategory)) =
    is-unital-composition-operation-indiscrete-Precategory
```

## Properties

### If the indiscrete precategory is preunivalent then it is a strict category

```agda
module _
  {l : Level} (X : UU l)
  where

  is-strict-category-is-preunivalent-indiscrete-Precategory :
    is-preunivalent-Precategory (indiscrete-Precategory X) →
    is-strict-category-Precategory (indiscrete-Precategory X)
  is-strict-category-is-preunivalent-indiscrete-Precategory H x y =
    is-prop-is-emb
      ( iso-eq-Precategory (indiscrete-Precategory X) x y)
      ( H x y)
      ( is-prop-Σ
        ( is-prop-unit)
        ( is-prop-is-iso-Precategory (indiscrete-Precategory X) {x} {y}))
```

### The construction `indiscrete-Precategory` is a section

```agda
is-section-indiscrete-Precategory :
  {l : Level} → obj-Precategory ∘ indiscrete-Precategory {l} ~ id
is-section-indiscrete-Precategory X = refl
```

### The terminal projection functor is fully faithful

```agda
module _
  {l : Level} (X : UU l)
  where

  is-fully-faithful-terminal-functor-indiscrete-Precategory :
    is-fully-faithful-functor-Precategory
      ( indiscrete-Precategory X)
      ( terminal-Precategory)
      (terminal-functor-Precategory (indiscrete-Precategory X))
  is-fully-faithful-terminal-functor-indiscrete-Precategory x y = is-equiv-id
```

## External links

- [indiscrete category](https://ncatlab.org/nlab/show/indiscrete+category) at
  nlab
- [Indiscrete category](https://en.wikipedia.org/wiki/Indiscrete_category) at
  Wikipedia

A wikidata identifier was not available for this concept.
