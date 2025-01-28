# Indiscrete precategories

```agda
module category-theory.indiscrete-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories
open import category-theory.pregroupoids
open import category-theory.preunivalent-categories
open import category-theory.strict-categories
open import category-theory.subterminal-precategories

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
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
every indiscrete precategory is
[subterminal](category-theory.subterminal-precategories.md).

## Definitions

### The indiscrete precategory associated to a type

#### The objects and hom-sets of the indiscrete precategory associated to a type

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

#### The precategory structure of the indiscrete precategory associated to a type

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
      ( f)
      ( id-hom-indiscrete-Precategory {x}) ＝
    f
  right-unit-law-comp-hom-indiscrete-Precategory f = refl

  indiscrete-Precategory : Precategory l lzero
  indiscrete-Precategory =
    make-Precategory
      ( obj-indiscrete-Precategory X)
      ( hom-set-indiscrete-Precategory X)
      ( λ {x} {y} {z} → comp-hom-indiscrete-Precategory {x} {y} {z})
      ( λ x → id-hom-indiscrete-Precategory {x})
      ( λ {x} {y} {z} {w} →
        associative-comp-hom-indiscrete-Precategory {x} {y} {z} {w})
      ( λ {x} {y} → left-unit-law-comp-hom-indiscrete-Precategory {x} {y})
      ( λ {x} {y} → right-unit-law-comp-hom-indiscrete-Precategory {x} {y})
```

#### The pregroupoid structure of the indiscrete precategory associated to a type

```agda
module _
  {l : Level} (X : UU l)
  where

  is-iso-hom-indiscrete-Precategory :
    {x y : obj-indiscrete-Precategory X}
    (f : hom-indiscrete-Precategory X x y) →
    is-iso-Precategory (indiscrete-Precategory X) {x} {y} f
  pr1 (is-iso-hom-indiscrete-Precategory _) = star
  pr1 (pr2 (is-iso-hom-indiscrete-Precategory _)) = refl
  pr2 (pr2 (is-iso-hom-indiscrete-Precategory _)) = refl

  iso-obj-indiscrete-Precategory :
    (x y : obj-indiscrete-Precategory X) →
    iso-Precategory (indiscrete-Precategory X) x y
  pr1 (iso-obj-indiscrete-Precategory x y) = star
  pr2 (iso-obj-indiscrete-Precategory x y) =
    is-iso-hom-indiscrete-Precategory {x} {y} star

  is-pregroupoid-indiscrete-Precategory :
    is-pregroupoid-Precategory (indiscrete-Precategory X)
  is-pregroupoid-indiscrete-Precategory x y =
    is-iso-hom-indiscrete-Precategory {x} {y}

  indiscrete-Pregroupoid : Pregroupoid l lzero
  pr1 indiscrete-Pregroupoid = indiscrete-Precategory X
  pr2 indiscrete-Pregroupoid = is-pregroupoid-indiscrete-Precategory
```

### The predicate on a precategory of being indiscrete

For completeness, we also record the predicate on a precategory of being
indiscrete.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-indiscrete-Precategory : UU (l1 ⊔ l2)
  is-indiscrete-Precategory =
    (x y : obj-Precategory C) → is-contr (hom-Precategory C x y)

  is-prop-is-indiscrete-Precategory : is-prop is-indiscrete-Precategory
  is-prop-is-indiscrete-Precategory =
    is-prop-iterated-Π 2 (λ x y → is-property-is-contr)

  is-indiscrete-prop-Precategory : Prop (l1 ⊔ l2)
  pr1 is-indiscrete-prop-Precategory = is-indiscrete-Precategory
  pr2 is-indiscrete-prop-Precategory = is-prop-is-indiscrete-Precategory
```

#### The indiscrete precategory associated to a type is indiscrete

```agda
module _
  {l : Level} (X : UU l)
  where

  is-indiscrete-indiscrete-Precategory :
    is-indiscrete-Precategory (indiscrete-Precategory X)
  is-indiscrete-indiscrete-Precategory x y = is-contr-unit
```

## Properties

### If an indiscrete precategory is preunivalent then it is a strict category

**Proof:** If an indiscrete precategory is preunivalent, that means every
identity type of the objects embeds into the unit type, hence the objects form a
set.

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
      ( preunivalence-is-preunivalent-Precategory
        ( indiscrete-Precategory X)
        ( H)
        ( x)
        ( y))
      ( is-prop-Σ
        ( is-prop-unit)
        ( is-prop-is-iso-Precategory (indiscrete-Precategory X) {x} {y}))
```

### The construction of `indiscrete-Precategory` is a section of `obj-Precategory`

```agda
is-section-indiscrete-Precategory :
  {l : Level} → obj-Precategory ∘ indiscrete-Precategory {l} ~ id
is-section-indiscrete-Precategory X = refl
```

### Indiscrete precategories are subterminal

```agda
module _
  {l : Level} (X : UU l)
  where

  is-subterminal-indiscrete-Precategory :
    is-subterminal-Precategory (indiscrete-Precategory X)
  is-subterminal-indiscrete-Precategory x y = is-equiv-id
```

## External links

- [indiscrete category](https://ncatlab.org/nlab/show/indiscrete+category) at
  $n$Lab
- [Indiscrete category](https://en.wikipedia.org/wiki/Indiscrete_category) at
  Wikipedia

A wikidata identifier was not available for this concept.
