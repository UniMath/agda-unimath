# Isometries between pseudometric spaces

```agda
module metric-spaces.isometries-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.retractions
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
```

</details>

## Idea

A [map](metric-spaces.maps-pseudometric-spaces.md) between
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) is an
{{#concept "isometry" Disambiguation="between pseudometric spaces" Agda=is-isometry-Pseudometric-Space}}
if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is equivalent to the
[preimage](metric-spaces.preimages-rational-neighborhood-relations.md) under `f`
of the rational neighborhood relation on `B`. I.e., upper bounds on the distance
between two points in `A` are exactly the upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a isometry between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  where

  is-isometry-prop-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-isometry-prop-Pseudometric-Space =
    Eq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Pseudometric-Space B))

  is-isometry-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-isometry-Pseudometric-Space =
    type-Prop is-isometry-prop-Pseudometric-Space

  is-prop-is-isometry-Pseudometric-Space :
    is-prop is-isometry-Pseudometric-Space
  is-prop-is-isometry-Pseudometric-Space =
    is-prop-type-Prop is-isometry-prop-Pseudometric-Space
```

### The type of isometries between metric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  isometry-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  isometry-Pseudometric-Space =
    type-subtype
      ( is-isometry-prop-Pseudometric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  map-isometry-Pseudometric-Space : map-Pseudometric-Space A B
  map-isometry-Pseudometric-Space = pr1 f

  is-isometry-map-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space A B map-isometry-Pseudometric-Space
  is-isometry-map-isometry-Pseudometric-Space = pr2 f
```

## Properties

### The identity map on a pseudometric space is an isometry

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-isometry-id-Pseudometric-Space :
    is-isometry-Pseudometric-Space A A (id-map-Pseudometric-Space A)
  is-isometry-id-Pseudometric-Space d x y = id-iff

  id-isometry-Pseudometric-Space : isometry-Pseudometric-Space A A
  id-isometry-Pseudometric-Space =
    ( id-map-Pseudometric-Space A , is-isometry-id-Pseudometric-Space)
```

### Equality of isometries in pseudometric spaces is equivalent to homotopies between their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f g : isometry-Pseudometric-Space A B)
  where

  htpy-map-isometry-Pseudometric-Space : UU (l1 ⊔ l1')
  htpy-map-isometry-Pseudometric-Space =
    map-isometry-Pseudometric-Space A B f ~
    map-isometry-Pseudometric-Space A B g

  equiv-eq-htpy-map-isometry-Pseudometric-Space :
    (f ＝ g) ≃ htpy-map-isometry-Pseudometric-Space
  equiv-eq-htpy-map-isometry-Pseudometric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-isometry-prop-Pseudometric-Space A B)
      ( f)
      ( g)

  htpy-eq-map-isometry-Pseudometric-Space :
    (f ＝ g) → htpy-map-isometry-Pseudometric-Space
  htpy-eq-map-isometry-Pseudometric-Space =
    map-equiv equiv-eq-htpy-map-isometry-Pseudometric-Space

  eq-htpy-map-isometry-Pseudometric-Space :
    htpy-map-isometry-Pseudometric-Space → (f ＝ g)
  eq-htpy-map-isometry-Pseudometric-Space =
    map-inv-equiv equiv-eq-htpy-map-isometry-Pseudometric-Space
```

### An isometry preserves and reflects neighborhoods

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  preserves-neighborhoods-map-isometry-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space A) →
    neighborhood-Pseudometric-Space A d x y →
    neighborhood-Pseudometric-Space
      ( B)
      ( d)
      ( map-isometry-Pseudometric-Space A B f x)
      ( map-isometry-Pseudometric-Space A B f y)
  preserves-neighborhoods-map-isometry-Pseudometric-Space d x y =
    forward-implication
      ( is-isometry-map-isometry-Pseudometric-Space A B f d x y)

  reflects-neighborhoods-map-isometry-Pseudometric-Space :
    (d : ℚ⁺) (x y : type-Pseudometric-Space A) →
    neighborhood-Pseudometric-Space
      ( B)
      ( d)
      ( map-isometry-Pseudometric-Space A B f x)
      ( map-isometry-Pseudometric-Space A B f y) →
    neighborhood-Pseudometric-Space A d x y
  reflects-neighborhoods-map-isometry-Pseudometric-Space d x y =
    backward-implication
      ( is-isometry-map-isometry-Pseudometric-Space A B f d x y)
```

### Composition of isometries

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  where

  is-isometry-comp-Pseudometric-Space :
    (g : map-Pseudometric-Space B C) →
    (f : map-Pseudometric-Space A B) →
    is-isometry-Pseudometric-Space B C g →
    is-isometry-Pseudometric-Space A B f →
    is-isometry-Pseudometric-Space A C (g ∘ f)
  is-isometry-comp-Pseudometric-Space g f H K d x y =
    H d (f x) (f y) ∘iff K d x y

  comp-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space B C →
    isometry-Pseudometric-Space A B →
    isometry-Pseudometric-Space A C
  comp-isometry-Pseudometric-Space g f =
    ( map-isometry-Pseudometric-Space B C g ∘
      map-isometry-Pseudometric-Space A B f) ,
    ( is-isometry-comp-Pseudometric-Space
      ( map-isometry-Pseudometric-Space B C g)
      ( map-isometry-Pseudometric-Space A B f)
      ( is-isometry-map-isometry-Pseudometric-Space B C g)
      ( is-isometry-map-isometry-Pseudometric-Space A B f))
```

### Unit laws for composition of isometries between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (f : isometry-Pseudometric-Space A B)
  where

  left-unit-law-comp-isometry-Pseudometric-Space :
    ( comp-isometry-Pseudometric-Space A B B
      ( id-isometry-Pseudometric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-isometry-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( comp-isometry-Pseudometric-Space
        ( A)
        ( B)
        ( B)
        ( id-isometry-Pseudometric-Space B)
        ( f))
      ( f)
      ( refl-htpy)

  right-unit-law-comp-isometry-Pseudometric-Space :
    ( comp-isometry-Pseudometric-Space A A B
      ( f)
      ( id-isometry-Pseudometric-Space A)) ＝
    ( f)
  right-unit-law-comp-isometry-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( f)
      ( comp-isometry-Pseudometric-Space
        ( A)
        ( A)
        ( B)
        ( f)
        ( id-isometry-Pseudometric-Space A))
      ( refl-htpy)
```

### Associativity of composition of isometries between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  (D : Pseudometric-Space l1d l2d)
  (h : isometry-Pseudometric-Space C D)
  (g : isometry-Pseudometric-Space B C)
  (f : isometry-Pseudometric-Space A B)
  where

  associative-comp-isometry-Pseudometric-Space :
    ( comp-isometry-Pseudometric-Space A B D
      ( comp-isometry-Pseudometric-Space B C D h g)
      ( f)) ＝
    ( comp-isometry-Pseudometric-Space A C D
      ( h)
      ( comp-isometry-Pseudometric-Space A B C g f))
  associative-comp-isometry-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space
      ( A)
      ( D)
      ( comp-isometry-Pseudometric-Space A B D
        ( comp-isometry-Pseudometric-Space B C D h g)
        ( f))
      ( comp-isometry-Pseudometric-Space A C D
        ( h)
        ( comp-isometry-Pseudometric-Space A B C g f))
      ( refl-htpy)
```

### The inverse of an isometric equivalence is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  (I : is-isometry-Pseudometric-Space A B f)
  (E : is-equiv f)
  where

  is-isometry-map-inv-is-equiv-is-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space B A (map-inv-is-equiv E)
  is-isometry-map-inv-is-equiv-is-isometry-Pseudometric-Space d x y =
    logical-equivalence-reasoning
      ( neighborhood-Pseudometric-Space B d x y)
      ↔ ( neighborhood-Pseudometric-Space B d
          ( f (map-inv-is-equiv E x))
          ( f (map-inv-is-equiv E y)))
        by
          binary-tr
            ( λ u v →
              ( neighborhood-Pseudometric-Space B d x y) ↔
              ( neighborhood-Pseudometric-Space B d u v))
            ( inv (is-section-map-inv-is-equiv E x))
            ( inv (is-section-map-inv-is-equiv E y))
            ( id-iff)
      ↔ ( neighborhood-Pseudometric-Space A d
          ( map-inv-is-equiv E x)
          ( map-inv-is-equiv E y))
        by
          inv-iff
            ( I d (map-inv-is-equiv E x) (map-inv-is-equiv E y))

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  (E : is-equiv (map-isometry-Pseudometric-Space A B f))
  where

  isometry-inv-is-equiv-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space B A
  isometry-inv-is-equiv-isometry-Pseudometric-Space =
    ( map-inv-is-equiv E) ,
    ( is-isometry-map-inv-is-equiv-is-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( map-isometry-Pseudometric-Space A B f)
      ( is-isometry-map-isometry-Pseudometric-Space A B f)
      ( E))

  is-section-isometry-inv-is-equiv-isometry-Pseudometric-Space :
    ( comp-isometry-Pseudometric-Space B A B
      ( f)
      ( isometry-inv-is-equiv-isometry-Pseudometric-Space)) ＝
    ( id-isometry-Pseudometric-Space B)
  is-section-isometry-inv-is-equiv-isometry-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space B B
      ( comp-isometry-Pseudometric-Space B A B
        ( f)
        ( isometry-inv-is-equiv-isometry-Pseudometric-Space))
      ( id-isometry-Pseudometric-Space B)
      ( is-section-map-inv-is-equiv E)

  is-retraction-isometry-inv-is-equiv-isometry-Pseudometric-Space :
    ( comp-isometry-Pseudometric-Space A B A
      ( isometry-inv-is-equiv-isometry-Pseudometric-Space)
      ( f)) ＝
    ( id-isometry-Pseudometric-Space A)
  is-retraction-isometry-inv-is-equiv-isometry-Pseudometric-Space =
    eq-htpy-map-isometry-Pseudometric-Space A A
      ( comp-isometry-Pseudometric-Space A B A
        ( isometry-inv-is-equiv-isometry-Pseudometric-Space)
        ( f))
      ( id-isometry-Pseudometric-Space A)
      ( is-retraction-map-inv-is-equiv E)
```

### Retractions of isometries between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : isometry-Pseudometric-Space A B)
  where

  retraction-isometry-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  retraction-isometry-Pseudometric-Space =
    Σ ( isometry-Pseudometric-Space B A)
      ( λ g →
        is-retraction
          ( map-isometry-Pseudometric-Space A B f)
          ( map-isometry-Pseudometric-Space B A g))
```
