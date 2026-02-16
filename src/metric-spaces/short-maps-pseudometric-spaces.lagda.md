# Short maps between pseudometric spaces

```agda
module metric-spaces.short-maps-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import lists.sequences

open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-pseudometric-spaces
open import metric-spaces.poset-of-rational-neighborhood-relations
open import metric-spaces.preimages-rational-neighborhood-relations
open import metric-spaces.pseudometric-spaces
```

</details>

## Idea

A [map](metric-spaces.maps-pseudometric-spaces.md) `f` between two
[pseudometric spaces](metric-spaces.pseudometric-spaces.md) `A` and `B` is
{{#concept "short" Disambiguation="map between pseudometric spaces" Agda=is-short-map-Pseudometric-Space WD="metric map" WDID=Q2713824}}
if the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
on `A` is [finer](metric-spaces.poset-of-rational-neighborhood-relations.md)
than the [preimage](metric-spaces.preimages-rational-neighborhood-relations.md)
by `f` of the rational neighborhood relation on `B`. I.e., upper bounds on the
distance between two points in `A` are upper bounds of the distance between
their images in `B`.

## Definitions

### The property of being a short map between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  where

  is-short-map-prop-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-short-map-prop-Pseudometric-Space =
    leq-prop-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space A)
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Pseudometric-Space B))

  is-short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-short-map-Pseudometric-Space =
    type-Prop is-short-map-prop-Pseudometric-Space

  is-prop-is-short-map-Pseudometric-Space :
    is-prop is-short-map-Pseudometric-Space
  is-prop-is-short-map-Pseudometric-Space =
    is-prop-type-Prop is-short-map-prop-Pseudometric-Space
```

### The set of short maps between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  short-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  short-map-Pseudometric-Space =
    type-subtype (is-short-map-prop-Pseudometric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : short-map-Pseudometric-Space A B)
  where

  map-short-map-Pseudometric-Space : map-Pseudometric-Space A B
  map-short-map-Pseudometric-Space = pr1 f

  is-short-map-short-map-Pseudometric-Space :
    is-short-map-Pseudometric-Space A B
      map-short-map-Pseudometric-Space
  is-short-map-short-map-Pseudometric-Space = pr2 f
```

## Properties

### The identity map on a pseudometric space is short

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-short-map-id-map-Pseudometric-Space :
    is-short-map-Pseudometric-Space A A (id-map-Pseudometric-Space A)
  is-short-map-id-map-Pseudometric-Space d x y H = H

  id-short-map-Pseudometric-Space :
    short-map-Pseudometric-Space A A
  id-short-map-Pseudometric-Space =
    ( id-map-Pseudometric-Space A , is-short-map-id-map-Pseudometric-Space)
```

### Equality of short maps between pseudometric spaces is characterized by homotopy of their carrier maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f g : short-map-Pseudometric-Space A B)
  where

  htpy-map-short-map-Pseudometric-Space : UU (l1 ⊔ l1')
  htpy-map-short-map-Pseudometric-Space =
    map-short-map-Pseudometric-Space A B f ~
    map-short-map-Pseudometric-Space A B g

  equiv-eq-htpy-map-short-map-Pseudometric-Space :
    (f ＝ g) ≃ htpy-map-short-map-Pseudometric-Space
  equiv-eq-htpy-map-short-map-Pseudometric-Space =
    equiv-funext ∘e
    extensionality-type-subtype'
      ( is-short-map-prop-Pseudometric-Space A B) f g

  eq-htpy-map-short-map-Pseudometric-Space :
    htpy-map-short-map-Pseudometric-Space → f ＝ g
  eq-htpy-map-short-map-Pseudometric-Space =
    map-inv-equiv equiv-eq-htpy-map-short-map-Pseudometric-Space
```

### Composition of short maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  where

  is-short-map-comp-Pseudometric-Space :
    (g : map-Pseudometric-Space B C) →
    (f : map-Pseudometric-Space A B) →
    is-short-map-Pseudometric-Space B C g →
    is-short-map-Pseudometric-Space A B f →
    is-short-map-Pseudometric-Space A C (g ∘ f)
  is-short-map-comp-Pseudometric-Space g f H K d x y =
    H d (f x) (f y) ∘ K d x y

  comp-short-map-Pseudometric-Space :
    short-map-Pseudometric-Space B C →
    short-map-Pseudometric-Space A B →
    short-map-Pseudometric-Space A C
  comp-short-map-Pseudometric-Space g f =
    ( map-short-map-Pseudometric-Space B C g ∘
      map-short-map-Pseudometric-Space A B f) ,
    ( is-short-map-comp-Pseudometric-Space
      ( map-short-map-Pseudometric-Space B C g)
      ( map-short-map-Pseudometric-Space A B f)
      ( is-short-map-short-map-Pseudometric-Space B C g)
      ( is-short-map-short-map-Pseudometric-Space A B f))
```

### Unit laws for composition of short maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (f : short-map-Pseudometric-Space A B)
  where

  left-unit-law-comp-short-map-Pseudometric-Space :
    ( comp-short-map-Pseudometric-Space A B B
      ( id-short-map-Pseudometric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-short-map-Pseudometric-Space =
    eq-htpy-map-short-map-Pseudometric-Space
      ( A)
      ( B)
      ( comp-short-map-Pseudometric-Space
        ( A)
        ( B)
        ( B)
        ( id-short-map-Pseudometric-Space B)
        ( f))
      ( f)
      ( λ x → refl)

  right-unit-law-comp-short-map-Pseudometric-Space :
    ( comp-short-map-Pseudometric-Space A A B
      ( f)
      ( id-short-map-Pseudometric-Space A)) ＝
    ( f)
  right-unit-law-comp-short-map-Pseudometric-Space =
    eq-htpy-map-short-map-Pseudometric-Space
      ( A)
      ( B)
      ( f)
      ( comp-short-map-Pseudometric-Space
        ( A)
        ( A)
        ( B)
        ( f)
        ( id-short-map-Pseudometric-Space A))
      ( λ x → refl)
```

### Associativity of composition of short maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  (D : Pseudometric-Space l1d l2d)
  (h : short-map-Pseudometric-Space C D)
  (g : short-map-Pseudometric-Space B C)
  (f : short-map-Pseudometric-Space A B)
  where

  associative-comp-short-map-Pseudometric-Space :
    ( comp-short-map-Pseudometric-Space A B D
      ( comp-short-map-Pseudometric-Space B C D h g)
        ( f)) ＝
    ( comp-short-map-Pseudometric-Space A C D
      ( h)
      ( comp-short-map-Pseudometric-Space A B C g f))
  associative-comp-short-map-Pseudometric-Space =
    eq-htpy-map-short-map-Pseudometric-Space
      ( A)
      ( D)
      ( comp-short-map-Pseudometric-Space A B D
        ( comp-short-map-Pseudometric-Space B C D h g)
        ( f))
      ( comp-short-map-Pseudometric-Space A C D
        ( h)
        ( comp-short-map-Pseudometric-Space A B C g f))
      ( λ x → refl)
```

### Constant maps between pseudometric spaces are short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (b : type-Pseudometric-Space B)
  where

  is-short-map-const-Pseudometric-Space :
    is-short-map-Pseudometric-Space A B (const-map-Pseudometric-Space A B b)
  is-short-map-const-Pseudometric-Space ε x y H =
    refl-neighborhood-Pseudometric-Space B ε b

  const-short-map-Pseudometric-Space :
    short-map-Pseudometric-Space A B
  pr1 const-short-map-Pseudometric-Space =
    const-map-Pseudometric-Space A B b
  pr2 const-short-map-Pseudometric-Space =
    is-short-map-const-Pseudometric-Space
```

### Any isometry between pseudometric spaces is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  where

  is-short-map-is-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space A B f →
    is-short-map-Pseudometric-Space A B f
  is-short-map-is-isometry-Pseudometric-Space I =
    preserves-neighborhoods-map-isometry-Pseudometric-Space A B (f , I)
```

### The embedding of isometries of pseudometric spaces into short maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  short-map-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B → short-map-Pseudometric-Space A B
  short-map-isometry-Pseudometric-Space f =
    map-isometry-Pseudometric-Space A B f ,
    is-short-map-is-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( map-isometry-Pseudometric-Space A B f)
      ( is-isometry-map-isometry-Pseudometric-Space A B f)

  is-emb-short-map-isometry-Pseudometric-Space :
    is-emb short-map-isometry-Pseudometric-Space
  is-emb-short-map-isometry-Pseudometric-Space =
    is-emb-right-factor
      ( map-short-map-Pseudometric-Space A B)
      ( short-map-isometry-Pseudometric-Space)
      ( is-emb-inclusion-subtype
        ( is-short-map-prop-Pseudometric-Space A B))
      ( is-emb-htpy
        ( λ f → refl)
        ( is-emb-inclusion-subtype (is-isometry-prop-Pseudometric-Space A B)))

  emb-short-map-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B ↪ short-map-Pseudometric-Space A B
  emb-short-map-isometry-Pseudometric-Space =
    short-map-isometry-Pseudometric-Space ,
    is-emb-short-map-isometry-Pseudometric-Space
```
