# Expansive maps between pseudometric spaces

```agda
module metric-spaces.expansive-maps-pseudometric-spaces where
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
{{#concept "expansive" Disambiguation="maps between pseudometric spaces" Agda=is-expansive-map-Pseudometric-Space}}
if for any two points `x` and `y` in `A`, if `f x` and `f y` share an
`ε`-neighborhood in `B` then `x` and `y` share an `ε`-neighborhood in `A`. In
other words, `f` reflects neighborhoods.

## Definitions

### The property of being an expansive map between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  where

  is-expansive-map-prop-Pseudometric-Space : Prop (l1 ⊔ l2 ⊔ l2')
  is-expansive-map-prop-Pseudometric-Space =
    leq-prop-Rational-Neighborhood-Relation
      ( preimage-Rational-Neighborhood-Relation
        ( f)
        ( neighborhood-prop-Pseudometric-Space B))
      ( neighborhood-prop-Pseudometric-Space A)

  is-expansive-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l2')
  is-expansive-map-Pseudometric-Space =
    type-Prop is-expansive-map-prop-Pseudometric-Space

  is-prop-is-expansive-map-Pseudometric-Space :
    is-prop is-expansive-map-Pseudometric-Space
  is-prop-is-expansive-map-Pseudometric-Space =
    is-prop-type-Prop is-expansive-map-prop-Pseudometric-Space
```

### The set of expansive maps between pseudometric spaces

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  expansive-map-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  expansive-map-Pseudometric-Space =
    type-subtype (is-expansive-map-prop-Pseudometric-Space A B)

module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : expansive-map-Pseudometric-Space A B)
  where

  map-expansive-map-Pseudometric-Space : map-Pseudometric-Space A B
  map-expansive-map-Pseudometric-Space = pr1 f

  is-expansive-map-expansive-map-Pseudometric-Space :
    is-expansive-map-Pseudometric-Space A B
      ( map-expansive-map-Pseudometric-Space)
  is-expansive-map-expansive-map-Pseudometric-Space = pr2 f
```

## Properties

### The identity map on a pseudometric space is expansive

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-expansive-map-id-map-Pseudometric-Space :
    is-expansive-map-Pseudometric-Space A A (id-map-Pseudometric-Space A)
  is-expansive-map-id-map-Pseudometric-Space d x y H = H

  id-expansive-map-Pseudometric-Space :
    expansive-map-Pseudometric-Space A A
  id-expansive-map-Pseudometric-Space =
    ( id-map-Pseudometric-Space A , is-expansive-map-id-map-Pseudometric-Space)
```

### Equality of expansive maps between pseudometric spaces is characterized by homotopy of their underlying maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f g : expansive-map-Pseudometric-Space A B)
  where

  htpy-map-expansive-map-Pseudometric-Space : UU (l1 ⊔ l1')
  htpy-map-expansive-map-Pseudometric-Space =
    map-expansive-map-Pseudometric-Space A B f ~
    map-expansive-map-Pseudometric-Space A B g

  equiv-eq-htpy-map-expansive-map-Pseudometric-Space :
    (f ＝ g) ≃ htpy-map-expansive-map-Pseudometric-Space
  equiv-eq-htpy-map-expansive-map-Pseudometric-Space =
    ( equiv-funext) ∘e
    ( extensionality-type-subtype'
      ( is-expansive-map-prop-Pseudometric-Space A B)
      ( f)
      ( g))

  eq-htpy-map-expansive-map-Pseudometric-Space :
    htpy-map-expansive-map-Pseudometric-Space → f ＝ g
  eq-htpy-map-expansive-map-Pseudometric-Space =
    map-inv-equiv equiv-eq-htpy-map-expansive-map-Pseudometric-Space
```

### Composition of expansive maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  where

  is-expansive-map-comp-Pseudometric-Space :
    (g : map-Pseudometric-Space B C) →
    (f : map-Pseudometric-Space A B) →
    is-expansive-map-Pseudometric-Space B C g →
    is-expansive-map-Pseudometric-Space A B f →
    is-expansive-map-Pseudometric-Space A C (g ∘ f)
  is-expansive-map-comp-Pseudometric-Space g f H K d x y =
    K d x y ∘ H d (f x) (f y)

  comp-expansive-map-Pseudometric-Space :
    expansive-map-Pseudometric-Space B C →
    expansive-map-Pseudometric-Space A B →
    expansive-map-Pseudometric-Space A C
  comp-expansive-map-Pseudometric-Space g f =
    ( map-expansive-map-Pseudometric-Space B C g ∘
      map-expansive-map-Pseudometric-Space A B f) ,
    ( is-expansive-map-comp-Pseudometric-Space
      ( map-expansive-map-Pseudometric-Space B C g)
      ( map-expansive-map-Pseudometric-Space A B f)
      ( is-expansive-map-expansive-map-Pseudometric-Space B C g)
      ( is-expansive-map-expansive-map-Pseudometric-Space A B f))
```

### Unit laws for composition of expansive maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (f : expansive-map-Pseudometric-Space A B)
  where

  left-unit-law-comp-expansive-map-Pseudometric-Space :
    ( comp-expansive-map-Pseudometric-Space A B B
      ( id-expansive-map-Pseudometric-Space B)
      ( f)) ＝
    ( f)
  left-unit-law-comp-expansive-map-Pseudometric-Space = refl

  right-unit-law-comp-expansive-map-Pseudometric-Space :
    ( comp-expansive-map-Pseudometric-Space A A B
      ( f)
      ( id-expansive-map-Pseudometric-Space A)) ＝
    ( f)
  right-unit-law-comp-expansive-map-Pseudometric-Space = refl
```

### Associativity of composition of expansive maps between pseudometric spaces

```agda
module _
  {l1a l2a l1b l2b l1c l2c l1d l2d : Level}
  (A : Pseudometric-Space l1a l2a)
  (B : Pseudometric-Space l1b l2b)
  (C : Pseudometric-Space l1c l2c)
  (D : Pseudometric-Space l1d l2d)
  (h : expansive-map-Pseudometric-Space C D)
  (g : expansive-map-Pseudometric-Space B C)
  (f : expansive-map-Pseudometric-Space A B)
  where

  associative-comp-expansive-map-Pseudometric-Space :
    ( comp-expansive-map-Pseudometric-Space A B D
      ( comp-expansive-map-Pseudometric-Space B C D h g)
        ( f)) ＝
    ( comp-expansive-map-Pseudometric-Space A C D
      ( h)
      ( comp-expansive-map-Pseudometric-Space A B C g f))
  associative-comp-expansive-map-Pseudometric-Space =
    eq-htpy-map-expansive-map-Pseudometric-Space
      ( A)
      ( D)
      ( comp-expansive-map-Pseudometric-Space A B D
        ( comp-expansive-map-Pseudometric-Space B C D h g)
        ( f))
      ( comp-expansive-map-Pseudometric-Space A C D
        ( h)
        ( comp-expansive-map-Pseudometric-Space A B C g f))
      ( λ x → refl)
```

### Any isometry between pseudometric spaces is expansive

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  (f : map-Pseudometric-Space A B)
  where

  is-expansive-map-is-isometry-Pseudometric-Space :
    is-isometry-Pseudometric-Space A B f →
    is-expansive-map-Pseudometric-Space A B f
  is-expansive-map-is-isometry-Pseudometric-Space I =
    reflects-neighborhoods-map-isometry-Pseudometric-Space A B (f , I)
```

### The embedding of isometries of pseudometric spaces into expansive maps

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2) (B : Pseudometric-Space l1' l2')
  where

  expansive-map-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B → expansive-map-Pseudometric-Space A B
  expansive-map-isometry-Pseudometric-Space f =
    map-isometry-Pseudometric-Space A B f ,
    is-expansive-map-is-isometry-Pseudometric-Space
      ( A)
      ( B)
      ( map-isometry-Pseudometric-Space A B f)
      ( is-isometry-map-isometry-Pseudometric-Space A B f)

  is-emb-expansive-map-isometry-Pseudometric-Space :
    is-emb expansive-map-isometry-Pseudometric-Space
  is-emb-expansive-map-isometry-Pseudometric-Space =
    is-emb-right-factor
      ( map-expansive-map-Pseudometric-Space A B)
      ( expansive-map-isometry-Pseudometric-Space)
      ( is-emb-inclusion-subtype
        ( is-expansive-map-prop-Pseudometric-Space A B))
      ( is-emb-inclusion-subtype (is-isometry-prop-Pseudometric-Space A B))

  emb-expansive-map-isometry-Pseudometric-Space :
    isometry-Pseudometric-Space A B ↪ expansive-map-Pseudometric-Space A B
  emb-expansive-map-isometry-Pseudometric-Space =
    ( expansive-map-isometry-Pseudometric-Space ,
      is-emb-expansive-map-isometry-Pseudometric-Space)
```
