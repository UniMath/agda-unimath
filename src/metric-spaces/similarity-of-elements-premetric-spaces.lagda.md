# Similarity of elements in premetric spaces

```agda
module metric-spaces.similarity-of-elements-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-spaces-WIP
```

</details>

## Idea

Two elements `x y` of a [premetric space](metric-spaces.premetric-spaces-WIP.md)
are
{{#concept "similar" Disambiguation="elements of a premetric space" Agda=sim-Premetric-Space-WIP}}
if they share all neighborhoods. Similarity in premetric spaces is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### Neighborhood similarity relation in premetric spaces

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  sim-prop-Premetric-Space-WIP :
    Relation-Prop l2 (type-Premetric-Space-WIP A)
  sim-prop-Premetric-Space-WIP x y =
    Π-Prop ℚ⁺ (is-upper-bound-dist-prop-Premetric-Space-WIP A x y)

  sim-Premetric-Space-WIP :
    Relation l2 (type-Premetric-Space-WIP A)
  sim-Premetric-Space-WIP =
    type-Relation-Prop sim-prop-Premetric-Space-WIP

  is-prop-sim-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    is-prop (sim-Premetric-Space-WIP x y)
  is-prop-sim-Premetric-Space-WIP =
    is-prop-type-Relation-Prop sim-prop-Premetric-Space-WIP
```

## Properties

### Similarity in premetric spaces is reflexive

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  refl-sim-Premetric-Space-WIP :
    (x : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP A x x
  refl-sim-Premetric-Space-WIP x d =
    refl-neighborhood-Premetric-Space-WIP A d x
```

### Similarity in premetric spaces is symmetric

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  symmetric-sim-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP A x y →
    sim-Premetric-Space-WIP A y x
  symmetric-sim-Premetric-Space-WIP x y Nxy d =
    symmetric-neighborhood-Premetric-Space-WIP A d x y (Nxy d)
```

### Similarity in premetric spaces is transitive

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  transitive-sim-Premetric-Space-WIP :
    (x y z : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP A y z →
    sim-Premetric-Space-WIP A x y →
    sim-Premetric-Space-WIP A x z
  transitive-sim-Premetric-Space-WIP x y z Nyz Nxy d =
    tr
      ( is-upper-bound-dist-Premetric-Space-WIP A x z)
      ( eq-add-split-ℚ⁺ d)
      ( triangular-neighborhood-Premetric-Space-WIP
        ( A)
        ( x)
        ( y)
        ( z)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( Nyz (right-summand-split-ℚ⁺ d))
        ( Nxy (left-summand-split-ℚ⁺ d)))
```

### Similarity in premetric spaces is an equivalence relation

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  is-equivalence-relation-sim-Premetric-Space :
    is-equivalence-relation (sim-prop-Premetric-Space-WIP A)
  is-equivalence-relation-sim-Premetric-Space =
    ( refl-sim-Premetric-Space-WIP A) ,
    ( symmetric-sim-Premetric-Space-WIP A) ,
    ( transitive-sim-Premetric-Space-WIP A)

  equivalence-sim-Premetric-Space :
    equivalence-relation l2 (type-Premetric-Space-WIP A)
  equivalence-sim-Premetric-Space =
    ( sim-prop-Premetric-Space-WIP A) ,
    ( is-equivalence-relation-sim-Premetric-Space)
```
