# Elements of premetric spaces with same neighbors

```agda
module metric-spaces.same-neighbors-elements-premetric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-spaces-WIP
```

</details>

## Idea

Two elements of a [premetric space](metric-spaces.premetric-Metric-Space-WIP.md)
have the {{#concept "same neighbors" Agda=sim-Premetric-Space-WIP'}} if their
neighborhoods are [equivalent](foundation.logical-equivalences.md). Having the
same neighbors is an [equivalence relation](foundation.equivalence-relations.md)
on the carrier type of the premetric space.

## Definitions

### Neighborhood similarity relation in premetric spaces

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  sim-prop-Premetric-Space-WIP' :
    Relation-Prop (l1 ⊔ l2) (type-Premetric-Space-WIP A)
  sim-prop-Premetric-Space-WIP' x y =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( type-Premetric-Space-WIP A)
          ( λ z →
            neighborhood-prop-Premetric-Space-WIP A ε x z ⇔
            neighborhood-prop-Premetric-Space-WIP A ε y z))

  sim-Premetric-Space-WIP' :
    Relation (l1 ⊔ l2) (type-Premetric-Space-WIP A)
  sim-Premetric-Space-WIP' =
    type-Relation-Prop sim-prop-Premetric-Space-WIP'

  is-prop-sim-Premetric-Space-WIP' :
    (x y : type-Premetric-Space-WIP A) →
    is-prop (sim-Premetric-Space-WIP' x y)
  is-prop-sim-Premetric-Space-WIP' =
    is-prop-type-Relation-Prop sim-prop-Premetric-Space-WIP'
```

## Properties

### Similarity in premetric spaces is reflexive

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  refl-sim-Premetric-Space-WIP' :
    (x : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP' A x x
  refl-sim-Premetric-Space-WIP' x d z =
    id-iff

  sim-eq-Premetric-Space-WIP' :
    (x y : type-Premetric-Space-WIP A) →
    x ＝ y →
    sim-Premetric-Space-WIP' A x y
  sim-eq-Premetric-Space-WIP' x .x refl =
    refl-sim-Premetric-Space-WIP' x
```

### Similarity in premetric spaces is symmetric

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  symmetric-sim-Premetric-Space-WIP' :
    (x y : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP' A x y →
    sim-Premetric-Space-WIP' A y x
  symmetric-sim-Premetric-Space-WIP' x y Nxy d z =
    inv-iff (Nxy d z)

  inv-sim-Premetric-Space-WIP' :
    {x y : type-Premetric-Space-WIP A} →
    sim-Premetric-Space-WIP' A x y →
    sim-Premetric-Space-WIP' A y x
  inv-sim-Premetric-Space-WIP' {x} {y} =
    symmetric-sim-Premetric-Space-WIP' x y
```

### Similarity in premetric spaces is transitive

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  transitive-sim-Premetric-Space-WIP' :
    (x y z : type-Premetric-Space-WIP A) →
    sim-Premetric-Space-WIP' A y z →
    sim-Premetric-Space-WIP' A x y →
    sim-Premetric-Space-WIP' A x z
  transitive-sim-Premetric-Space-WIP' x y z Nyz Nxy d w =
    ( Nyz d w) ∘iff (Nxy d w)
```

### Similarity in premetric spaces is an equivalence relation

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  is-equivalence-relation-sim-Premetric-Space-WIP' :
    is-equivalence-relation (sim-prop-Premetric-Space-WIP' A)
  is-equivalence-relation-sim-Premetric-Space-WIP' =
    ( refl-sim-Premetric-Space-WIP' A) ,
    ( symmetric-sim-Premetric-Space-WIP' A) ,
    ( transitive-sim-Premetric-Space-WIP' A)

  equivalence-sim-Premetric-Space-WIP' :
    equivalence-relation (l1 ⊔ l2) (type-Premetric-Space-WIP A)
  equivalence-sim-Premetric-Space-WIP' =
    ( sim-prop-Premetric-Space-WIP' A) ,
    ( is-equivalence-relation-sim-Premetric-Space-WIP')
```
