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
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-spaces-WIP
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

Two elements `x y` of a [premetric space](metric-spaces.premetric-spaces-WIP.md)
are
{{#concept "similar" Disambiguation="elements of a premetric space" Agda=sim-Premetric-Space-WIP}}
if any of the following equivalent propositions holds:

- they are similar w.r.t the underlying
  [rational neighborhood relation](metric-spaces.rational-neighborhoods.md);
- they have the same neighbors: `∀ δ z → N δ x z ↔ N δ y z`;
- they share all neighborhoods: `∀ δ → N δ x y`.

Similarity in a premetric space is an
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

  sim-eq-Premetric-Space-WIP :
    (x y : type-Premetric-Space-WIP A) →
    x ＝ y →
    sim-Premetric-Space-WIP A x y
  sim-eq-Premetric-Space-WIP x .x refl =
    refl-sim-Premetric-Space-WIP x
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

  inv-sim-Premetric-Space-WIP :
    {x y : type-Premetric-Space-WIP A} →
    sim-Premetric-Space-WIP A x y →
    sim-Premetric-Space-WIP A y x
  inv-sim-Premetric-Space-WIP {x} {y} =
    symmetric-sim-Premetric-Space-WIP x y
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

  is-equivalence-relation-sim-Premetric-Space-WIP :
    is-equivalence-relation (sim-prop-Premetric-Space-WIP A)
  is-equivalence-relation-sim-Premetric-Space-WIP =
    ( refl-sim-Premetric-Space-WIP A) ,
    ( symmetric-sim-Premetric-Space-WIP A) ,
    ( transitive-sim-Premetric-Space-WIP A)

  equivalence-sim-Premetric-Space-WIP :
    equivalence-relation l2 (type-Premetric-Space-WIP A)
  equivalence-sim-Premetric-Space-WIP =
    ( sim-prop-Premetric-Space-WIP A) ,
    ( is-equivalence-relation-sim-Premetric-Space-WIP)
```

### Similar elements are elements with the same neighbors

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  preserves-neighborhood-sim-Premetric-Space :
    { x y : type-Premetric-Space-WIP A} →
    ( sim-Premetric-Space-WIP A x y) →
    ( d : ℚ⁺) (z : type-Premetric-Space-WIP A) →
    neighborhood-Premetric-Space-WIP A d x z →
    neighborhood-Premetric-Space-WIP A d y z
  preserves-neighborhood-sim-Premetric-Space {x} {y} x≍y d z Nxz =
    saturated-neighborhood-Premetric-Space-WIP
      ( A)
      ( d)
      ( y)
      ( z)
      ( λ δ →
        tr
          ( is-upper-bound-dist-Premetric-Space-WIP A y z)
          ( commutative-add-ℚ⁺ δ d)
          ( triangular-neighborhood-Premetric-Space-WIP
            ( A)
            ( y)
            ( x)
            ( z)
            ( δ)
            ( d)
            ( Nxz)
            ( symmetric-neighborhood-Premetric-Space-WIP
              ( A)
              ( δ)
              ( x)
              ( y)
              ( x≍y δ))))

  iff-same-neighbors-sim-Premetric-Space :
    { x y : type-Premetric-Space-WIP A} →
    ( sim-Premetric-Space-WIP A x y) ↔
    ( (d : ℚ⁺) (z : type-Premetric-Space-WIP A) →
      neighborhood-Premetric-Space-WIP A d x z ↔
      neighborhood-Premetric-Space-WIP A d y z)
  iff-same-neighbors-sim-Premetric-Space =
    ( λ x≍y d z →
      ( preserves-neighborhood-sim-Premetric-Space x≍y d z) ,
      ( preserves-neighborhood-sim-Premetric-Space
        ( inv-sim-Premetric-Space-WIP A x≍y)
        ( d)
        ( z))) ,
    ( λ same-neighbors d →
      backward-implication
        ( same-neighbors d _)
        ( refl-sim-Premetric-Space-WIP A _ d))
```

### Similar elements are elements similar w.r.t the underlying rational neighborhood relation

```agda
module _
  {l1 l2 : Level} (A : Premetric-Space-WIP l1 l2)
  where

  iff-same-neighbors-same-neighborhood-Premetric-Space :
    {x y : type-Premetric-Space-WIP A} →
    ( (d : ℚ⁺) (z : type-Premetric-Space-WIP A) →
      neighborhood-Premetric-Space-WIP A d x z ↔
      neighborhood-Premetric-Space-WIP A d y z) ↔
    ( sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Premetric-Space-WIP A)
      ( x)
      ( y))
  iff-same-neighbors-same-neighborhood-Premetric-Space =
    ( λ H d z →
      ( H d z) ,
      ( inv-neighborhood-Premetric-Space-WIP A ∘
        pr1 (H d z) ∘
        inv-neighborhood-Premetric-Space-WIP A) ,
      ( inv-neighborhood-Premetric-Space-WIP A ∘
        pr2 (H d z) ∘
        inv-neighborhood-Premetric-Space-WIP A)) ,
    ( iff-left-neighbor-sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Premetric-Space-WIP A))

  iff-same-neighborhood-sim-Premetric-Space :
    { x y : type-Premetric-Space-WIP A} →
    ( sim-Premetric-Space-WIP A x y) ↔
    ( sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Premetric-Space-WIP A)
      ( x)
      ( y))
  iff-same-neighborhood-sim-Premetric-Space =
    ( iff-same-neighbors-same-neighborhood-Premetric-Space) ∘iff
    ( iff-same-neighbors-sim-Premetric-Space A)
```
