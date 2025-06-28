# Similarity of elements in pseudometric spaces

```agda
module metric-spaces.similarity-of-elements-pseudometric-spaces where
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

open import metric-spaces.pseudometric-spaces-WIP
open import metric-spaces.rational-neighborhoods
```

</details>

## Idea

Two elements `x y` of a
[pseudometric space](metric-spaces.pseudometric-spaces-WIP.md) are
{{#concept "similar" Disambiguation="elements of a pseudometric space" Agda=sim-Pseudometric-Space-WIP}}
if any of the following equivalent propositions holds:

- they are similar w.r.t the underlying
  [rational neighborhood relation](metric-spaces.rational-neighborhoods.md);
- they have the same neighbors: `∀ δ z → N δ x z ↔ N δ y z`;
- they share all neighborhoods: `∀ δ → N δ x y`.

Similarity in a pseudometric space is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### Neighborhood similarity relation in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  sim-prop-Pseudometric-Space-WIP :
    Relation-Prop l2 (type-Pseudometric-Space-WIP A)
  sim-prop-Pseudometric-Space-WIP x y =
    Π-Prop ℚ⁺ (is-upper-bound-dist-prop-Pseudometric-Space-WIP A x y)

  sim-Pseudometric-Space-WIP :
    Relation l2 (type-Pseudometric-Space-WIP A)
  sim-Pseudometric-Space-WIP =
    type-Relation-Prop sim-prop-Pseudometric-Space-WIP

  is-prop-sim-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    is-prop (sim-Pseudometric-Space-WIP x y)
  is-prop-sim-Pseudometric-Space-WIP =
    is-prop-type-Relation-Prop sim-prop-Pseudometric-Space-WIP
```

## Properties

### Similarity in pseudometric spaces is reflexive

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  refl-sim-Pseudometric-Space-WIP :
    (x : type-Pseudometric-Space-WIP A) →
    sim-Pseudometric-Space-WIP A x x
  refl-sim-Pseudometric-Space-WIP x d =
    refl-neighborhood-Pseudometric-Space-WIP A d x

  sim-eq-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    x ＝ y →
    sim-Pseudometric-Space-WIP A x y
  sim-eq-Pseudometric-Space-WIP x .x refl =
    refl-sim-Pseudometric-Space-WIP x
```

### Similarity in pseudometric spaces is symmetric

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  symmetric-sim-Pseudometric-Space-WIP :
    (x y : type-Pseudometric-Space-WIP A) →
    sim-Pseudometric-Space-WIP A x y →
    sim-Pseudometric-Space-WIP A y x
  symmetric-sim-Pseudometric-Space-WIP x y Nxy d =
    symmetric-neighborhood-Pseudometric-Space-WIP A d x y (Nxy d)

  inv-sim-Pseudometric-Space-WIP :
    {x y : type-Pseudometric-Space-WIP A} →
    sim-Pseudometric-Space-WIP A x y →
    sim-Pseudometric-Space-WIP A y x
  inv-sim-Pseudometric-Space-WIP {x} {y} =
    symmetric-sim-Pseudometric-Space-WIP x y
```

### Similarity in pseudometric spaces is transitive

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  transitive-sim-Pseudometric-Space-WIP :
    (x y z : type-Pseudometric-Space-WIP A) →
    sim-Pseudometric-Space-WIP A y z →
    sim-Pseudometric-Space-WIP A x y →
    sim-Pseudometric-Space-WIP A x z
  transitive-sim-Pseudometric-Space-WIP x y z Nyz Nxy d =
    tr
      ( is-upper-bound-dist-Pseudometric-Space-WIP A x z)
      ( eq-add-split-ℚ⁺ d)
      ( triangular-neighborhood-Pseudometric-Space-WIP
        ( A)
        ( x)
        ( y)
        ( z)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( Nyz (right-summand-split-ℚ⁺ d))
        ( Nxy (left-summand-split-ℚ⁺ d)))
```

### Similarity in pseudometric spaces is an equivalence relation

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  is-equivalence-relation-sim-Pseudometric-Space-WIP :
    is-equivalence-relation (sim-prop-Pseudometric-Space-WIP A)
  is-equivalence-relation-sim-Pseudometric-Space-WIP =
    ( refl-sim-Pseudometric-Space-WIP A) ,
    ( symmetric-sim-Pseudometric-Space-WIP A) ,
    ( transitive-sim-Pseudometric-Space-WIP A)

  equivalence-sim-Pseudometric-Space-WIP :
    equivalence-relation l2 (type-Pseudometric-Space-WIP A)
  equivalence-sim-Pseudometric-Space-WIP =
    ( sim-prop-Pseudometric-Space-WIP A) ,
    ( is-equivalence-relation-sim-Pseudometric-Space-WIP)
```

### Similar elements are elements with the same neighbors

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  preserves-neighborhood-sim-Pseudometric-Space :
    { x y : type-Pseudometric-Space-WIP A} →
    ( sim-Pseudometric-Space-WIP A x y) →
    ( d : ℚ⁺) (z : type-Pseudometric-Space-WIP A) →
    neighborhood-Pseudometric-Space-WIP A d x z →
    neighborhood-Pseudometric-Space-WIP A d y z
  preserves-neighborhood-sim-Pseudometric-Space {x} {y} x≍y d z Nxz =
    saturated-neighborhood-Pseudometric-Space-WIP
      ( A)
      ( d)
      ( y)
      ( z)
      ( λ δ →
        tr
          ( is-upper-bound-dist-Pseudometric-Space-WIP A y z)
          ( commutative-add-ℚ⁺ δ d)
          ( triangular-neighborhood-Pseudometric-Space-WIP
            ( A)
            ( y)
            ( x)
            ( z)
            ( δ)
            ( d)
            ( Nxz)
            ( symmetric-neighborhood-Pseudometric-Space-WIP
              ( A)
              ( δ)
              ( x)
              ( y)
              ( x≍y δ))))

  iff-same-neighbors-sim-Pseudometric-Space :
    { x y : type-Pseudometric-Space-WIP A} →
    ( sim-Pseudometric-Space-WIP A x y) ↔
    ( (d : ℚ⁺) (z : type-Pseudometric-Space-WIP A) →
      neighborhood-Pseudometric-Space-WIP A d x z ↔
      neighborhood-Pseudometric-Space-WIP A d y z)
  iff-same-neighbors-sim-Pseudometric-Space =
    ( λ x≍y d z →
      ( preserves-neighborhood-sim-Pseudometric-Space x≍y d z) ,
      ( preserves-neighborhood-sim-Pseudometric-Space
        ( inv-sim-Pseudometric-Space-WIP A x≍y)
        ( d)
        ( z))) ,
    ( λ same-neighbors d →
      backward-implication
        ( same-neighbors d _)
        ( refl-sim-Pseudometric-Space-WIP A _ d))
```

### Similar elements are elements similar w.r.t the underlying rational neighborhood relation

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space-WIP l1 l2)
  where

  iff-same-neighbors-same-neighborhood-Pseudometric-Space :
    {x y : type-Pseudometric-Space-WIP A} →
    ( (d : ℚ⁺) (z : type-Pseudometric-Space-WIP A) →
      neighborhood-Pseudometric-Space-WIP A d x z ↔
      neighborhood-Pseudometric-Space-WIP A d y z) ↔
    ( sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space-WIP A)
      ( x)
      ( y))
  iff-same-neighbors-same-neighborhood-Pseudometric-Space =
    ( λ H d z →
      ( H d z) ,
      ( inv-neighborhood-Pseudometric-Space-WIP A ∘
        pr1 (H d z) ∘
        inv-neighborhood-Pseudometric-Space-WIP A) ,
      ( inv-neighborhood-Pseudometric-Space-WIP A ∘
        pr2 (H d z) ∘
        inv-neighborhood-Pseudometric-Space-WIP A)) ,
    ( iff-left-neighbor-sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space-WIP A))

  iff-same-neighborhood-sim-Pseudometric-Space :
    { x y : type-Pseudometric-Space-WIP A} →
    ( sim-Pseudometric-Space-WIP A x y) ↔
    ( sim-Rational-Neighborhood-Relation
      ( neighborhood-prop-Pseudometric-Space-WIP A)
      ( x)
      ( y))
  iff-same-neighborhood-sim-Pseudometric-Space =
    ( iff-same-neighbors-same-neighborhood-Pseudometric-Space) ∘iff
    ( iff-same-neighbors-sim-Pseudometric-Space A)
```
