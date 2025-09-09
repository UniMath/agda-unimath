# Similarity of elements in pseudometric spaces

```agda
{-# OPTIONS --lossy-unification #-}

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

open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-pseudometric-spaces
```

</details>

## Idea

Two elements `x y` of a
[pseudometric space](metric-spaces.pseudometric-spaces.md) are
{{#concept "similar" Disambiguation="elements of a pseudometric space" Agda=sim-Pseudometric-Space}}
if any of the following equivalent propositions holds:

- they are similar w.r.t the underlying
  [rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md);
- they have the same neighbors: `∀ δ z → N δ x z ↔ N δ y z`;
- they share all neighborhoods: `∀ δ → N δ x y`.

Similarity in a pseudometric space is an
[equivalence relation](foundation.equivalence-relations.md).

## Definitions

### Neighborhood similarity relation in pseudometric spaces

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  sim-prop-Pseudometric-Space :
    Relation-Prop l2 (type-Pseudometric-Space A)
  sim-prop-Pseudometric-Space x y =
    Π-Prop ℚ⁺ (is-upper-bound-dist-prop-Pseudometric-Space A x y)

  sim-Pseudometric-Space :
    Relation l2 (type-Pseudometric-Space A)
  sim-Pseudometric-Space =
    type-Relation-Prop sim-prop-Pseudometric-Space

  is-prop-sim-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    is-prop (sim-Pseudometric-Space x y)
  is-prop-sim-Pseudometric-Space =
    is-prop-type-Relation-Prop sim-prop-Pseudometric-Space
```

## Properties

### Similarity in pseudometric spaces is reflexive

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  refl-sim-Pseudometric-Space :
    (x : type-Pseudometric-Space A) →
    sim-Pseudometric-Space A x x
  refl-sim-Pseudometric-Space x d =
    refl-neighborhood-Pseudometric-Space A d x

  sim-eq-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    x ＝ y →
    sim-Pseudometric-Space A x y
  sim-eq-Pseudometric-Space x .x refl =
    refl-sim-Pseudometric-Space x
```

### Similarity in pseudometric spaces is symmetric

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  symmetric-sim-Pseudometric-Space :
    (x y : type-Pseudometric-Space A) →
    sim-Pseudometric-Space A x y →
    sim-Pseudometric-Space A y x
  symmetric-sim-Pseudometric-Space x y Nxy d =
    symmetric-neighborhood-Pseudometric-Space A d x y (Nxy d)

  inv-sim-Pseudometric-Space :
    {x y : type-Pseudometric-Space A} →
    sim-Pseudometric-Space A x y →
    sim-Pseudometric-Space A y x
  inv-sim-Pseudometric-Space {x} {y} =
    symmetric-sim-Pseudometric-Space x y
```

### Similarity in pseudometric spaces is transitive

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  abstract
    transitive-sim-Pseudometric-Space :
      (x y z : type-Pseudometric-Space A) →
      sim-Pseudometric-Space A y z →
      sim-Pseudometric-Space A x y →
      sim-Pseudometric-Space A x z
    transitive-sim-Pseudometric-Space x y z Nyz Nxy d =
      tr
        ( is-upper-bound-dist-Pseudometric-Space A x z)
        ( eq-add-split-ℚ⁺ d)
        ( triangular-neighborhood-Pseudometric-Space
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
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  is-equivalence-relation-sim-Pseudometric-Space :
    is-equivalence-relation (sim-prop-Pseudometric-Space A)
  is-equivalence-relation-sim-Pseudometric-Space =
    ( refl-sim-Pseudometric-Space A) ,
    ( symmetric-sim-Pseudometric-Space A) ,
    ( transitive-sim-Pseudometric-Space A)

  equivalence-relation-sim-Pseudometric-Space :
    equivalence-relation l2 (type-Pseudometric-Space A)
  equivalence-relation-sim-Pseudometric-Space =
    ( sim-prop-Pseudometric-Space A) ,
    ( is-equivalence-relation-sim-Pseudometric-Space)
```

### Similar elements are elements with the same neighbors

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  abstract
    preserves-neighborhood-left-sim-Pseudometric-Space :
      { x y : type-Pseudometric-Space A} →
      ( sim-Pseudometric-Space A x y) →
      ( d : ℚ⁺) (z : type-Pseudometric-Space A) →
      neighborhood-Pseudometric-Space A d x z →
      neighborhood-Pseudometric-Space A d y z
    preserves-neighborhood-left-sim-Pseudometric-Space {x} {y} x≍y d z Nxz =
      saturated-neighborhood-Pseudometric-Space
        ( A)
        ( d)
        ( y)
        ( z)
        ( λ δ →
          tr
            ( is-upper-bound-dist-Pseudometric-Space A y z)
            ( commutative-add-ℚ⁺ δ d)
            ( triangular-neighborhood-Pseudometric-Space
              ( A)
              ( y)
              ( x)
              ( z)
              ( δ)
              ( d)
              ( Nxz)
              ( symmetric-neighborhood-Pseudometric-Space
                ( A)
                ( δ)
                ( x)
                ( y)
                ( x≍y δ))))

    preserves-neighborhood-right-sim-Pseudometric-Space :
      { x y : type-Pseudometric-Space A} →
      ( sim-Pseudometric-Space A x y) →
      ( d : ℚ⁺) (z : type-Pseudometric-Space A) →
      neighborhood-Pseudometric-Space A d z x →
      neighborhood-Pseudometric-Space A d z y
    preserves-neighborhood-right-sim-Pseudometric-Space {x} {y} x≍y d z Nzx =
      symmetric-neighborhood-Pseudometric-Space A d y z
        ( preserves-neighborhood-left-sim-Pseudometric-Space x≍y d z
          ( symmetric-neighborhood-Pseudometric-Space A d z x Nzx))

    preserves-neighborhood-sim-Pseudometric-Space :
      {x x' y y' : type-Pseudometric-Space A} →
      sim-Pseudometric-Space A x x' →
      sim-Pseudometric-Space A y y' →
      (d : ℚ⁺) →
      neighborhood-Pseudometric-Space A d x y →
      neighborhood-Pseudometric-Space A d x' y'
    preserves-neighborhood-sim-Pseudometric-Space
      {x} {x'} {y} {y'} x~x' y~y' d Nxy =
      preserves-neighborhood-left-sim-Pseudometric-Space
        ( x~x')
        ( d)
        ( y')
        ( preserves-neighborhood-right-sim-Pseudometric-Space
          ( y~y')
          ( d)
          ( x)
          ( Nxy))

    reflects-neighborhood-sim-Pseudometric-Space :
      {x x' y y' : type-Pseudometric-Space A} →
      sim-Pseudometric-Space A x x' →
      sim-Pseudometric-Space A y y' →
      (d : ℚ⁺) →
      neighborhood-Pseudometric-Space A d x' y' →
      neighborhood-Pseudometric-Space A d x y
    reflects-neighborhood-sim-Pseudometric-Space
      {x} {x'} {y} {y'} x~x' y~y' =
      preserves-neighborhood-sim-Pseudometric-Space
        ( inv-sim-Pseudometric-Space A x~x')
        ( inv-sim-Pseudometric-Space A y~y')

    iff-same-neighbors-sim-Pseudometric-Space :
      { x y : type-Pseudometric-Space A} →
      ( sim-Pseudometric-Space A x y) ↔
      ( (d : ℚ⁺) (z : type-Pseudometric-Space A) →
        neighborhood-Pseudometric-Space A d x z ↔
        neighborhood-Pseudometric-Space A d y z)
    iff-same-neighbors-sim-Pseudometric-Space =
      ( λ x≍y d z →
        ( preserves-neighborhood-left-sim-Pseudometric-Space x≍y d z) ,
        ( preserves-neighborhood-left-sim-Pseudometric-Space
          ( inv-sim-Pseudometric-Space A x≍y)
          ( d)
          ( z))) ,
      ( λ same-neighbors d →
        backward-implication
          ( same-neighbors d _)
          ( refl-sim-Pseudometric-Space A _ d))
```

### Similar elements are elements similar w.r.t the underlying rational neighborhood relation

```agda
module _
  {l1 l2 : Level} (A : Pseudometric-Space l1 l2)
  where

  abstract
    iff-same-neighbors-same-neighborhood-Pseudometric-Space :
      {x y : type-Pseudometric-Space A} →
      ( (d : ℚ⁺) (z : type-Pseudometric-Space A) →
        neighborhood-Pseudometric-Space A d x z ↔
        neighborhood-Pseudometric-Space A d y z) ↔
      ( sim-Rational-Neighborhood-Relation
        ( neighborhood-prop-Pseudometric-Space A)
        ( x)
        ( y))
    iff-same-neighbors-same-neighborhood-Pseudometric-Space =
      ( λ H d z →
        ( H d z) ,
        ( inv-neighborhood-Pseudometric-Space A ∘
          pr1 (H d z) ∘
          inv-neighborhood-Pseudometric-Space A) ,
        ( inv-neighborhood-Pseudometric-Space A ∘
          pr2 (H d z) ∘
          inv-neighborhood-Pseudometric-Space A)) ,
      ( iff-left-neighbor-sim-Rational-Neighborhood-Relation
        ( neighborhood-prop-Pseudometric-Space A))

    iff-same-neighborhood-sim-Pseudometric-Space :
      { x y : type-Pseudometric-Space A} →
      ( sim-Pseudometric-Space A x y) ↔
      ( sim-Rational-Neighborhood-Relation
        ( neighborhood-prop-Pseudometric-Space A)
        ( x)
        ( y))
    iff-same-neighborhood-sim-Pseudometric-Space =
      ( iff-same-neighbors-same-neighborhood-Pseudometric-Space) ∘iff
      ( iff-same-neighbors-sim-Pseudometric-Space A)
```

### Short maps between pseudometric spaces preserves similarity

```agda
module _
  { l1 l2 l1' l2' : Level}
  ( A : Pseudometric-Space l1 l2)
  ( B : Pseudometric-Space l1' l2')
  ( f : short-function-Pseudometric-Space A B)
  where

  abstract
    preserves-sim-map-short-function-Pseudometric-Space :
      ( x y : type-Pseudometric-Space A) →
      ( sim-Pseudometric-Space A x y) →
      ( sim-Pseudometric-Space B
        ( map-short-function-Pseudometric-Space A B f x)
        ( map-short-function-Pseudometric-Space A B f y))
    preserves-sim-map-short-function-Pseudometric-Space x y x~y d =
      is-short-map-short-function-Pseudometric-Space A B f d x y (x~y d)
```
