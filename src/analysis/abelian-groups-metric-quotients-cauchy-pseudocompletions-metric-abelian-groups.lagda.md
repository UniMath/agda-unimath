# The abelian groups of the metric quotients of Cauchy pseudocompletions of metric abelian groups

```agda
{-# OPTIONS --lossy-unification #-}

module analysis.abelian-groups-metric-quotients-cauchy-pseudocompletions-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.addition-cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups
open import analysis.metric-quotients-cauchy-pseudocompletions-metric-abelian-groups
open import analysis.negation-cauchy-approximations-metric-abelian-groups

open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-functoriality-set-quotients
open import foundation.dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.set-quotients
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

The [metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)
of the
[Cauchy pseudocompletion](analysis.cauchy-pseudocompletions-metric-abelian-groups.md)
of a [metric abelian group](analysis.metric-abelian-groups.md) forms an
[abelian group](group-theory.abelian-groups.md).

## Definition

### Addition in the metric quotient

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  binary-hom-add-cauchy-pseudocompletion-Metric-Ab :
    binary-hom-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
  binary-hom-add-cauchy-pseudocompletion-Metric-Ab =
    ( add-cauchy-approximation-Metric-Ab G ,
      λ {x} {x'} {y} {y'} →
        preserves-sim-add-cauchy-approximation-Metric-Ab G {x} {x'} {y} {y'})

  add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G →
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G →
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  add-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    binary-map-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( binary-hom-add-cauchy-pseudocompletion-Metric-Ab)
```

## Properties

### The embedding in the metric quotient of the Cauchy pseudocompletion preserves addition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x y : cauchy-approximation-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
        ( G)
        ( x))
      ( in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
        ( G)
        ( y)) ＝
    in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
      ( G)
      ( add-cauchy-approximation-Metric-Ab G x y)
  add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    compute-binary-map-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( binary-hom-add-cauchy-pseudocompletion-Metric-Ab G)

  add-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x y : type-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( in-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x)
      ( in-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y) ＝
    in-metric-quotient-cauchy-pseudocompletion-Metric-Ab G (add-Metric-Ab G x y)
  add-in-metric-quotient-cauchy-pseudocompletion-Metric-Ab x y =
    add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
      ( const-cauchy-approximation-Metric-Ab G x)
      ( const-cauchy-approximation-Metric-Ab G y) ∙
    apply-effectiveness-quotient-map'
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( sim-add-const-cauchy-approximation-Metric-Ab G x y)
```

### Addition in the metric quotient of the Cauchy pseudocompletion is associative

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  associative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x y z : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x y)
      ( z) ＝
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( x)
      ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y z)
  associative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    triple-induction-set-quotient'
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( λ x y z →
        Id-Prop
          ( set-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x y)
            ( z))
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
            ( x)
            ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y z)))
      ( λ x y z →
        let
          in-approx-G =
            in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          _+~G_ = add-cauchy-approximation-Metric-Ab G
          _+∙G_ = add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
        in
          equational-reasoning
            (in-approx-G x +∙G in-approx-G y) +∙G in-approx-G z
            ＝ in-approx-G (x +~G y) +∙G in-approx-G z
              by
                ap-binary
                  ( _+∙G_)
                  ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                    ( G)
                    ( x)
                    ( y))
                  ( refl)
            ＝ in-approx-G ((x +~G y) +~G z)
              by
                add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                  ( G)
                  ( x +~G y)
                  ( z)
            ＝ in-approx-G (x +~G (y +~G z))
              by
                apply-effectiveness-quotient-map'
                  ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab
                    ( G))
                  ( sim-associative-add-cauchy-approximation-Metric-Ab G x y z)
            ＝ in-approx-G x +∙G in-approx-G (y +~G z)
              by
                inv
                  ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                    ( G)
                    ( x)
                    ( y +~G z))
            ＝ in-approx-G x +∙G (in-approx-G y +∙G in-approx-G z)
              by
                ap-binary
                  ( _+∙G_)
                  ( refl)
                  ( inv
                    ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                      ( G)
                      ( y)
                      ( z))))
```

### Addition in the metric quotient of the Cauchy pseudocompletion is commutative

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  commutative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x y : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x y ＝
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y x
  commutative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    double-induction-set-quotient'
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( λ x y →
        Id-Prop
          ( set-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x y)
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G y x))
      ( λ x y →
        let
          in-approx-G =
            in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          _+~G_ = add-cauchy-approximation-Metric-Ab G
          _+∙G_ = add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
        in
          equational-reasoning
            in-approx-G x +∙G in-approx-G y
            ＝ in-approx-G (x +~G y)
              by
                add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                  ( G)
                  ( x)
                  ( y)
            ＝ in-approx-G (y +~G x)
              by
                ap
                  ( in-approx-G)
                  ( commutative-add-cauchy-approximation-Metric-Ab G x y)
            ＝ in-approx-G y +∙G in-approx-G x
              by
                inv
                  ( add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                    ( G)
                    ( y)
                    ( x)))
```

### Unit laws of addition in the metric quotient of the Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  left-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
      ( x) ＝
    x
  left-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    induction-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( λ x →
        Id-Prop
          ( set-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
            ( zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
            ( x))
          ( x))
      ( λ x →
        let
          in-approx-G =
            in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          _+~G_ = add-cauchy-approximation-Metric-Ab G
          _+∙G_ = add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          0-approx-G = zero-cauchy-approximation-Metric-Ab G
        in
          equational-reasoning
            in-approx-G 0-approx-G +∙G in-approx-G x
            ＝ in-approx-G (0-approx-G +~G x)
              by
                add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                  ( G)
                  ( 0-approx-G)
                  ( x)
            ＝ in-approx-G x
              by
                apply-effectiveness-quotient-map'
                  ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab
                    ( G))
                  ( sim-left-unit-law-add-cauchy-approximation-Metric-Ab G x))

  right-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( x)
      ( zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) ＝
    x
  right-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab x =
    commutative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G _ _ ∙
    left-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab x
```

### Negation in the metric quotient of the Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  hom-neg-cauchy-pseudocompletion-Metric-Ab :
    hom-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
  hom-neg-cauchy-pseudocompletion-Metric-Ab =
    ( neg-cauchy-approximation-Metric-Ab G ,
      preserves-sim-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( isometry-neg-cauchy-pseudocompletion-Metric-Ab G)
        ( _)
        ( _))

  neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G →
    type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    map-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( hom-neg-cauchy-pseudocompletion-Metric-Ab)

  abstract
    neg-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
      (x : cauchy-approximation-Metric-Ab G) →
      neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab
        ( in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
          ( G)
          ( x)) ＝
      in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
        ( G)
        ( neg-cauchy-approximation-Metric-Ab G x)
    neg-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
      coherence-square-map-set-quotient
        ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
        ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
        ( hom-neg-cauchy-pseudocompletion-Metric-Ab)
```

### Inverse laws of addition in the metric quotient of the Cauchy pseudocompletion

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract

  left-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x)
      ( x) ＝
    zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  left-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    induction-set-quotient
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( λ x →
        Id-Prop
          ( set-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
          ( add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
            ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x)
            ( x))
          ( zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G))
      ( λ x →
        let
          in-approx-G =
            in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          _+~G_ = add-cauchy-approximation-Metric-Ab G
          _+∙G_ = add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          neg-∙G = neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
          neg-G = neg-cauchy-approximation-Metric-Ab G
          0-approx-G = zero-cauchy-approximation-Metric-Ab G
        in
          equational-reasoning
            neg-∙G (in-approx-G x) +∙G in-approx-G x
            ＝ in-approx-G (neg-G x) +∙G in-approx-G x
              by
                ap-binary
                  ( _+∙G_)
                  ( neg-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                    ( G)
                    ( x))
                  ( refl)
            ＝ in-approx-G (neg-G x +~G x)
              by
                add-in-approximation-metric-quotient-cauchy-pseudocompletion-Metric-Ab
                  ( G)
                  ( neg-G x)
                  ( x)
            ＝ in-approx-G 0-approx-G
              by
                ap
                  ( in-approx-G)
                  ( left-inverse-law-add-cauchy-approximation-Metric-Ab G x))

  right-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    (x : type-metric-quotient-cauchy-pseudocompletion-Metric-Ab G) →
    add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
      ( x)
      ( neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G x) ＝
    zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G
  right-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab x =
    commutative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G _ _ ∙
    left-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab x
```

### The metric quotient of the Cauchy pseudocompletion forms an abelian group

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Semigroup (l1 ⊔ l2)
  semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( set-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      associative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)

  is-unital-semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    is-unital-Semigroup
      ( semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab)
  is-unital-semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( zero-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      left-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      right-unit-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)

  group-metric-quotient-cauchy-pseudocompletion-Metric-Ab :
    Group (l1 ⊔ l2)
  group-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab ,
      is-unital-semigroup-metric-quotient-cauchy-pseudocompletion-Metric-Ab ,
      neg-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      left-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G ,
      right-inverse-law-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)

  ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab : Ab (l1 ⊔ l2)
  ab-metric-quotient-cauchy-pseudocompletion-Metric-Ab =
    ( group-metric-quotient-cauchy-pseudocompletion-Metric-Ab ,
      commutative-add-metric-quotient-cauchy-pseudocompletion-Metric-Ab G)
```
