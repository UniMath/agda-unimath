# Unit linear interpolation of proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.unit-linear-interpolation-proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.uniform-homeomorphisms-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import real-numbers.addition-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.isometry-difference-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-endomaps-real-numbers
open import real-numbers.subsets-real-numbers
open import real-numbers.uniformly-continuous-endomaps-real-numbers
open import real-numbers.unit-closed-interval-real-numbers
```

</details>

## Idea

The
{{#concept "unit linear interpolation" Disambiguation="of a proper closed interval of real numbers" WD="linear interpolation" WDID=Q2266329 Agda=real-map-unit-linear-interpolation-proper-closed-interval-ℝ}}
w.r.t. a
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` is the map `ℝ → ℝ` defined by

```text
  t ↦ (b - a) * t + a.
```

It is [invertible](foundation.equivalences.md) with inverse

```text
  x ↦ (x - a)/(b - a).
```

The linear interpolation map and its inverse are
[lipschitz maps](metric-spaces.lipschitz-maps-metric-spaces.md), preserve
[strict inequality](real-numbers.strict-inequality-real-numbers.md) and induce
an equivalence `[0,1] ≃ [a,b]`.

## Definitions

### Unit linear interpolation of a proper closed interval of real numbers

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  ([a,b]@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where

  real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    ℝ l → ℝ (l1 ⊔ l2 ⊔ l)
  real-map-unit-linear-interpolation-proper-closed-interval-ℝ x =
    (b -ℝ a) *ℝ x +ℝ a
```

### Inverse unit linear interpolation of a proper closed interval of real numbers

```agda
  real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    ℝ l → ℝ (l1 ⊔ l2 ⊔ l)
  real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ x =
    real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (x -ℝ a)
```

## Properties

### The unit linear interpolation is invertible

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where abstract

  is-section-real-map-inv-unit-interpolation-proper-closed-interval-ℝ :
    is-section
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
  is-section-real-map-inv-unit-interpolation-proper-closed-interval-ℝ x =
    ( ap-add-ℝ
      ( eq-sim-ℝ
        ( cancel-left-mul-div-ℝ⁺ (positive-diff-le-ℝ a<b) (x -ℝ a)))
      ( refl)) ∙
    ( eq-sim-ℝ (cancel-right-diff-add-ℝ x a))

  is-retraction-real-map-inv-unit-interpolation-proper-closed-interval-ℝ :
    is-retraction
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
  is-retraction-real-map-inv-unit-interpolation-proper-closed-interval-ℝ x =
    ( ap-mul-ℝ
      ( refl)
      ( eq-sim-ℝ (cancel-right-add-diff-ℝ ((b -ℝ a) *ℝ x) a))) ∙
    ( eq-sim-ℝ (cancel-left-div-mul-ℝ⁺ (positive-diff-le-ℝ a<b) x))

  is-equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-equiv
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
  is-equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    is-equiv-is-invertible
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1 ⊔ l2 ⊔ l)
        ( I))
      ( is-section-real-map-inv-unit-interpolation-proper-closed-interval-ℝ)
      ( is-retraction-real-map-inv-unit-interpolation-proper-closed-interval-ℝ)
```

### The real equivalence induced by linear interpolation

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I : proper-closed-interval-ℝ l1 l2)
  where

  equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    ℝ (l1 ⊔ l2 ⊔ l) ≃ ℝ (l1 ⊔ l2 ⊔ l)
  pr1 equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    real-map-unit-linear-interpolation-proper-closed-interval-ℝ
      ( l1 ⊔ l2 ⊔ l)
      ( I)
  pr2 equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    is-equiv-real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I
```

### The linear interpolation and its inverse are strictly increasing maps

```agda
module _
  {l1 l2 : Level}
  {l l' : Level}
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  (x : ℝ l)
  (x' : ℝ l')
  where abstract

  preserves-le-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    le-ℝ x x' →
    le-ℝ
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l' I x')
  preserves-le-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    preserves-le-right-add-ℝ a ((b -ℝ a) *ℝ x) ((b -ℝ a) *ℝ x') ∘
    preserves-le-left-mul-ℝ⁺ (positive-diff-le-ℝ a<b)

  preserves-le-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    le-ℝ x x' →
    le-ℝ
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l' I x')
  preserves-le-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ =
    preserves-le-left-mul-ℝ⁺ (inv-ℝ⁺ (positive-diff-le-ℝ a<b)) ∘
    preserves-le-right-add-ℝ (neg-ℝ a) x x'
```

### The linear interpolation and its inverse are increasing maps

```agda
module _
  {l1 l2 : Level}
  {l l' : Level}
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  (x : ℝ l)
  (x' : ℝ l')
  where abstract

  preserves-leq-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    leq-ℝ x x' →
    leq-ℝ
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l' I x')
  preserves-leq-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    preserves-leq-right-add-ℝ a ((b -ℝ a) *ℝ x) ((b -ℝ a) *ℝ x') ∘
    preserves-leq-left-mul-ℝ⁺ (positive-diff-le-ℝ a<b)

  preserves-leq-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    leq-ℝ x x' →
    leq-ℝ
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l' I x')
  preserves-leq-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ =
    preserves-leq-left-mul-ℝ⁺ (inv-ℝ⁺ (positive-diff-le-ℝ a<b)) ∘
    preserves-leq-right-add-ℝ (neg-ℝ a) x x'
```

### The linear interpolation and its inverse are Lipschitz continuous

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where abstract

  is-lipschitz-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-lipschitz-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I)
  is-lipschitz-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    is-lipschitz-map-comp-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l1 ⊔ l2 ⊔ l))
      ( metric-space-ℝ (l1 ⊔ l2 ⊔ l))
      ( λ x → x +ℝ a)
      ( mul-ℝ (b -ℝ a))
      ( is-lipschitz-is-isometry-Metric-Space
        ( metric-space-ℝ (l1 ⊔ l2 ⊔ l))
        ( metric-space-ℝ (l1 ⊔ l2 ⊔ l))
        ( λ x → x +ℝ a)
        ( is-isometry-right-add-ℝ a))
      ( is-lipschitz-map-right-mul-ℝ l (b -ℝ a))

  is-lipschitz-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-lipschitz-map-Metric-Space
      ( metric-space-ℝ l)
        ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I)
  is-lipschitz-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    is-lipschitz-map-comp-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l1 ⊔ l))
      ( metric-space-ℝ (l1 ⊔ l2 ⊔ l))
      ( λ x → real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ x)
      ( λ x → x -ℝ a)
      ( is-lipschitz-map-right-mul-ℝ
        ( l1 ⊔ l)
        ( real-inv-ℝ⁺ (positive-diff-le-ℝ a<b)))
      ( is-lipschitz-is-isometry-Metric-Space
        ( metric-space-ℝ l)
        ( metric-space-ℝ (l1 ⊔ l))
        ( λ x → x -ℝ a)
        ( is-isometry-right-add-ℝ (neg-ℝ a)))
```

### The linear interpolation and its inverse are uniformly continuous

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where abstract

  is-uniformly-continuous-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I)
  is-uniformly-continuous-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I)
      ( is-lipschitz-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I))

  is-uniformly-continuous-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-uniformly-continuous-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I)
  is-uniformly-continuous-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
      ( metric-space-ℝ l)
      ( metric-space-ℝ (l ⊔ l1 ⊔ l2))
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I)
      ( is-lipschitz-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I))
```

### The unit linear interpolation on `[a, b]` maps `0` to `a` and `1` to `b`

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where

  sim-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    sim-ℝ
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ _ I zero-ℝ)
      ( lower-bound-proper-closed-interval-ℝ I)
  sim-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    similarity-reasoning-ℝ
      (b -ℝ a) *ℝ zero-ℝ +ℝ a
      ~ℝ zero-ℝ +ℝ a
        by
          preserves-sim-right-add-ℝ
            ( a)
            ( (b -ℝ a) *ℝ zero-ℝ)
            ( zero-ℝ)
            ( right-zero-law-mul-ℝ (b -ℝ a))
      ~ℝ a
        by sim-eq-ℝ (left-unit-law-add-ℝ a)

  sim-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    sim-ℝ
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l1)
        ( I)
        ( a))
      ( zero-ℝ)
  sim-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    =
    similarity-reasoning-ℝ
      real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (a -ℝ a)
      ~ℝ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ zero-ℝ
        by
          preserves-sim-left-mul-ℝ
            (real-inv-ℝ⁺ (positive-diff-le-ℝ a<b))
            ( a -ℝ a)
            ( zero-ℝ)
            ( right-inverse-law-add-ℝ a)
      ~ℝ zero-ℝ
        by right-zero-law-mul-ℝ _

  sim-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    sim-ℝ
      ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ _ I one-ℝ)
      ( upper-bound-proper-closed-interval-ℝ I)
  sim-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    similarity-reasoning-ℝ
      (b -ℝ a) *ℝ one-ℝ +ℝ a
      ~ℝ (b -ℝ a) +ℝ a
        by
          preserves-sim-right-add-ℝ
            ( a)
            ( (b -ℝ a) *ℝ one-ℝ)
            ( b -ℝ a)
            ( sim-eq-ℝ (right-unit-law-mul-ℝ (b -ℝ a)))
      ~ℝ b
        by cancel-right-diff-add-ℝ b a

  sim-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    sim-ℝ
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l2)
        ( I)
        ( b))
      ( one-ℝ)
  sim-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    = left-inverse-law-mul-ℝ⁺ (positive-diff-le-ℝ a<b)
```

### The unit linear interpolation on `[a,b]` exchanges `[0,1]` and `[a,b]`

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where abstract

  preserves-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    (x : ℝ l) →
    leq-ℝ zero-ℝ x →
    leq-ℝ a (real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
  preserves-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
    x =
    preserves-leq-left-sim-ℝ
      ( sim-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)) ∘
    preserves-leq-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
      ( I)
      ( zero-ℝ)
      ( x)

  preserves-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    (x : ℝ l) →
    leq-ℝ a x →
    leq-ℝ
      ( zero-ℝ)
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
  preserves-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    x =
    preserves-leq-left-sim-ℝ
      ( sim-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)) ∘
    preserves-leq-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
      ( I)
      ( a)
      ( x)

  preserves-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    (x : ℝ l) →
    leq-ℝ x one-ℝ →
    leq-ℝ (real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I x) b
  preserves-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
    x =
    preserves-leq-right-sim-ℝ
      ( sim-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)) ∘
    preserves-leq-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
      ( I)
      ( x)
      ( one-ℝ)

  preserves-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    (x : ℝ l) →
    leq-ℝ x b →
    leq-ℝ
      ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I x)
      ( one-ℝ)
  preserves-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
    x =
    preserves-leq-right-sim-ℝ
      ( sim-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)) ∘
    preserves-leq-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
      ( I)
      ( x)
      ( b)
```

### The unit linear interpolation on `[a,b]` induces an equivalence `[0,1] ≃ [a,b]`

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where

  map-unit-linear-interpolation-proper-closed-interval-ℝ :
    type-unit-interval-ℝ l →
    type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I
  map-unit-linear-interpolation-proper-closed-interval-ℝ (x , lo , hi) =
    ( real-map-unit-linear-interpolation-proper-closed-interval-ℝ l I x ,
      preserves-lower-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)
        ( x)
        ( lo) ,
      preserves-upper-bound-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)
        ( x)
        ( hi))

  map-inv-unit-linear-interpolation-proper-closed-interval-ℝ :
    type-proper-closed-interval-ℝ l I →
    type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l)
  map-inv-unit-linear-interpolation-proper-closed-interval-ℝ (x , lo , hi) =
    ( real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ l I x ,
      preserves-lower-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)
        ( x)
        ( lo) ,
      preserves-upper-bound-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I)
        ( x)
        ( hi))

module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where

  is-equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    is-equiv
      ( map-unit-linear-interpolation-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
  is-equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    is-equiv-is-invertible
      ( map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
        (l1 ⊔ l2 ⊔ l)
        ( I))
      ( λ (x , _ , _) →
        eq-type-subtype
          ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
          ( is-section-real-map-inv-unit-interpolation-proper-closed-interval-ℝ
            ( l)
            ( I)
            ( x)))
      ( λ (x , _ , _) →
        eq-type-subtype
          ( subset-unit-interval-ℝ (l1 ⊔ l2 ⊔ l))
          ( is-retraction-real-map-inv-unit-interpolation-proper-closed-interval-ℝ
            ( l)
            ( I)
            ( x)))

  equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ :
    type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l) ≃
    type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I
  equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ =
    ( map-unit-linear-interpolation-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I ,
      is-equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ)
```

### The unit linear interpolation on `[a,b]` induces a uniform homemoorphism `[0,1] ≃ [a,b]`

```agda
module _
  {l1 l2 : Level}
  (l : Level)
  (I@(a , b , a<b) : proper-closed-interval-ℝ l1 l2)
  where

  uniform-homeo-unit-linear-interpolation-proper-closed-interval-ℝ :
    uniform-homeo-Metric-Space
      ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l))
      ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
  uniform-homeo-unit-linear-interpolation-proper-closed-interval-ℝ =
    ( map-unit-linear-interpolation-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I ,
      is-equiv-map-unit-linear-interpolation-proper-closed-interval-ℝ
        ( l)
        ( I) ,
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l))
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
        ( map-unit-linear-interpolation-proper-closed-interval-ℝ
          ( l1 ⊔ l2 ⊔ l)
          ( I))
        ( map-tot-exists
          ( λ k H δ (x , _ , _) (y , _ , _) → H δ x y)
          ( is-lipschitz-real-map-unit-linear-interpolation-proper-closed-interval-ℝ
            ( l1 ⊔ l2 ⊔ l)
            ( I))) ,
      is-uniformly-continuous-map-is-lipschitz-map-Metric-Space
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l) I)
        ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l))
        ( map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
          ( l1 ⊔ l2 ⊔ l)
          ( I))
        ( map-tot-exists
          ( λ k H δ (x , _ , _) (y , _ , _) → H δ x y)
          ( is-lipschitz-real-map-inv-unit-linear-interpolation-proper-closed-interval-ℝ
            ( l1 ⊔ l2 ⊔ l)
            ( I))))
```

## External links

- [Linear interpolation](https://en.wikipedia.org/wiki/Linear_interpolation) at
  Wikipedia
