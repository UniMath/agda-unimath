# Normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.real-vector-spaces
open import linear-algebra.seminormed-real-vector-spaces

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.lipschitz-maps-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.metrics-of-metric-spaces
open import metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-nonnegative-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

A
{{#concept "norm" WDID=Q956437 WD="norm" Disambiguation="on a real vector space" Agda=norm-ℝ-Vector-Space}}
on a [real vector space](linear-algebra.real-vector-spaces.md) `V` is a
[seminorm](linear-algebra.seminormed-real-vector-spaces.md) `p` on `V` that is
**extensional**: if `p(v) = 0`, then `v` is the zero vector.

A real vector space equipped with such a norm is called a
{{#concept "normed vector space" Disambiguation="normed real vector space" WDID=Q726210 WD="normed vector space" Agda=Normed-ℝ-Vector-Space}}.

A norm on a real vector space induces a
[located](metric-spaces.located-metric-spaces.md)
[metric space](metric-spaces.metric-spaces.md) on the vector space, defined by
the neighborhood relation that `v` and `w` are in an `ε`-neighborhood of each
other if `p(v - w) ≤ ε`.

## Definition

```agda
module _
  {l1 l2 : Level} (V : ℝ-Vector-Space l1 l2) (p : seminorm-ℝ-Vector-Space V)
  where

  is-norm-prop-seminorm-ℝ-Vector-Space : Prop (l1 ⊔ l2)
  is-norm-prop-seminorm-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ v →
        hom-Prop
          ( is-zero-prop-ℝ (pr1 p v))
          ( is-zero-prop-ℝ-Vector-Space V v))

  is-norm-seminorm-ℝ-Vector-Space : UU (l1 ⊔ l2)
  is-norm-seminorm-ℝ-Vector-Space =
    type-Prop is-norm-prop-seminorm-ℝ-Vector-Space

norm-ℝ-Vector-Space : {l1 l2 : Level} → ℝ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
norm-ℝ-Vector-Space V = type-subtype (is-norm-prop-seminorm-ℝ-Vector-Space V)

Normed-ℝ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Normed-ℝ-Vector-Space l1 l2 = Σ (ℝ-Vector-Space l1 l2) norm-ℝ-Vector-Space
```

## Properties

```agda
module _
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2)
  where

  vector-space-Normed-ℝ-Vector-Space : ℝ-Vector-Space l1 l2
  vector-space-Normed-ℝ-Vector-Space = pr1 V

  ab-Normed-ℝ-Vector-Space : Ab l2
  ab-Normed-ℝ-Vector-Space =
    ab-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  norm-Normed-ℝ-Vector-Space :
    norm-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space
  norm-Normed-ℝ-Vector-Space = pr2 V

  seminorm-Normed-ℝ-Vector-Space :
    seminorm-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space
  seminorm-Normed-ℝ-Vector-Space = pr1 norm-Normed-ℝ-Vector-Space

  seminormed-vector-space-Normed-ℝ-Vector-Space :
    Seminormed-ℝ-Vector-Space l1 l2
  seminormed-vector-space-Normed-ℝ-Vector-Space =
    ( vector-space-Normed-ℝ-Vector-Space , seminorm-Normed-ℝ-Vector-Space)

  set-Normed-ℝ-Vector-Space : Set l2
  set-Normed-ℝ-Vector-Space =
    set-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  type-Normed-ℝ-Vector-Space : UU l2
  type-Normed-ℝ-Vector-Space =
    type-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space
```

### Properties inherited from the abelian group structure on addition

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (let ab-V = ab-Normed-ℝ-Vector-Space V)
  where

  add-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V →
    type-Normed-ℝ-Vector-Space V
  add-Normed-ℝ-Vector-Space = add-Ab ab-V

  diff-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V →
    type-Normed-ℝ-Vector-Space V
  diff-Normed-ℝ-Vector-Space = right-subtraction-Ab ab-V

  neg-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V
  neg-Normed-ℝ-Vector-Space = neg-Ab ab-V

  zero-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space V
  zero-Normed-ℝ-Vector-Space = zero-Ab ab-V

  is-zero-prop-Normed-ℝ-Vector-Space : subtype l2 (type-Normed-ℝ-Vector-Space V)
  is-zero-prop-Normed-ℝ-Vector-Space = is-zero-prop-Ab ab-V

  is-zero-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space V → UU l2
  is-zero-Normed-ℝ-Vector-Space = is-zero-Ab ab-V

  abstract
    associative-add-Normed-ℝ-Vector-Space :
      (u v w : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space
        ( add-Normed-ℝ-Vector-Space u v)
        ( w) ＝
      add-Normed-ℝ-Vector-Space
        ( u)
        ( add-Normed-ℝ-Vector-Space v w)
    associative-add-Normed-ℝ-Vector-Space = associative-add-Ab ab-V

    left-unit-law-add-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space zero-Normed-ℝ-Vector-Space v ＝ v
    left-unit-law-add-Normed-ℝ-Vector-Space = left-unit-law-add-Ab ab-V

    right-unit-law-add-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space v zero-Normed-ℝ-Vector-Space ＝ v
    right-unit-law-add-Normed-ℝ-Vector-Space = right-unit-law-add-Ab ab-V

    left-inverse-law-add-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space (neg-Normed-ℝ-Vector-Space v) v ＝
      zero-Normed-ℝ-Vector-Space
    left-inverse-law-add-Normed-ℝ-Vector-Space =
      left-inverse-law-add-Ab ab-V

    right-inverse-law-add-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      diff-Normed-ℝ-Vector-Space v v ＝ zero-Normed-ℝ-Vector-Space
    right-inverse-law-add-Normed-ℝ-Vector-Space =
      right-inverse-law-add-Ab ab-V

    commutative-add-Normed-ℝ-Vector-Space :
      (u v : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space u v ＝ add-Normed-ℝ-Vector-Space v u
    commutative-add-Normed-ℝ-Vector-Space = commutative-add-Ab ab-V

    neg-neg-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      neg-Normed-ℝ-Vector-Space (neg-Normed-ℝ-Vector-Space v) ＝ v
    neg-neg-Normed-ℝ-Vector-Space = neg-neg-Ab ab-V

    distributive-neg-add-Normed-ℝ-Vector-Space :
      (v w : type-Normed-ℝ-Vector-Space V) →
      neg-Normed-ℝ-Vector-Space (add-Normed-ℝ-Vector-Space v w) ＝
      add-Normed-ℝ-Vector-Space
        ( neg-Normed-ℝ-Vector-Space v)
        ( neg-Normed-ℝ-Vector-Space w)
    distributive-neg-add-Normed-ℝ-Vector-Space = distributive-neg-add-Ab ab-V

    interchange-add-add-Normed-ℝ-Vector-Space :
      (u v w x : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space
        ( add-Normed-ℝ-Vector-Space u v)
        ( add-Normed-ℝ-Vector-Space w x) ＝
      add-Normed-ℝ-Vector-Space
        ( add-Normed-ℝ-Vector-Space u w)
        ( add-Normed-ℝ-Vector-Space v x)
    interchange-add-add-Normed-ℝ-Vector-Space =
      interchange-add-add-Ab ab-V

    eq-is-zero-diff-Normed-ℝ-Vector-Space :
      {u v : type-Normed-ℝ-Vector-Space V} →
      is-zero-Normed-ℝ-Vector-Space (diff-Normed-ℝ-Vector-Space u v) →
      u ＝ v
    eq-is-zero-diff-Normed-ℝ-Vector-Space =
      eq-is-zero-right-subtraction-Ab ab-V

    interchange-add-diff-Normed-ℝ-Vector-Space :
      (x y z w : type-Normed-ℝ-Vector-Space V) →
      diff-Normed-ℝ-Vector-Space
        ( add-Normed-ℝ-Vector-Space x y)
        ( add-Normed-ℝ-Vector-Space z w) ＝
      add-Normed-ℝ-Vector-Space
        ( diff-Normed-ℝ-Vector-Space x z)
        ( diff-Normed-ℝ-Vector-Space y w)
    interchange-add-diff-Normed-ℝ-Vector-Space =
      interchange-add-right-subtraction-Ab ab-V

    right-swap-add-Normed-ℝ-Vector-Space :
      (x y z : type-Normed-ℝ-Vector-Space V) →
      add-Normed-ℝ-Vector-Space (add-Normed-ℝ-Vector-Space x y) z ＝
      add-Normed-ℝ-Vector-Space (add-Normed-ℝ-Vector-Space x z) y
    right-swap-add-Normed-ℝ-Vector-Space = right-swap-add-Ab ab-V
```

### Properties inherited from the vector space structure

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (let vector-space-V = vector-space-Normed-ℝ-Vector-Space V)
  where

  mul-Normed-ℝ-Vector-Space :
    ℝ l1 → type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V
  mul-Normed-ℝ-Vector-Space = mul-ℝ-Vector-Space vector-space-V

  abstract
    left-distributive-mul-add-Normed-ℝ-Vector-Space :
      (c : ℝ l1) (v w : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space c (add-Normed-ℝ-Vector-Space V v w) ＝
      add-Normed-ℝ-Vector-Space V
        ( mul-Normed-ℝ-Vector-Space c v)
        ( mul-Normed-ℝ-Vector-Space c w)
    left-distributive-mul-add-Normed-ℝ-Vector-Space =
      left-distributive-mul-add-ℝ-Vector-Space vector-space-V

    left-distributive-mul-diff-Normed-ℝ-Vector-Space :
      (c : ℝ l1) (v w : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space c (diff-Normed-ℝ-Vector-Space V v w) ＝
      diff-Normed-ℝ-Vector-Space V
        ( mul-Normed-ℝ-Vector-Space c v)
        ( mul-Normed-ℝ-Vector-Space c w)
    left-distributive-mul-diff-Normed-ℝ-Vector-Space =
      left-distributive-mul-diff-ℝ-Vector-Space vector-space-V

    right-distributive-mul-add-Normed-ℝ-Vector-Space :
      (c d : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space (c +ℝ d) v ＝
      add-Normed-ℝ-Vector-Space V
        ( mul-Normed-ℝ-Vector-Space c v)
        ( mul-Normed-ℝ-Vector-Space d v)
    right-distributive-mul-add-Normed-ℝ-Vector-Space =
      right-distributive-mul-add-ℝ-Vector-Space vector-space-V

    right-distributive-mul-diff-Normed-ℝ-Vector-Space :
      (c d : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space (c -ℝ d) v ＝
      diff-Normed-ℝ-Vector-Space V
        ( mul-Normed-ℝ-Vector-Space c v)
        ( mul-Normed-ℝ-Vector-Space d v)
    right-distributive-mul-diff-Normed-ℝ-Vector-Space =
      right-distributive-mul-diff-ℝ-Vector-Space vector-space-V

    associative-mul-Normed-ℝ-Vector-Space :
      (c d : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space (c *ℝ d) v ＝
      mul-Normed-ℝ-Vector-Space c (mul-Normed-ℝ-Vector-Space d v)
    associative-mul-Normed-ℝ-Vector-Space =
      associative-mul-ℝ-Vector-Space vector-space-V

    left-unit-law-mul-Normed-ℝ-Vector-Space :
      (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space (raise-one-ℝ l1) v ＝ v
    left-unit-law-mul-Normed-ℝ-Vector-Space =
      left-unit-law-mul-ℝ-Vector-Space vector-space-V

    left-negative-law-mul-Normed-ℝ-Vector-Space :
      (c : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space (neg-ℝ c) v ＝
      neg-Normed-ℝ-Vector-Space V (mul-Normed-ℝ-Vector-Space c v)
    left-negative-law-mul-Normed-ℝ-Vector-Space =
      left-negative-law-mul-ℝ-Vector-Space vector-space-V

    right-zero-law-mul-Normed-ℝ-Vector-Space :
      (c : ℝ l1) →
      mul-Normed-ℝ-Vector-Space c (zero-Normed-ℝ-Vector-Space V) ＝
      zero-Normed-ℝ-Vector-Space V
    right-zero-law-mul-Normed-ℝ-Vector-Space =
      right-zero-law-mul-ℝ-Vector-Space vector-space-V

    left-swap-mul-Normed-ℝ-Vector-Space :
      (c d : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
      mul-Normed-ℝ-Vector-Space c (mul-Normed-ℝ-Vector-Space d v) ＝
      mul-Normed-ℝ-Vector-Space d (mul-Normed-ℝ-Vector-Space c v)
    left-swap-mul-Normed-ℝ-Vector-Space =
      left-swap-mul-ℝ-Vector-Space vector-space-V
```

### Norms and distances in a normed vector space

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (let seminormed-V = seminormed-vector-space-Normed-ℝ-Vector-Space V)
  where

  map-norm-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space V → ℝ l1
  map-norm-Normed-ℝ-Vector-Space = pr1 (pr1 (norm-Normed-ℝ-Vector-Space V))

  nonnegative-norm-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-norm-Normed-ℝ-Vector-Space =
    nonnegative-seminorm-Seminormed-ℝ-Vector-Space seminormed-V

  dist-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V → ℝ l1
  dist-Normed-ℝ-Vector-Space = dist-Seminormed-ℝ-Vector-Space seminormed-V

  nonnegative-dist-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space V → type-Normed-ℝ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-dist-Normed-ℝ-Vector-Space =
    nonnegative-dist-Seminormed-ℝ-Vector-Space seminormed-V

  is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space :
    (c : ℝ l1) (v : type-Normed-ℝ-Vector-Space V) →
    map-norm-Normed-ℝ-Vector-Space (mul-Normed-ℝ-Vector-Space V c v) ＝
    abs-ℝ c *ℝ map-norm-Normed-ℝ-Vector-Space v
  is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space =
    is-absolutely-homogeneous-seminorm-Seminormed-ℝ-Vector-Space seminormed-V

  right-zero-law-dist-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space V) →
    dist-Normed-ℝ-Vector-Space v (zero-Normed-ℝ-Vector-Space V) ＝
    map-norm-Normed-ℝ-Vector-Space v
  right-zero-law-dist-Normed-ℝ-Vector-Space =
    right-zero-law-dist-Seminormed-ℝ-Vector-Space seminormed-V
```

### The distance function in a normed vector space satisfies the properties of a metric

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  is-extensional-norm-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space V) →
    is-zero-ℝ (map-norm-Normed-ℝ-Vector-Space V v) →
    v ＝ zero-Normed-ℝ-Vector-Space V
  is-extensional-norm-Normed-ℝ-Vector-Space = pr2 (norm-Normed-ℝ-Vector-Space V)

  is-extensional-dist-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space V) →
    is-zero-ℝ (dist-Normed-ℝ-Vector-Space V v w) →
    v ＝ w
  is-extensional-dist-Normed-ℝ-Vector-Space v w |v-w|=0 =
    eq-is-zero-diff-Normed-ℝ-Vector-Space V
      ( is-extensional-norm-Normed-ℝ-Vector-Space
        ( diff-Normed-ℝ-Vector-Space V v w)
        ( |v-w|=0))

  refl-dist-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space V) →
    is-zero-ℝ (dist-Normed-ℝ-Vector-Space V v v)
  refl-dist-Normed-ℝ-Vector-Space =
    is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space V)

  symmetric-dist-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space V) →
    dist-Normed-ℝ-Vector-Space V v w ＝ dist-Normed-ℝ-Vector-Space V w v
  symmetric-dist-Normed-ℝ-Vector-Space =
    symmetric-dist-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space V)

  triangular-norm-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space V) →
    leq-ℝ
      ( map-norm-Normed-ℝ-Vector-Space V (add-Normed-ℝ-Vector-Space V v w))
      ( map-norm-Normed-ℝ-Vector-Space V v +ℝ
        map-norm-Normed-ℝ-Vector-Space V w)
  triangular-norm-Normed-ℝ-Vector-Space =
    triangular-seminorm-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space V)

  triangular-dist-Normed-ℝ-Vector-Space :
    (u v w : type-Normed-ℝ-Vector-Space V) →
    leq-ℝ
      ( dist-Normed-ℝ-Vector-Space V u w)
      ( dist-Normed-ℝ-Vector-Space V u v +ℝ dist-Normed-ℝ-Vector-Space V v w)
  triangular-dist-Normed-ℝ-Vector-Space =
    triangular-dist-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space V)

  is-metric-dist-Normed-ℝ-Vector-Space :
    is-metric-distance-function
      ( set-Normed-ℝ-Vector-Space V)
      ( nonnegative-dist-Normed-ℝ-Vector-Space V)
  is-metric-dist-Normed-ℝ-Vector-Space =
    ( refl-dist-Normed-ℝ-Vector-Space ,
      ( λ v w → eq-ℝ⁰⁺ _ _ (symmetric-dist-Normed-ℝ-Vector-Space v w)) ,
      triangular-dist-Normed-ℝ-Vector-Space ,
      is-extensional-dist-Normed-ℝ-Vector-Space)
```

### The metric space of a normed vector space

```agda
module _
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2)
  where

  metric-Normed-ℝ-Vector-Space : Metric l1 (set-Normed-ℝ-Vector-Space V)
  metric-Normed-ℝ-Vector-Space =
    ( nonnegative-dist-Normed-ℝ-Vector-Space V ,
      is-metric-dist-Normed-ℝ-Vector-Space V)

  metric-space-Normed-ℝ-Vector-Space : Metric-Space l2 l1
  metric-space-Normed-ℝ-Vector-Space =
    metric-space-Metric
      ( set-Normed-ℝ-Vector-Space V)
      ( metric-Normed-ℝ-Vector-Space)

  located-metric-space-Normed-ℝ-Vector-Space : Located-Metric-Space l2 l1
  located-metric-space-Normed-ℝ-Vector-Space =
    located-metric-space-Metric
      ( set-Normed-ℝ-Vector-Space V)
      ( metric-Normed-ℝ-Vector-Space)

  neighborhood-prop-Normed-ℝ-Vector-Space :
    Rational-Neighborhood-Relation l1 (type-Normed-ℝ-Vector-Space V)
  neighborhood-prop-Normed-ℝ-Vector-Space =
    neighborhood-prop-Metric-Space metric-space-Normed-ℝ-Vector-Space

  neighborhood-Normed-ℝ-Vector-Space :
    ℚ⁺ → Relation l1 (type-Normed-ℝ-Vector-Space V)
  neighborhood-Normed-ℝ-Vector-Space =
    neighborhood-Metric-Space metric-space-Normed-ℝ-Vector-Space
```

### Negation is an isometry in the metric space of a normed vector space

```agda
module _
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  dist-neg-Normed-ℝ-Vector-Space :
    (x y : type-Normed-ℝ-Vector-Space V) →
    dist-Normed-ℝ-Vector-Space V
      ( neg-Normed-ℝ-Vector-Space V x)
      ( neg-Normed-ℝ-Vector-Space V y) ＝
    dist-Normed-ℝ-Vector-Space V x y
  dist-neg-Normed-ℝ-Vector-Space x y =
    equational-reasoning
      dist-Normed-ℝ-Vector-Space V
        ( neg-Normed-ℝ-Vector-Space V x)
        ( neg-Normed-ℝ-Vector-Space V y)
      ＝ dist-Normed-ℝ-Vector-Space V y x
        by
          ap
            ( map-norm-Normed-ℝ-Vector-Space V)
            ( right-subtraction-neg-Ab
              ( ab-Normed-ℝ-Vector-Space V)
              ( _)
              ( _))
      ＝ dist-Normed-ℝ-Vector-Space V x y
        by symmetric-dist-Normed-ℝ-Vector-Space V y x

  is-isometry-neg-Normed-ℝ-Vector-Space :
    is-isometry-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( neg-Normed-ℝ-Vector-Space V)
  is-isometry-neg-Normed-ℝ-Vector-Space =
    is-isometry-sim-metric-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( nonnegative-dist-Normed-ℝ-Vector-Space V)
      ( nonnegative-dist-Normed-ℝ-Vector-Space V)
      ( is-metric-metric-space-Metric
        ( set-Normed-ℝ-Vector-Space V)
        ( metric-Normed-ℝ-Vector-Space V))
      ( is-metric-metric-space-Metric
        ( set-Normed-ℝ-Vector-Space V)
        ( metric-Normed-ℝ-Vector-Space V))
      ( neg-Normed-ℝ-Vector-Space V)
      ( λ x y → sim-eq-ℝ (inv (dist-neg-Normed-ℝ-Vector-Space x y)))
```

### Left addition is an isometry in the metric space of a normed vector space

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (u : type-Normed-ℝ-Vector-Space V)
  where abstract

  dist-left-add-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space V) →
    dist-Normed-ℝ-Vector-Space
      ( V)
      ( add-Normed-ℝ-Vector-Space V u v)
      ( add-Normed-ℝ-Vector-Space V u w) ＝
    dist-Normed-ℝ-Vector-Space V v w
  dist-left-add-Normed-ℝ-Vector-Space v w =
    ap
      ( map-norm-Normed-ℝ-Vector-Space V)
      ( right-subtraction-left-add-Ab (ab-Normed-ℝ-Vector-Space V) u v w)

  is-isometry-left-add-Normed-ℝ-Vector-Space :
    is-isometry-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( add-Normed-ℝ-Vector-Space V u)
  is-isometry-left-add-Normed-ℝ-Vector-Space =
    is-isometry-sim-metric-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( nonnegative-dist-Normed-ℝ-Vector-Space V)
      ( nonnegative-dist-Normed-ℝ-Vector-Space V)
      ( is-metric-metric-space-Metric
        ( set-Normed-ℝ-Vector-Space V)
        ( metric-Normed-ℝ-Vector-Space V))
      ( is-metric-metric-space-Metric
        ( set-Normed-ℝ-Vector-Space V)
        ( metric-Normed-ℝ-Vector-Space V))
      ( add-Normed-ℝ-Vector-Space V u)
      ( λ v w → sim-eq-ℝ (inv (dist-left-add-Normed-ℝ-Vector-Space v w)))
```

### Right addition is an isometry in the metric space of a normed vector space

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (u : type-Normed-ℝ-Vector-Space V)
  where abstract

  dist-right-add-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space V) →
    dist-Normed-ℝ-Vector-Space
      ( V)
      ( add-Normed-ℝ-Vector-Space V v u)
      ( add-Normed-ℝ-Vector-Space V w u) ＝
    dist-Normed-ℝ-Vector-Space V v w
  dist-right-add-Normed-ℝ-Vector-Space v w =
    ( ap-binary
      ( dist-Normed-ℝ-Vector-Space V)
      ( commutative-add-Normed-ℝ-Vector-Space V v u)
      ( commutative-add-Normed-ℝ-Vector-Space V w u)) ∙
    ( dist-left-add-Normed-ℝ-Vector-Space V u v w)
```

### The norm of the zero vector is zero

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  norm-zero-Normed-ℝ-Vector-Space :
    map-norm-Normed-ℝ-Vector-Space V (zero-Normed-ℝ-Vector-Space V) ＝
    raise-zero-ℝ l1
  norm-zero-Normed-ℝ-Vector-Space =
    seminorm-zero-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space V)
```

### The distance between `cv` and `cw` is `|c|` times the distance between `v` and `w`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (c : ℝ l1)
  (v w : type-Normed-ℝ-Vector-Space V)
  where abstract

  multiplicative-dist-Normed-ℝ-Vector-Space :
    dist-Normed-ℝ-Vector-Space V
      ( mul-Normed-ℝ-Vector-Space V c v)
      ( mul-Normed-ℝ-Vector-Space V c w) ＝
    abs-ℝ c *ℝ dist-Normed-ℝ-Vector-Space V v w
  multiplicative-dist-Normed-ℝ-Vector-Space =
    ( ap
      ( map-norm-Normed-ℝ-Vector-Space V)
      ( inv (left-distributive-mul-diff-Normed-ℝ-Vector-Space V c v w))) ∙
    ( is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space V c _)
```

### The real numbers are a normed vector space over themselves with norm `x ↦ |x|`

```agda
normed-real-vector-space-ℝ :
  (l : Level) → Normed-ℝ-Vector-Space l (lsuc l)
normed-real-vector-space-ℝ l =
  ( real-vector-space-ℝ l ,
    ( abs-ℝ , triangle-inequality-abs-ℝ , abs-mul-ℝ) ,
    λ x |x|~0 → eq-raise-zero-is-zero-ℝ (is-zero-is-zero-abs-ℝ x |x|~0))

abstract
  eq-metric-space-normed-real-vector-space-metric-space-ℝ :
    (l : Level) →
    metric-space-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l) ＝
    metric-space-ℝ l
  eq-metric-space-normed-real-vector-space-metric-space-ℝ l =
    eq-isometric-eq-Metric-Space _ _
      ( refl , λ d x y → inv-iff (neighborhood-iff-leq-dist-ℝ d x y))
```

### The distance between `cx` and `cy` is `abs-ℝ c` times the distance between `x` and `y`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where abstract

  left-distributive-abs-mul-dist-Normed-ℝ-Vector-Space :
    (c : ℝ l1) (x y : type-Normed-ℝ-Vector-Space V) →
    abs-ℝ c *ℝ dist-Normed-ℝ-Vector-Space V x y ＝
    dist-Normed-ℝ-Vector-Space V
      ( mul-Normed-ℝ-Vector-Space V c x)
      ( mul-Normed-ℝ-Vector-Space V c y)
  left-distributive-abs-mul-dist-Normed-ℝ-Vector-Space c x y =
    ( inv (is-absolutely-homogeneous-norm-Normed-ℝ-Vector-Space V c _)) ∙
    ( ap
      ( map-norm-Normed-ℝ-Vector-Space V)
      ( left-distributive-mul-diff-Normed-ℝ-Vector-Space V c x y))
```

### The distance function is a uniformly continuous map from the product metric space to the nonnegative real numbers

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    is-uniformly-continuous-map-nonnegative-dist-Normed-ℝ-Vector-Space :
      is-uniformly-continuous-map-Metric-Space
        ( product-Metric-Space
          ( metric-space-Normed-ℝ-Vector-Space V)
          ( metric-space-Normed-ℝ-Vector-Space V))
        ( metric-space-ℝ⁰⁺ l1)
        ( ind-Σ (nonnegative-dist-Normed-ℝ-Vector-Space V))
    is-uniformly-continuous-map-nonnegative-dist-Normed-ℝ-Vector-Space =
      is-uniformly-continuous-map-metric-of-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( nonnegative-dist-Normed-ℝ-Vector-Space V)
        ( is-metric-metric-space-Metric
          ( set-Normed-ℝ-Vector-Space V)
          ( metric-Normed-ℝ-Vector-Space V))

    is-uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-Normed-ℝ-Vector-Space V)
        ( metric-space-ℝ⁰⁺ l1)
        ( nonnegative-norm-Normed-ℝ-Vector-Space V)
    is-uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space =
      tr
        ( is-uniformly-continuous-map-Metric-Space
          ( metric-space-Normed-ℝ-Vector-Space V)
          ( metric-space-ℝ⁰⁺ l1))
        ( eq-htpy
          ( λ v → eq-ℝ⁰⁺ _ _ (right-zero-law-dist-Normed-ℝ-Vector-Space V v)))
        ( is-uniformly-continuous-map-comp-Metric-Space
          ( metric-space-Normed-ℝ-Vector-Space V)
          ( product-Metric-Space
            ( metric-space-Normed-ℝ-Vector-Space V)
            ( metric-space-Normed-ℝ-Vector-Space V))
          ( metric-space-ℝ⁰⁺ l1)
          ( ind-Σ (nonnegative-dist-Normed-ℝ-Vector-Space V))
          ( _, zero-Normed-ℝ-Vector-Space V)
          ( is-uniformly-continuous-map-nonnegative-dist-Normed-ℝ-Vector-Space)
          ( is-uniformly-continuous-map-is-isometry-Metric-Space
            ( metric-space-Normed-ℝ-Vector-Space V)
            ( product-Metric-Space
              ( metric-space-Normed-ℝ-Vector-Space V)
              ( metric-space-Normed-ℝ-Vector-Space V))
            ( _, zero-Normed-ℝ-Vector-Space V)
            ( is-isometry-right-pair-Metric-Space
              ( metric-space-Normed-ℝ-Vector-Space V)
              ( metric-space-Normed-ℝ-Vector-Space V)
              ( zero-Normed-ℝ-Vector-Space V))))

  uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-ℝ⁰⁺ l1)
  uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space =
    ( nonnegative-norm-Normed-ℝ-Vector-Space V ,
      is-uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space)

  uniformly-continuous-map-norm-Normed-ℝ-Vector-Space :
    uniformly-continuous-map-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-ℝ l1)
  uniformly-continuous-map-norm-Normed-ℝ-Vector-Space =
    comp-uniformly-continuous-map-Metric-Space
      ( metric-space-Normed-ℝ-Vector-Space V)
      ( metric-space-ℝ⁰⁺ l1)
      ( metric-space-ℝ l1)
      ( uniformly-continuous-inclusion-subspace-Metric-Space
        ( metric-space-ℝ l1)
        ( is-nonnegative-prop-ℝ))
      ( uniformly-continuous-map-nonnegative-norm-Normed-ℝ-Vector-Space)
```

### For any `x y : V`, `∥x∥ ≤ ∥y∥ + ∥x - y∥`

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (x y : type-Normed-ℝ-Vector-Space V)
  (let _+V_ = add-Normed-ℝ-Vector-Space V)
  (let _-V_ = diff-Normed-ℝ-Vector-Space V)
  where abstract

  open inequality-reasoning-Large-Poset ℝ-Large-Poset

  leq-norm-add-norm-dist-Normed-ℝ-Vector-Space :
    leq-ℝ
      ( map-norm-Normed-ℝ-Vector-Space V x)
      ( map-norm-Normed-ℝ-Vector-Space V y +ℝ
        dist-Normed-ℝ-Vector-Space V x y)
  leq-norm-add-norm-dist-Normed-ℝ-Vector-Space =
    chain-of-inequalities
      map-norm-Normed-ℝ-Vector-Space V x
      ≤ map-norm-Normed-ℝ-Vector-Space V (y +V (x -V y))
        by
          leq-eq-ℝ
            ( ap
              ( map-norm-Normed-ℝ-Vector-Space V)
              ( inv
                ( is-identity-right-conjugation-Ab
                  ( ab-Normed-ℝ-Vector-Space V)
                  ( y)
                  ( x))))
      ≤ map-norm-Normed-ℝ-Vector-Space V y +ℝ
        dist-Normed-ℝ-Vector-Space V x y
        by triangular-norm-Normed-ℝ-Vector-Space V _ _
```

## See also

- [Real Banach spaces](functional-analysis.real-banach-spaces.md), normed real
  vector spaces for which the induced metric space is
  [complete](metric-spaces.complete-metric-spaces.md)

## External links

- [Normed vector space](https://en.wikipedia.org/wiki/Normed_vector_space) on
  Wikipedia
