# Normed real vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.normed-real-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
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

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.metrics-of-metric-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.distance-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
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

  is-norm-prop-seminorm-ℝ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-norm-prop-seminorm-ℝ-Vector-Space =
    Π-Prop
      ( type-ℝ-Vector-Space V)
      ( λ v →
        hom-Prop
          ( Id-Prop (ℝ-Set l1) (pr1 p v) (raise-ℝ l1 zero-ℝ))
          ( is-zero-prop-ℝ-Vector-Space V v))

  is-norm-seminorm-ℝ-Vector-Space : UU (lsuc l1 ⊔ l2)
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

  add-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space →
    type-Normed-ℝ-Vector-Space
  add-Normed-ℝ-Vector-Space =
    add-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  commutative-add-Normed-ℝ-Vector-Space :
    (u v : type-Normed-ℝ-Vector-Space) →
    add-Normed-ℝ-Vector-Space u v ＝ add-Normed-ℝ-Vector-Space v u
  commutative-add-Normed-ℝ-Vector-Space =
    commutative-add-Ab ab-Normed-ℝ-Vector-Space

  diff-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space →
    type-Normed-ℝ-Vector-Space
  diff-Normed-ℝ-Vector-Space =
    diff-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  neg-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space
  neg-Normed-ℝ-Vector-Space =
    neg-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  neg-neg-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space) →
    neg-Normed-ℝ-Vector-Space (neg-Normed-ℝ-Vector-Space v) ＝ v
  neg-neg-Normed-ℝ-Vector-Space =
    neg-neg-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  distributive-neg-add-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space) →
    neg-Normed-ℝ-Vector-Space (add-Normed-ℝ-Vector-Space v w) ＝
    add-Normed-ℝ-Vector-Space
      ( neg-Normed-ℝ-Vector-Space v)
      ( neg-Normed-ℝ-Vector-Space w)
  distributive-neg-add-Normed-ℝ-Vector-Space =
    distributive-neg-add-Ab ab-Normed-ℝ-Vector-Space

  interchange-add-add-Normed-ℝ-Vector-Space :
    (u v w x : type-Normed-ℝ-Vector-Space) →
    add-Normed-ℝ-Vector-Space
      ( add-Normed-ℝ-Vector-Space u v)
      ( add-Normed-ℝ-Vector-Space w x) ＝
    add-Normed-ℝ-Vector-Space
      ( add-Normed-ℝ-Vector-Space u w)
      ( add-Normed-ℝ-Vector-Space v x)
  interchange-add-add-Normed-ℝ-Vector-Space =
    interchange-add-add-Ab ab-Normed-ℝ-Vector-Space

  zero-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space
  zero-Normed-ℝ-Vector-Space =
    zero-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space

  left-unit-law-add-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space) →
    add-Normed-ℝ-Vector-Space zero-Normed-ℝ-Vector-Space v ＝ v
  left-unit-law-add-Normed-ℝ-Vector-Space =
    left-unit-law-add-Ab ab-Normed-ℝ-Vector-Space

  right-inverse-law-add-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space) →
    diff-Normed-ℝ-Vector-Space v v ＝ zero-Normed-ℝ-Vector-Space
  right-inverse-law-add-Normed-ℝ-Vector-Space =
    right-inverse-law-add-Ab ab-Normed-ℝ-Vector-Space

  map-norm-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space → ℝ l1
  map-norm-Normed-ℝ-Vector-Space = pr1 (pr1 norm-Normed-ℝ-Vector-Space)

  nonnegative-norm-Normed-ℝ-Vector-Space : type-Normed-ℝ-Vector-Space → ℝ⁰⁺ l1
  nonnegative-norm-Normed-ℝ-Vector-Space =
    nonnegative-seminorm-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space)

  dist-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space → ℝ l1
  dist-Normed-ℝ-Vector-Space =
    dist-Seminormed-ℝ-Vector-Space seminormed-vector-space-Normed-ℝ-Vector-Space

  nonnegative-dist-Normed-ℝ-Vector-Space :
    type-Normed-ℝ-Vector-Space → type-Normed-ℝ-Vector-Space → ℝ⁰⁺ l1
  nonnegative-dist-Normed-ℝ-Vector-Space =
    nonnegative-dist-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space)

  triangular-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space) →
    leq-ℝ
      ( map-norm-Normed-ℝ-Vector-Space (add-Normed-ℝ-Vector-Space v w))
      ( map-norm-Normed-ℝ-Vector-Space v +ℝ map-norm-Normed-ℝ-Vector-Space w)
  triangular-Normed-ℝ-Vector-Space =
    triangular-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space)

  is-extensional-norm-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space) →
    map-norm-Normed-ℝ-Vector-Space v ＝ raise-ℝ l1 zero-ℝ →
    v ＝ zero-Normed-ℝ-Vector-Space
  is-extensional-norm-Normed-ℝ-Vector-Space = pr2 norm-Normed-ℝ-Vector-Space

  is-extensional-dist-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space) →
    dist-Normed-ℝ-Vector-Space v w ＝ raise-ℝ l1 zero-ℝ →
    v ＝ w
  is-extensional-dist-Normed-ℝ-Vector-Space v w |v-w|=0 =
    eq-is-zero-right-subtraction-Ab
      ( ab-ℝ-Vector-Space vector-space-Normed-ℝ-Vector-Space)
      ( is-extensional-norm-Normed-ℝ-Vector-Space
        ( diff-Normed-ℝ-Vector-Space v w)
        ( |v-w|=0))

  commutative-dist-Normed-ℝ-Vector-Space :
    (v w : type-Normed-ℝ-Vector-Space) →
    dist-Normed-ℝ-Vector-Space v w ＝ dist-Normed-ℝ-Vector-Space w v
  commutative-dist-Normed-ℝ-Vector-Space =
    commutative-dist-Seminormed-ℝ-Vector-Space
      ( seminormed-vector-space-Normed-ℝ-Vector-Space)
```

### The metric space of a normed vector space

```agda
module _
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2)
  where

  refl-norm-Normed-ℝ-Vector-Space :
    (v : type-Normed-ℝ-Vector-Space V) →
    sim-ℝ zero-ℝ (dist-Normed-ℝ-Vector-Space V v v)
  refl-norm-Normed-ℝ-Vector-Space v =
    inv-tr
      ( sim-ℝ zero-ℝ)
      ( is-zero-diagonal-dist-Seminormed-ℝ-Vector-Space
        ( seminormed-vector-space-Normed-ℝ-Vector-Space V)
        ( v))
      ( sim-raise-ℝ l1 zero-ℝ)

  metric-Normed-ℝ-Vector-Space : Metric l1 (set-Normed-ℝ-Vector-Space V)
  metric-Normed-ℝ-Vector-Space =
    ( nonnegative-dist-Normed-ℝ-Vector-Space V ,
      refl-norm-Normed-ℝ-Vector-Space ,
      ( λ v w → eq-ℝ⁰⁺ _ _ (commutative-dist-Normed-ℝ-Vector-Space V v w)) ,
      triangular-dist-Seminormed-ℝ-Vector-Space
        ( seminormed-vector-space-Normed-ℝ-Vector-Space V) ,
      ( λ v w 0~dvw →
        is-extensional-dist-Normed-ℝ-Vector-Space V v w
          ( eq-sim-ℝ
            ( transitive-sim-ℝ _ _ _
              ( sim-raise-ℝ l1 zero-ℝ)
              ( symmetric-sim-ℝ 0~dvw)))))

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
```

## Properties

### The real numbers are a normed vector space over themselves with norm `x ↦ |x|`

```agda
normed-real-vector-space-ℝ :
  (l : Level) → Normed-ℝ-Vector-Space l (lsuc l)
normed-real-vector-space-ℝ l =
  ( real-vector-space-ℝ l ,
    ( abs-ℝ , triangle-inequality-abs-ℝ , abs-mul-ℝ) ,
    eq-raise-zero-eq-raise-zero-abs-ℝ)

abstract
  eq-metric-space-normed-real-vector-space-metric-space-ℝ :
    (l : Level) →
    metric-space-Normed-ℝ-Vector-Space (normed-real-vector-space-ℝ l) ＝
    metric-space-ℝ l
  eq-metric-space-normed-real-vector-space-metric-space-ℝ l =
    eq-isometric-eq-Metric-Space _ _
      ( refl , λ d x y → inv-iff (neighborhood-iff-leq-dist-ℝ d x y))
```

### Negation is an isometry in the metric space of a normed vector space

```agda
module _
  {l1 l2 : Level} (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
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
        ( λ x y →
          sim-eq-ℝ
            ( inv
              ( equational-reasoning
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
                  by commutative-dist-Normed-ℝ-Vector-Space V y x)))
```

### Addition is an isometry in the metric space of a normed vector space

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  (u : type-Normed-ℝ-Vector-Space V)
  where

  abstract
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
        ( λ v w →
          sim-eq-ℝ
            ( ap
              ( map-norm-Normed-ℝ-Vector-Space V)
              ( inv
                ( right-subtraction-left-add-Ab
                  ( ab-Normed-ℝ-Vector-Space V)
                  ( u)
                  ( v)
                  ( w)))))
```

### The norm of the zero vector is zero

```agda
module _
  {l1 l2 : Level}
  (V : Normed-ℝ-Vector-Space l1 l2)
  where

  abstract
    is-zero-norm-zero-Normed-ℝ-Vector-Space :
      map-norm-Normed-ℝ-Vector-Space V (zero-Normed-ℝ-Vector-Space V) ＝
      raise-ℝ l1 zero-ℝ
    is-zero-norm-zero-Normed-ℝ-Vector-Space =
      is-zero-seminorm-zero-Seminormed-ℝ-Vector-Space
        ( seminormed-vector-space-Normed-ℝ-Vector-Space V)
```

## See also

- [Real Banach spaces](linear-algebra.real-banach-spaces.md), normed real vector
  spaces for which the induced metric space is
  [complete](metric-spaces.complete-metric-spaces.md)

## External links

- [Normed vector space](https://en.wikipedia.org/wiki/Normed_vector_space) on
  Wikipedia
