# Seminormed complex vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.seminormed-complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.magnitude-complex-numbers

open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.complex-vector-spaces
open import linear-algebra.seminormed-real-vector-spaces

open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
```

</details>

## Idea

A
{{#concept "seminorm" WDID=Q1416088 WD="seminorm" Disambiguation="on a complex vector space" Agda=seminorm-ℂ-Vector-Space}}
on a [complex vector space](linear-algebra.complex-vector-spaces.md) `V` is a
[real](real-numbers.dedekind-real-numbers.md)-valued function `p` on the vector
space which is

- **Triangular.** `p(x + y) ≤ p(x) + p(y)` for all `x` and `y` in `V`, and
- **Absolutely homogeneous.** `p(c * x) = |c| * p(x)` for all
  [complex numbers](complex-numbers.complex-numbers.md) `c` and `x` in `V`.

These conditions together imply that `p(x) ≥ 0` for any `x`, and `p(0) = 0`.

A complex vector space equipped with such a seminorm is called a
{{#concept "seminormed space" WD="seminormed space" WDID=Q63793693 Disambiguation="complex seminormed space" Agda=Seminormed-ℂ-Vector-Space}}.
A seminormed space has an induced
[pseudometric structure](metric-spaces.pseudometric-spaces.md) defined by the
neighborhood relation that `v` and `w` are in an `ε`-neighborhood of each other
if `p(v - w) ≤ ε`.

**Terminology.** The term _absolute homogeneity_ comes from the more general
concept of
[homogeneous functions](https://en.wikipedia.org/wiki/Homogeneous_function). A
multivariable function `f` on real vector spaces is said to be _homogeneous of
degree `k`_ if for every scalar `s` we have that
`f(sx₀,sx₁,…,sxₙ) = sᵏf(x₀,x₁,…,xₙ)`. In particular, you may note that any
homogeneous bilinear form must be homogeneous of degree one.

## Definition

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (p : type-ℂ-Vector-Space V → ℝ l1)
  where

  is-triangular-prop-seminorm-ℂ-Vector-Space : Prop (l1 ⊔ l2)
  is-triangular-prop-seminorm-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ x →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ y → leq-prop-ℝ (p (add-ℂ-Vector-Space V x y)) (p x +ℝ p y)))

  is-triangular-seminorm-ℂ-Vector-Space : UU (l1 ⊔ l2)
  is-triangular-seminorm-ℂ-Vector-Space =
    type-Prop is-triangular-prop-seminorm-ℂ-Vector-Space

  is-absolutely-homogeneous-prop-seminorm-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-absolutely-homogeneous-prop-seminorm-ℂ-Vector-Space =
    Π-Prop
      ( ℂ l1)
      ( λ c →
        Π-Prop
          ( type-ℂ-Vector-Space V)
          ( λ x →
            Id-Prop
              ( ℝ-Set l1)
              ( p (mul-ℂ-Vector-Space V c x))
              ( magnitude-ℂ c *ℝ p x)))

  is-absolutely-homogeneous-seminorm-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-absolutely-homogeneous-seminorm-ℂ-Vector-Space =
    type-Prop is-absolutely-homogeneous-prop-seminorm-ℂ-Vector-Space

  is-seminorm-prop-ℂ-Vector-Space : Prop (lsuc l1 ⊔ l2)
  is-seminorm-prop-ℂ-Vector-Space =
    is-triangular-prop-seminorm-ℂ-Vector-Space ∧
    is-absolutely-homogeneous-prop-seminorm-ℂ-Vector-Space

  is-seminorm-ℂ-Vector-Space : UU (lsuc l1 ⊔ l2)
  is-seminorm-ℂ-Vector-Space = type-Prop is-seminorm-prop-ℂ-Vector-Space

seminorm-ℂ-Vector-Space :
  {l1 l2 : Level} → ℂ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
seminorm-ℂ-Vector-Space V =
  type-subtype (is-seminorm-prop-ℂ-Vector-Space V)

Seminormed-ℂ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Seminormed-ℂ-Vector-Space l1 l2 =
  Σ (ℂ-Vector-Space l1 l2) seminorm-ℂ-Vector-Space

module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  vector-space-Seminormed-ℂ-Vector-Space : ℂ-Vector-Space l1 l2
  vector-space-Seminormed-ℂ-Vector-Space = pr1 V

  seminorm-Seminormed-ℂ-Vector-Space :
    seminorm-ℂ-Vector-Space vector-space-Seminormed-ℂ-Vector-Space
  seminorm-Seminormed-ℂ-Vector-Space = pr2 V

  type-Seminormed-ℂ-Vector-Space : UU l2
  type-Seminormed-ℂ-Vector-Space =
    type-ℂ-Vector-Space vector-space-Seminormed-ℂ-Vector-Space

  map-seminorm-Seminormed-ℂ-Vector-Space : type-Seminormed-ℂ-Vector-Space → ℝ l1
  map-seminorm-Seminormed-ℂ-Vector-Space =
    pr1 seminorm-Seminormed-ℂ-Vector-Space

  is-triangular-seminorm-Seminormed-ℂ-Vector-Space :
    is-triangular-seminorm-ℂ-Vector-Space
      ( vector-space-Seminormed-ℂ-Vector-Space)
      ( map-seminorm-Seminormed-ℂ-Vector-Space)
  is-triangular-seminorm-Seminormed-ℂ-Vector-Space =
    pr1 (pr2 seminorm-Seminormed-ℂ-Vector-Space)

  is-absolutely-homogeneous-seminorm-Seminormed-ℂ-Vector-Space :
    is-absolutely-homogeneous-seminorm-ℂ-Vector-Space
      ( vector-space-Seminormed-ℂ-Vector-Space)
      ( map-seminorm-Seminormed-ℂ-Vector-Space)
  is-absolutely-homogeneous-seminorm-Seminormed-ℂ-Vector-Space =
    pr2 (pr2 seminorm-Seminormed-ℂ-Vector-Space)

  ab-Seminormed-ℂ-Vector-Space : Ab l2
  ab-Seminormed-ℂ-Vector-Space =
    ab-ℂ-Vector-Space vector-space-Seminormed-ℂ-Vector-Space

  zero-Seminormed-ℂ-Vector-Space : type-Seminormed-ℂ-Vector-Space
  zero-Seminormed-ℂ-Vector-Space = zero-Ab ab-Seminormed-ℂ-Vector-Space

  add-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space → type-Seminormed-ℂ-Vector-Space →
    type-Seminormed-ℂ-Vector-Space
  add-Seminormed-ℂ-Vector-Space = add-Ab ab-Seminormed-ℂ-Vector-Space

  neg-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space → type-Seminormed-ℂ-Vector-Space
  neg-Seminormed-ℂ-Vector-Space = neg-Ab ab-Seminormed-ℂ-Vector-Space

  diff-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space → type-Seminormed-ℂ-Vector-Space →
    type-Seminormed-ℂ-Vector-Space
  diff-Seminormed-ℂ-Vector-Space =
    right-subtraction-Ab ab-Seminormed-ℂ-Vector-Space

  dist-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space → type-Seminormed-ℂ-Vector-Space → ℝ l1
  dist-Seminormed-ℂ-Vector-Space v w =
    map-seminorm-Seminormed-ℂ-Vector-Space (diff-Seminormed-ℂ-Vector-Space v w)
```

## Properties

### A seminormed complex vector space is a seminormed real vector space

```agda
module _
  {l1 l2 : Level}
  (V : ℂ-Vector-Space l1 l2)
  (p : type-ℂ-Vector-Space V → ℝ l1)
  where

  abstract
    is-real-absolutely-homogeneous-is-seminorm-ℂ-Vector-Space :
      is-seminorm-ℂ-Vector-Space V p →
      (c : ℝ l1) (v : type-ℂ-Vector-Space V) →
      p (mul-real-ℂ-Vector-Space V c v) ＝ abs-ℝ c *ℝ p v
    is-real-absolutely-homogeneous-is-seminorm-ℂ-Vector-Space (_ , H) c v =
      H (complex-ℝ c) v ∙ ap-mul-ℝ (magnitude-complex-ℝ c) refl

  is-seminorm-real-ℂ-Vector-Space :
    is-seminorm-ℂ-Vector-Space V p →
    is-seminorm-ℝ-Vector-Space (real-vector-space-ℂ-Vector-Space V) p
  is-seminorm-real-ℂ-Vector-Space H@(triangular , _) =
    ( triangular ,
      is-real-absolutely-homogeneous-is-seminorm-ℂ-Vector-Space H)

seminormed-real-vector-space-Seminormed-ℂ-Vector-Space :
  {l1 l2 : Level} →
  Seminormed-ℂ-Vector-Space l1 l2 → Seminormed-ℝ-Vector-Space l1 l2
seminormed-real-vector-space-Seminormed-ℂ-Vector-Space (V , p , S) =
  ( real-vector-space-ℂ-Vector-Space V ,
    p ,
    is-seminorm-real-ℂ-Vector-Space V p S)
```

### The seminorm of the zero vector is zero

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  abstract
    eq-zero-seminorm-zero-Seminormed-ℂ-Vector-Space :
      map-seminorm-Seminormed-ℂ-Vector-Space V
        ( zero-Seminormed-ℂ-Vector-Space V) ＝
      raise-zero-ℝ l1
    eq-zero-seminorm-zero-Seminormed-ℂ-Vector-Space =
      eq-zero-seminorm-zero-Seminormed-ℝ-Vector-Space
        ( seminormed-real-vector-space-Seminormed-ℂ-Vector-Space V)
```

### The seminorm of the negation of a vector is equal to the seminorm of the vector

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  abstract
    seminorm-neg-Seminormed-ℂ-Vector-Space :
      (v : type-Seminormed-ℂ-Vector-Space V) →
      map-seminorm-Seminormed-ℂ-Vector-Space
        ( V)
        ( neg-Seminormed-ℂ-Vector-Space V v) ＝
      map-seminorm-Seminormed-ℂ-Vector-Space V v
    seminorm-neg-Seminormed-ℂ-Vector-Space =
      seminorm-neg-Seminormed-ℝ-Vector-Space
        ( seminormed-real-vector-space-Seminormed-ℂ-Vector-Space V)
```

### The distance function on a seminormed complex vector space satisfies the triangle inequality

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  abstract
    triangular-dist-Seminormed-ℂ-Vector-Space :
      (v w x : type-Seminormed-ℂ-Vector-Space V) →
      leq-ℝ
        ( dist-Seminormed-ℂ-Vector-Space V v x)
        ( dist-Seminormed-ℂ-Vector-Space V v w +ℝ
          dist-Seminormed-ℂ-Vector-Space V w x)
    triangular-dist-Seminormed-ℂ-Vector-Space =
      triangular-dist-Seminormed-ℝ-Vector-Space
        ( seminormed-real-vector-space-Seminormed-ℂ-Vector-Space V)
```

### The seminorm of a vector is nonnegative

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  abstract
    is-nonnegative-seminorm-Seminormed-ℂ-Vector-Space :
      (v : type-Seminormed-ℂ-Vector-Space V) →
      is-nonnegative-ℝ (map-seminorm-Seminormed-ℂ-Vector-Space V v)
    is-nonnegative-seminorm-Seminormed-ℂ-Vector-Space =
      is-nonnegative-seminorm-Seminormed-ℝ-Vector-Space
        ( seminormed-real-vector-space-Seminormed-ℂ-Vector-Space V)

  nonnegative-seminorm-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-seminorm-Seminormed-ℂ-Vector-Space v =
    ( map-seminorm-Seminormed-ℂ-Vector-Space V v ,
      is-nonnegative-seminorm-Seminormed-ℂ-Vector-Space v)
```

### The pseudometric space associated with a seminormed vector space

```agda
module _
  {l1 l2 : Level}
  (V : Seminormed-ℂ-Vector-Space l1 l2)
  where

  nonnegative-dist-Seminormed-ℂ-Vector-Space :
    type-Seminormed-ℂ-Vector-Space V → type-Seminormed-ℂ-Vector-Space V → ℝ⁰⁺ l1
  nonnegative-dist-Seminormed-ℂ-Vector-Space v w =
    ( dist-Seminormed-ℂ-Vector-Space V v w ,
      is-nonnegative-seminorm-Seminormed-ℂ-Vector-Space V _)

  neighborhood-prop-Seminormed-ℂ-Vector-Space :
    Rational-Neighborhood-Relation l1 (type-Seminormed-ℂ-Vector-Space V)
  neighborhood-prop-Seminormed-ℂ-Vector-Space d v w =
    leq-prop-ℝ
      ( dist-Seminormed-ℂ-Vector-Space V v w)
      ( real-ℚ⁺ d)

  neighborhood-Seminormed-ℂ-Vector-Space :
    ℚ⁺ → Relation l1 (type-Seminormed-ℂ-Vector-Space V)
  neighborhood-Seminormed-ℂ-Vector-Space d =
    type-Relation-Prop (neighborhood-prop-Seminormed-ℂ-Vector-Space d)

  pseudometric-structure-Seminormed-ℂ-Vector-Space :
    Pseudometric-Structure l1 (type-Seminormed-ℂ-Vector-Space V)
  pseudometric-structure-Seminormed-ℂ-Vector-Space =
    pseudometric-structure-Seminormed-ℝ-Vector-Space
      ( seminormed-real-vector-space-Seminormed-ℂ-Vector-Space V)

  pseudometric-space-Seminormed-ℂ-Vector-Space : Pseudometric-Space l2 l1
  pseudometric-space-Seminormed-ℂ-Vector-Space =
    ( type-Seminormed-ℂ-Vector-Space V ,
      pseudometric-structure-Seminormed-ℂ-Vector-Space)
```

### The complex numbers are a seminormed vector space over themselves

```agda
seminorm-magnitude-ℂ :
  (l : Level) → seminorm-ℂ-Vector-Space (complex-vector-space-ℂ l)
seminorm-magnitude-ℂ l =
  ( magnitude-ℂ ,
    triangular-magnitude-ℂ ,
    distributive-magnitude-mul-ℂ)

seminormed-complex-vector-space-ℂ :
  (l : Level) → Seminormed-ℂ-Vector-Space l (lsuc l)
seminormed-complex-vector-space-ℂ l =
  ( complex-vector-space-ℂ l , seminorm-magnitude-ℂ l)
```
