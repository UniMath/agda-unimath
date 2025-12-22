# Normed complex vector spaces

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.normed-complex-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.magnitude-complex-numbers
open import complex-numbers.metric-space-of-complex-numbers
open import complex-numbers.zero-complex-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.complex-vector-spaces
open import linear-algebra.normed-real-vector-spaces
open import linear-algebra.seminormed-complex-vector-spaces

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.metric-spaces

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

A
{{#concept "norm" WDID=Q956437 WD="norm" Disambiguation="on a complex vector space" Agda=norm-ℂ-Vector-Space}}
on a [complex vector space](linear-algebra.complex-vector-spaces.md) `V` is a
[seminorm](linear-algebra.seminormed-complex-vector-spaces.md) `p` on `V` that
is **extensional**: if `p(v) = 0`, then `v` is the zero vector.

A complex vector space equipped with such a norm is called a
{{#concept "normed vector space" Disambiguation="normed complex vector space" WDID=Q726210 WD="normed vector space" Agda=Normed-ℂ-Vector-Space}}.

A norm on a complex vector space induces a
[located](metric-spaces.located-metric-spaces.md)
[metric space](metric-spaces.metric-spaces.md) on the vector space, defined by
the neighborhood relation that `v` and `w` are in an `ε`-neighborhood of each
other if `p(v - w) ≤ ε`.

## Definition

```agda
module _
  {l1 l2 : Level} (V : ℂ-Vector-Space l1 l2) (p : seminorm-ℂ-Vector-Space V)
  where

  is-norm-prop-seminorm-ℂ-Vector-Space : Prop (l1 ⊔ l2)
  is-norm-prop-seminorm-ℂ-Vector-Space =
    Π-Prop
      ( type-ℂ-Vector-Space V)
      ( λ v →
        hom-Prop
          ( is-zero-prop-ℝ (pr1 p v))
          ( is-zero-prop-ℂ-Vector-Space V v))

  is-norm-seminorm-ℂ-Vector-Space : UU (l1 ⊔ l2)
  is-norm-seminorm-ℂ-Vector-Space =
    type-Prop is-norm-prop-seminorm-ℂ-Vector-Space

norm-ℂ-Vector-Space : {l1 l2 : Level} → ℂ-Vector-Space l1 l2 → UU (lsuc l1 ⊔ l2)
norm-ℂ-Vector-Space V = type-subtype (is-norm-prop-seminorm-ℂ-Vector-Space V)

Normed-ℂ-Vector-Space : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Normed-ℂ-Vector-Space l1 l2 = Σ (ℂ-Vector-Space l1 l2) norm-ℂ-Vector-Space

module _
  {l1 l2 : Level}
  (V : Normed-ℂ-Vector-Space l1 l2)
  where

  vector-space-Normed-ℂ-Vector-Space : ℂ-Vector-Space l1 l2
  vector-space-Normed-ℂ-Vector-Space = pr1 V

  norm-Normed-ℂ-Vector-Space :
    norm-ℂ-Vector-Space vector-space-Normed-ℂ-Vector-Space
  norm-Normed-ℂ-Vector-Space = pr2 V

  seminorm-Normed-ℂ-Vector-Space :
    seminorm-ℂ-Vector-Space vector-space-Normed-ℂ-Vector-Space
  seminorm-Normed-ℂ-Vector-Space = pr1 norm-Normed-ℂ-Vector-Space

  seminormed-vector-space-Normed-ℂ-Vector-Space :
    Seminormed-ℂ-Vector-Space l1 l2
  seminormed-vector-space-Normed-ℂ-Vector-Space =
    ( vector-space-Normed-ℂ-Vector-Space , seminorm-Normed-ℂ-Vector-Space)

  type-Normed-ℂ-Vector-Space : UU l2
  type-Normed-ℂ-Vector-Space =
    type-ℂ-Vector-Space vector-space-Normed-ℂ-Vector-Space

  ab-Normed-ℂ-Vector-Space : Ab l2
  ab-Normed-ℂ-Vector-Space =
    ab-ℂ-Vector-Space vector-space-Normed-ℂ-Vector-Space

  zero-Normed-ℂ-Vector-Space : type-Normed-ℂ-Vector-Space
  zero-Normed-ℂ-Vector-Space = zero-Ab ab-Normed-ℂ-Vector-Space

  add-Normed-ℂ-Vector-Space :
    type-Normed-ℂ-Vector-Space → type-Normed-ℂ-Vector-Space →
    type-Normed-ℂ-Vector-Space
  add-Normed-ℂ-Vector-Space = add-Ab ab-Normed-ℂ-Vector-Space

  neg-Normed-ℂ-Vector-Space :
    type-Normed-ℂ-Vector-Space → type-Normed-ℂ-Vector-Space
  neg-Normed-ℂ-Vector-Space = neg-Ab ab-Normed-ℂ-Vector-Space

  diff-Normed-ℂ-Vector-Space :
    type-Normed-ℂ-Vector-Space → type-Normed-ℂ-Vector-Space →
    type-Normed-ℂ-Vector-Space
  diff-Normed-ℂ-Vector-Space = right-subtraction-Ab ab-Normed-ℂ-Vector-Space

  mul-Normed-ℂ-Vector-Space :
    ℂ l1 → type-Normed-ℂ-Vector-Space → type-Normed-ℂ-Vector-Space
  mul-Normed-ℂ-Vector-Space =
    mul-ℂ-Vector-Space vector-space-Normed-ℂ-Vector-Space
```

## Properties

### A normed complex vector space is a normed real vector space

```agda
normed-real-vector-space-Normed-ℂ-Vector-Space :
  {l1 l2 : Level} → Normed-ℂ-Vector-Space l1 l2 → Normed-ℝ-Vector-Space l1 l2
normed-real-vector-space-Normed-ℂ-Vector-Space (V , (p , S) , H) =
  ( real-vector-space-ℂ-Vector-Space V ,
    ( p , is-seminorm-real-ℂ-Vector-Space V p S) ,
    H)
```

### The metric space of a normed complex vector space

```agda
metric-space-Normed-ℂ-Vector-Space :
  {l1 l2 : Level} → Normed-ℂ-Vector-Space l1 l2 → Metric-Space l2 l1
metric-space-Normed-ℂ-Vector-Space V =
  metric-space-Normed-ℝ-Vector-Space
    ( normed-real-vector-space-Normed-ℂ-Vector-Space V)
```

### The complex numbers are a normed vector space over themselves

```agda
normed-complex-vector-space-ℂ :
  (l : Level) → Normed-ℂ-Vector-Space l (lsuc l)
normed-complex-vector-space-ℂ l =
  ( complex-vector-space-ℂ l ,
    seminorm-magnitude-ℂ l ,
    λ z |z|=0 → eq-raise-zero-is-zero-ℂ (is-extensional-magnitude-ℂ z |z|=0))

abstract
  isometric-eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ :
    (l : Level) →
    isometric-eq-Metric-Space
      ( metric-space-ℂ l)
      ( metric-space-Normed-ℂ-Vector-Space (normed-complex-vector-space-ℂ l))
  isometric-eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ l =
    ( refl , λ _ _ _ → id-iff)

  eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ :
    (l : Level) →
    metric-space-ℂ l ＝
    metric-space-Normed-ℂ-Vector-Space (normed-complex-vector-space-ℂ l)
  eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ l =
    eq-isometric-eq-Metric-Space
      ( metric-space-ℂ l)
      ( metric-space-Normed-ℂ-Vector-Space (normed-complex-vector-space-ℂ l))
      ( isometric-eq-metric-space-ℂ-metric-space-normed-complex-vector-space-ℂ
        ( l))
```
