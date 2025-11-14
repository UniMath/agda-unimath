# Metrics of metric spaces

```agda
module metric-spaces.metrics-of-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.located-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metrics
open import metric-spaces.short-functions-metric-spaces

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-nonnegative-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.saturation-inequality-nonnegative-real-numbers
open import real-numbers.similarity-nonnegative-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-nonnegative-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A function `ρ` from two elements of a
[metric space](metric-spaces.metric-spaces.md) `M` to the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is a
{{#concept "metric" disambiguation="of a metric space" WD="metric function" WDID=Q865746 Agda=is-metric-of-Metric-Space}}
of `M` if for all
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`d` and all `x y : M`, `x` and `y` are in a `d`-neighborhood of each other in
`M` [if and only if](foundation.logical-equivalences.md) `ρ x y ≤ real-ℚ⁺ d`.

It follows that `ρ` is a [metric](metric-spaces.metrics.md) on the
[set](foundation.sets.md) of elements of `M`, and that `M` is
[isometrically equivalent](metric-spaces.equality-of-metric-spaces.md) to the
metric space induced by `ρ`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  where

  is-metric-prop-Metric-Space : Prop (l1 ⊔ l2 ⊔ l3)
  is-metric-prop-Metric-Space =
    Π-Prop ℚ⁺
      ( λ d →
        Π-Prop
          ( type-Metric-Space M)
          ( λ x →
            Π-Prop
              ( type-Metric-Space M)
              ( λ y →
                neighborhood-prop-Metric-Space M d x y ⇔
                leq-prop-ℝ⁰⁺ (ρ x y) (nonnegative-real-ℚ⁺ d))))

  is-metric-of-Metric-Space : UU (l1 ⊔ l2 ⊔ l3)
  is-metric-of-Metric-Space = type-Prop is-metric-prop-Metric-Space
```

## Properties

### A metric is a metric of the metric space it induces

```agda
module _
  {l1 l2 : Level} (X : Set l1) (ρ : Metric l2 X)
  where

  is-metric-metric-space-Metric :
    is-metric-of-Metric-Space
      ( metric-space-Metric X ρ)
      ( dist-Metric X ρ)
  is-metric-metric-space-Metric _ _ _ = id-iff
```

### If `ρ` is a metric for a metric space, it is a metric

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  abstract
    is-reflexive-is-metric-of-Metric-Space :
      is-reflexive-distance-function (set-Metric-Space M) ρ
    is-reflexive-is-metric-of-Metric-Space x =
      sim-zero-leq-positive-rational-ℝ⁰⁺
        ( ρ x x)
        ( λ ε →
          forward-implication
            ( is-metric-M-ρ ε x x)
            ( refl-neighborhood-Metric-Space M ε x))

    is-symmetric-is-metric-of-Metric-Space :
      is-symmetric-distance-function (set-Metric-Space M) ρ
    is-symmetric-is-metric-of-Metric-Space x y =
      eq-sim-ℝ⁰⁺ (ρ x y) (ρ y x)
        ( sim-leq-same-positive-rational-ℝ⁰⁺ (ρ x y) (ρ y x)
          ( λ d →
            is-metric-M-ρ d y x ∘iff
            ( symmetric-neighborhood-Metric-Space M d x y ,
              symmetric-neighborhood-Metric-Space M d y x) ∘iff
            inv-iff (is-metric-M-ρ d x y)))

    is-triangular-is-metric-of-Metric-Space :
      is-triangular-distance-function (set-Metric-Space M) ρ
    is-triangular-is-metric-of-Metric-Space x y z =
      leq-le-positive-rational-ℝ⁰⁺ (ρ x z) (ρ x y +ℝ⁰⁺ ρ y z)
        ( λ d ρxy+ρyz<d →
          let
            open
              do-syntax-trunc-Prop (le-prop-ℝ⁰⁺ (ρ x z) (nonnegative-real-ℚ⁺ d))
          in do
            (d' , ρxy+ρyz<d' , d'<d) ← dense-rational-le-ℝ _ _ ρxy+ρyz<d
            ((q , r) , d'=q+r , ρxy<q , ρyz<r) ←
              le-split-add-rational-ℝ
                ( real-ℝ⁰⁺ (ρ x y))
                ( real-ℝ⁰⁺ (ρ y z))
                ( d')
                ( ρxy+ρyz<d')
            let
              d'⁺ =
                ( d' ,
                    is-positive-le-nonnegative-real-ℚ
                      ( ρ x y +ℝ⁰⁺ ρ y z)
                      ( d')
                      ( ρxy+ρyz<d'))
              q⁺ = (q , is-positive-le-nonnegative-real-ℚ (ρ x y) q ρxy<q)
              r⁺ = (r , is-positive-le-nonnegative-real-ℚ (ρ y z) r ρyz<r)
            concatenate-leq-le-ℝ _ _ _
              ( forward-implication
                ( is-metric-M-ρ d'⁺ x z)
                ( inv-tr
                  ( λ dd → neighborhood-Metric-Space M dd x z)
                  ( eq-ℚ⁺ d'=q+r)
                  ( triangular-neighborhood-Metric-Space M x y z
                    ( q⁺)
                    ( r⁺)
                    ( backward-implication
                      ( is-metric-M-ρ r⁺ y z)
                      ( leq-le-ℝ ρyz<r))
                    ( backward-implication
                      ( is-metric-M-ρ q⁺ x y)
                      ( leq-le-ℝ ρxy<q)))))
              ( d'<d))

    is-extensional-is-metric-of-Metric-Space :
      is-extensional-distance-function (set-Metric-Space M) ρ
    is-extensional-is-metric-of-Metric-Space x y ρxy~0 =
      eq-sim-Metric-Space M x y
        ( λ ε →
          backward-implication
            ( is-metric-M-ρ ε x y)
            ( preserves-leq-left-sim-ℝ⁰⁺
              ( nonnegative-real-ℚ⁺ ε)
              ( zero-ℝ⁰⁺)
              ( ρ x y)
              ( ρxy~0)
              ( leq-zero-ℝ⁰⁺ (nonnegative-real-ℚ⁺ ε))))

  is-metric-is-metric-of-Metric-Space :
    is-metric-distance-function (set-Metric-Space M) ρ
  is-metric-is-metric-of-Metric-Space =
    ( is-reflexive-is-metric-of-Metric-Space ,
      is-symmetric-is-metric-of-Metric-Space ,
      is-triangular-is-metric-of-Metric-Space ,
      is-extensional-is-metric-of-Metric-Space)

  metric-is-metric-of-Metric-Space : Metric l3 (set-Metric-Space M)
  metric-is-metric-of-Metric-Space =
    ( ρ ,
      is-metric-is-metric-of-Metric-Space)
```

### If `ρ` is a metric for a metric space `M`, then `M` is isometrically equivalent to the metric space induced by `ρ`

```agda
module _
  {l1 l2 l3 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l3 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  isometric-equiv-metric-is-metric-of-Metric-Space :
    isometric-equiv-Metric-Space
      ( M)
      ( metric-space-Metric
        ( set-Metric-Space M)
        ( metric-is-metric-of-Metric-Space M ρ is-metric-M-ρ))
  isometric-equiv-metric-is-metric-of-Metric-Space = (id-equiv , is-metric-M-ρ)
```

### If `ρ` is a metric for a metric space `M`, then `M` is located

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l2 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  abstract
    is-located-is-metric-of-Metric-Space : is-located-Metric-Space M
    is-located-is-metric-of-Metric-Space x y δ ε δ<ε =
      map-disjunction
        ( λ δ<ρxy Nδxy →
          not-le-leq-ℝ
            ( real-ℝ⁰⁺ (ρ x y))
            ( real-ℚ⁺ δ)
            ( forward-implication (is-metric-M-ρ δ x y) Nδxy)
            ( le-real-is-in-lower-cut-ℚ
              ( real-ℝ⁰⁺ (ρ x y))
              ( δ<ρxy)))
        ( λ ρxy<ε →
          backward-implication
            ( is-metric-M-ρ ε x y)
            ( leq-le-ℝ
              ( le-real-is-in-upper-cut-ℚ
                ( real-ℝ⁰⁺ (ρ x y))
                ( ρxy<ε))))
        ( is-located-lower-upper-cut-ℝ (real-ℝ⁰⁺ (ρ x y)) δ<ε)
```

### If `ρ` is a metric for a metric space `M` at the appropriate universe level, then `M` is equal to the metric space induced by `ρ`

```agda
module _
  {l1 l2 : Level} (M : Metric-Space l1 l2)
  (ρ : distance-function l2 (set-Metric-Space M))
  (is-metric-M-ρ : is-metric-of-Metric-Space M ρ)
  where

  abstract
    eq-metric-is-metric-of-Metric-Space :
      M ＝
      metric-space-Metric
        ( set-Metric-Space M)
        ( metric-is-metric-of-Metric-Space M ρ is-metric-M-ρ)
    eq-metric-is-metric-of-Metric-Space =
      eq-isometric-equiv-Metric-Space _ _
        ( isometric-equiv-metric-is-metric-of-Metric-Space M ρ is-metric-M-ρ)
```

### If `M` and `N` are metric spaces with metrics `dM` and `dN`, a function `f : M → N` is an isometry if and only if `dM x y` is similar to `dN (f x) (f y)` for all `x, y : M`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (M : Metric-Space l1 l2)
  (N : Metric-Space l3 l4)
  (dM : distance-function l5 (set-Metric-Space M))
  (dN : distance-function l6 (set-Metric-Space N))
  (is-metric-dM : is-metric-of-Metric-Space M dM)
  (is-metric-dN : is-metric-of-Metric-Space N dN)
  (f : type-function-Metric-Space M N)
  where

  abstract
    is-isometry-sim-metric-Metric-Space :
      ((x y : type-Metric-Space M) → sim-ℝ⁰⁺ (dM x y) (dN (f x) (f y))) →
      is-isometry-Metric-Space M N f
    is-isometry-sim-metric-Metric-Space H d x y =
      logical-equivalence-reasoning
        neighborhood-Metric-Space M d x y
        ↔ leq-ℝ (real-ℝ⁰⁺ (dM x y)) (real-ℚ⁺ d)
          by is-metric-dM d x y
        ↔ leq-ℝ (real-ℝ⁰⁺ (dN (f x) (f y))) (real-ℚ⁺ d)
          by leq-iff-left-sim-ℝ (H x y)
        ↔ neighborhood-Metric-Space N d (f x) (f y)
          by inv-iff (is-metric-dN d (f x) (f y))

    sim-metric-is-isometry-Metric-Space :
      is-isometry-Metric-Space M N f →
      (x y : type-Metric-Space M) →
      sim-ℝ⁰⁺ (dM x y) (dN (f x) (f y))
    sim-metric-is-isometry-Metric-Space H x y =
      sim-leq-same-positive-rational-ℝ⁰⁺
        ( dM x y)
        ( dN (f x) (f y))
        ( λ d →
          logical-equivalence-reasoning
            leq-ℝ (real-ℝ⁰⁺ (dM x y)) (real-ℚ⁺ d)
            ↔ neighborhood-Metric-Space M d x y
              by inv-iff (is-metric-dM d x y)
            ↔ neighborhood-Metric-Space N d (f x) (f y)
              by H d x y
            ↔ leq-ℝ (real-ℝ⁰⁺ (dN (f x) (f y))) (real-ℚ⁺ d)
              by is-metric-dN d (f x) (f y))

  is-isometry-iff-sim-metric-Metric-Space :
    is-isometry-Metric-Space M N f ↔
    ((x y : type-Metric-Space M) → sim-ℝ⁰⁺ (dM x y) (dN (f x) (f y)))
  is-isometry-iff-sim-metric-Metric-Space =
    ( sim-metric-is-isometry-Metric-Space ,
      is-isometry-sim-metric-Metric-Space)
```

### If `M` and `N` are metric spaces with metrics `dM` and `dN`, a function `f : M → N` is short if and only if `dN (f x) (f y) ≤ dM x y` for all `x, y : M`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (M : Metric-Space l1 l2)
  (N : Metric-Space l3 l4)
  (dM : distance-function l5 (set-Metric-Space M))
  (dN : distance-function l6 (set-Metric-Space N))
  (is-metric-dM : is-metric-of-Metric-Space M dM)
  (is-metric-dN : is-metric-of-Metric-Space N dN)
  (f : type-function-Metric-Space M N)
  where

  abstract
    is-short-function-leq-metric-Metric-Space :
      ((x y : type-Metric-Space M) → leq-ℝ⁰⁺ (dN (f x) (f y)) (dM x y)) →
      is-short-function-Metric-Space M N f
    is-short-function-leq-metric-Metric-Space H d x y Ndxy =
      backward-implication
        ( is-metric-dN d (f x) (f y))
        ( transitive-leq-ℝ
          ( real-ℝ⁰⁺ (dN (f x) (f y)))
          ( real-ℝ⁰⁺ (dM x y))
          ( real-ℚ⁺ d)
          ( forward-implication (is-metric-dM d x y) Ndxy)
          ( H x y))

    leq-metric-is-short-function-Metric-Space :
      is-short-function-Metric-Space M N f →
      (x y : type-Metric-Space M) →
      leq-ℝ⁰⁺ (dN (f x) (f y)) (dM x y)
    leq-metric-is-short-function-Metric-Space H x y =
      leq-leq-positive-rational-ℝ⁰⁺
        ( dN (f x) (f y))
        ( dM x y)
        ( λ d dMxy≤d →
          forward-implication
            ( is-metric-dN d (f x) (f y))
            ( H d x y (backward-implication (is-metric-dM d x y) dMxy≤d)))

  is-short-function-iff-leq-metric-Metric-Space :
    is-short-function-Metric-Space M N f ↔
    ((x y : type-Metric-Space M) → leq-ℝ⁰⁺ (dN (f x) (f y)) (dM x y))
  is-short-function-iff-leq-metric-Metric-Space =
    ( leq-metric-is-short-function-Metric-Space ,
      is-short-function-leq-metric-Metric-Space)
```

## See also

- [Metrics of metric spaces are uniformly continuous](metric-spaces.metrics-of-metric-spaces-are-uniformly-continuous.md)
