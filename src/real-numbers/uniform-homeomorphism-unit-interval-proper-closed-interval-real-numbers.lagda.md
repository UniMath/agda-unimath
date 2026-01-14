# A uniform homeomorphism between the unit interval and a proper closed interval in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.uniform-homeomorphism-unit-interval-proper-closed-interval-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.closed-subsets-metric-spaces
open import metric-spaces.compact-metric-spaces
open import metric-spaces.subspaces-metric-spaces
open import metric-spaces.totally-bounded-metric-spaces
open import metric-spaces.uniform-homeomorphisms-metric-spaces
open import metric-spaces.uniformly-continuous-maps-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.cauchy-completeness-dedekind-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.inhabited-totally-bounded-subsets-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.proper-closed-intervals-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.totally-bounded-subsets-real-numbers
open import real-numbers.uniformly-continuous-endomaps-real-numbers
open import real-numbers.unit-closed-interval-real-numbers
```

</details>

## Idea

The [unit interval](real-numbers.unit-closed-interval-real-numbers.md) `[0, 1]`
is
[uniformly homeomorphic](metric-spaces.uniform-homeomorphisms-metric-spaces.md)
to any
[proper closed interval](real-numbers.proper-closed-intervals-real-numbers.md)
`[a, b]` on the [real numbers](real-numbers.dedekind-real-numbers.md), with the
simplest homeomorphism being the "scaling" map `x ↦ (b - a)x + a`.

## Proof

### The map from `[0, 1]` to a proper closed interval

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  opaque
    real-uniform-homeo-proper-unit-closed-interval-ℝ :
      type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3) → ℝ (l1 ⊔ l2 ⊔ l3)
    real-uniform-homeo-proper-unit-closed-interval-ℝ (x , 0≤x , x≤1) =
      let
        (a , b , a<b) = [a,b]
      in
        (b -ℝ a) *ℝ x +ℝ a

  abstract opaque
    unfolding real-uniform-homeo-proper-unit-closed-interval-ℝ

    lower-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ :
      (x : type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3)) →
      leq-ℝ
        ( lower-bound-proper-closed-interval-ℝ [a,b])
        ( real-uniform-homeo-proper-unit-closed-interval-ℝ x)
    lower-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , 0≤x , x≤1) =
      let
        (a , b , a<b) = [a,b]
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          a
          ≤ zero-ℝ +ℝ a
            by leq-eq-ℝ (inv (left-unit-law-add-ℝ a))
          ≤ (b -ℝ a) *ℝ zero-ℝ +ℝ a
            by
              leq-sim-ℝ'
                ( preserves-sim-right-add-ℝ a _ _
                  ( right-zero-law-mul-ℝ (b -ℝ a)))
          ≤ (b -ℝ a) *ℝ x +ℝ a
            by
              preserves-leq-right-add-ℝ a _ _
                ( preserves-leq-left-mul-ℝ⁺
                  ( positive-diff-le-ℝ a<b)
                  ( 0≤x))

    upper-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ :
      (x : type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3)) →
      leq-ℝ
        ( real-uniform-homeo-proper-unit-closed-interval-ℝ x)
        ( upper-bound-proper-closed-interval-ℝ [a,b])
    upper-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , 0≤x , x≤1) =
      let
        (a , b , a<b) = [a,b]
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          (b -ℝ a) *ℝ x +ℝ a
          ≤ (b -ℝ a) *ℝ one-ℝ +ℝ a
            by
              preserves-leq-right-add-ℝ a _ _
                ( preserves-leq-left-mul-ℝ⁺
                  ( positive-diff-le-ℝ a<b)
                  ( x≤1))
          ≤ (b -ℝ a) +ℝ a
            by leq-eq-ℝ (ap-add-ℝ (right-unit-law-mul-ℝ (b -ℝ a)) refl)
          ≤ b
            by leq-sim-ℝ (cancel-right-diff-add-ℝ b a)

  map-uniform-homeo-proper-unit-closed-interval-ℝ :
    type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3) →
    type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]
  map-uniform-homeo-proper-unit-closed-interval-ℝ x =
    ( real-uniform-homeo-proper-unit-closed-interval-ℝ x ,
      lower-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ x ,
      upper-bound-real-uniform-homeo-proper-unit-closed-interval-ℝ x)
```

### The map from a proper closed interval to `[0, 1]`

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  opaque
    real-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] → ℝ (l1 ⊔ l2 ⊔ l3)
    real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , a≤x , x≤b) =
      let
        (a , b , a<b) = [a,b]
      in
        real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (x -ℝ a)

  abstract opaque
    unfolding real-inv-uniform-homeo-proper-unit-closed-interval-ℝ

    lower-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      (x : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]) →
      leq-ℝ
        ( zero-ℝ)
        ( real-inv-uniform-homeo-proper-unit-closed-interval-ℝ x)
    lower-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , a≤x , x≤b) =
      let
        (a , b , a<b) = [a,b]
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          zero-ℝ
          ≤ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ zero-ℝ
            by leq-sim-ℝ' (right-zero-law-mul-ℝ _)
          ≤ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (a -ℝ a)
            by
              leq-sim-ℝ'
                ( preserves-sim-left-mul-ℝ _ _ _ (right-inverse-law-add-ℝ a))
          ≤ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (x -ℝ a)
            by
              preserves-leq-left-mul-ℝ⁺
                ( inv-ℝ⁺ (positive-diff-le-ℝ a<b))
                ( preserves-leq-right-add-ℝ _ _ _ a≤x)

    upper-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      (x : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]) →
      leq-ℝ
        ( real-inv-uniform-homeo-proper-unit-closed-interval-ℝ x)
        ( one-ℝ)
    upper-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , a≤x , x≤b) =
      let
        (a , b , a<b) = [a,b]
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        chain-of-inequalities
          real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (x -ℝ a)
          ≤ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (b -ℝ a)
            by
              preserves-leq-left-mul-ℝ⁺
                ( inv-ℝ⁺ (positive-diff-le-ℝ a<b))
                ( preserves-leq-right-add-ℝ _ _ _ x≤b)
          ≤ one-ℝ
            by leq-sim-ℝ (left-inverse-law-mul-ℝ⁺ (positive-diff-le-ℝ a<b))

  map-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
    type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] →
    type-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3)
  map-inv-uniform-homeo-proper-unit-closed-interval-ℝ x =
    ( real-inv-uniform-homeo-proper-unit-closed-interval-ℝ x ,
      lower-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
        ( x) ,
      upper-bound-real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
        ( x))
```

### The maps between `[0, 1]` and a proper closed interval are mutual inverses

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  abstract opaque
    unfolding
      real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      real-uniform-homeo-proper-unit-closed-interval-ℝ

    is-section-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      is-section
        ( map-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
        ( map-inv-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
    is-section-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , a≤x , x≤b) =
      let
        (a , b , a<b) = [a,b]
      in
        eq-type-subtype
          ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
          ( equational-reasoning
            ( ( b -ℝ a) *ℝ
              ( real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (x -ℝ a))) +ℝ
            ( a)
            ＝ (x -ℝ a) +ℝ a
              by
                ap-add-ℝ
                  ( eq-sim-ℝ
                    ( cancel-left-mul-div-ℝ⁺ (positive-diff-le-ℝ a<b) (x -ℝ a)))
                  ( refl)
            ＝ x
              by eq-sim-ℝ (cancel-right-diff-add-ℝ x a))

    is-retraction-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      is-retraction
        ( map-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
        ( map-inv-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
    is-retraction-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      (x , 0≤x , x≤1) =
      let
        (a , b , a<b) = [a,b]
      in
        eq-type-subtype
          ( subset-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
          ( equational-reasoning
            real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ (((b -ℝ a) *ℝ x +ℝ a) -ℝ a)
            ＝ real-inv-ℝ⁺ (positive-diff-le-ℝ a<b) *ℝ ((b -ℝ a) *ℝ x)
              by ap-mul-ℝ refl (eq-sim-ℝ (cancel-right-add-diff-ℝ _ _))
            ＝ x
              by eq-sim-ℝ (cancel-left-div-mul-ℝ⁺ (positive-diff-le-ℝ a<b) x))

  is-equiv-map-uniform-homeo-proper-unit-closed-interval-ℝ :
    is-equiv (map-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
  is-equiv-map-uniform-homeo-proper-unit-closed-interval-ℝ =
    is-equiv-is-invertible
      ( map-inv-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
      ( is-section-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ)
      ( is-retraction-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ)
```

### The maps between `[0, 1]` and a proper closed interval are uniformly continuous

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  abstract opaque
    unfolding
      real-inv-uniform-homeo-proper-unit-closed-interval-ℝ
      real-uniform-homeo-proper-unit-closed-interval-ℝ

    is-uniformly-continuous-map-uniform-homeo-proper-unit-closed-interval-ℝ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( map-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
    is-uniformly-continuous-map-uniform-homeo-proper-unit-closed-interval-ℝ =
      let
        (a , b , a<b) = [a,b]
      in
        is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
          ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
          ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
          ( uniformly-continuous-map-into-subspace-Metric-Space
            ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
            ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
            ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
            ( comp-uniformly-continuous-map-Metric-Space
              ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
              ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
              ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
              ( comp-uniformly-continuous-endomap-ℝ
                ( uniformly-continuous-right-add-ℝ a)
                ( uniformly-continuous-map-right-mul-ℝ (l1 ⊔ l2 ⊔ l3) (b -ℝ a)))
              ( uniformly-continuous-inclusion-subspace-Metric-Space
                ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
                ( subset-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))))
            ( λ x →
              pr2
                ( map-uniform-homeo-proper-unit-closed-interval-ℝ
                  ( l3)
                  ( [a,b])
                  ( x))))

    is-uniformly-continuous-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ :
      is-uniformly-continuous-map-Metric-Space
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
        ( map-inv-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b])
    is-uniformly-continuous-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ =
      let
        (a , b , a<b) = [a,b]
      in
        is-uniformly-continuous-map-uniformly-continuous-map-Metric-Space
          ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
          ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
          ( uniformly-continuous-map-into-subspace-Metric-Space
            ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
            ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
            ( subset-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
            ( comp-uniformly-continuous-map-Metric-Space
              ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
              ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
              ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
              ( comp-uniformly-continuous-endomap-ℝ
                ( uniformly-continuous-map-right-mul-ℝ
                  ( l1 ⊔ l2 ⊔ l3)
                  ( real-inv-ℝ⁺ (positive-diff-le-ℝ a<b)))
                ( uniformly-continuous-right-add-ℝ (neg-ℝ a)))
              ( uniformly-continuous-inclusion-subspace-Metric-Space
                ( metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
                ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])))
            ( λ x →
              pr2
                ( map-inv-uniform-homeo-proper-unit-closed-interval-ℝ
                  ( l3)
                  ( [a,b])
                  ( x))))
```

### The uniform homeomorphism between `[0, 1]` and a proper closed interval

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  uniform-homeo-unit-interval-proper-closed-interval-ℝ :
    uniform-homeo-Metric-Space
      ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
      ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
  uniform-homeo-unit-interval-proper-closed-interval-ℝ =
    ( map-uniform-homeo-proper-unit-closed-interval-ℝ l3 [a,b] ,
      is-equiv-map-uniform-homeo-proper-unit-closed-interval-ℝ
        ( l3)
        ( [a,b]) ,
      is-uniformly-continuous-map-uniform-homeo-proper-unit-closed-interval-ℝ
        ( l3)
        ( [a,b]) ,
      is-uniformly-continuous-map-inv-uniform-homeo-proper-unit-closed-interval-ℝ
        ( l3)
        ( [a,b]))
```

## Corollaries

### Every proper closed interval in `ℝ` is totally bounded

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  abstract
    is-totally-bounded-proper-closed-interval-ℝ :
      is-totally-bounded-subset-ℝ
        ( lsuc (l1 ⊔ l2 ⊔ l3))
        ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
    is-totally-bounded-proper-closed-interval-ℝ =
      preserves-is-totally-bounded-uniform-homeo-Metric-Space
        ( metric-space-unit-interval-ℝ (l1 ⊔ l2 ⊔ l3))
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( uniform-homeo-unit-interval-proper-closed-interval-ℝ l3 [a,b])
        ( is-totally-bounded-unit-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3))
```

### Every proper closed interval in `ℝ` is inhabited and totally bounded

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  inhabited-totally-bounded-subset-proper-closed-interval-ℝ :
    inhabited-totally-bounded-subset-ℝ
      ( l1 ⊔ l2 ⊔ l3)
      ( l1 ⊔ l2 ⊔ l3)
      ( lsuc (l1 ⊔ l2 ⊔ l3))
  inhabited-totally-bounded-subset-proper-closed-interval-ℝ =
    ( ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] ,
        is-totally-bounded-proper-closed-interval-ℝ l3 [a,b]) ,
      is-inhabited-subtype-proper-closed-interval-ℝ (l2 ⊔ l3) [a,b])
```

### Every proper closed interval in `ℝ` is compact

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  where

  abstract
    is-compact-metric-space-proper-closed-interval-ℝ :
      is-compact-Metric-Space
        ( lsuc (l1 ⊔ l2 ⊔ l3))
        ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
    is-compact-metric-space-proper-closed-interval-ℝ =
      ( is-totally-bounded-proper-closed-interval-ℝ l3 [a,b] ,
        is-complete-closed-subspace-Complete-Metric-Space
          ( complete-metric-space-ℝ (l1 ⊔ l2 ⊔ l3))
          ( subtype-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] ,
            is-closed-subset-proper-closed-interval-ℝ [a,b]))

  compact-metric-space-proper-closed-interval-ℝ :
    Compact-Metric-Space
      ( lsuc (l1 ⊔ l2 ⊔ l3))
      ( l1 ⊔ l2 ⊔ l3)
      ( lsuc (l1 ⊔ l2 ⊔ l3))
  compact-metric-space-proper-closed-interval-ℝ =
    ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b] ,
      is-compact-metric-space-proper-closed-interval-ℝ)
```
