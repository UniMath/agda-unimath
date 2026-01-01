# Proper closed intervals in the real numbers

```agda
module real-numbers.proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.action-on-cauchy-approximations-short-maps-metric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.closed-subsets-metric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.subspaces-metric-spaces

open import order-theory.large-posets

open import real-numbers.accumulation-points-subsets-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.apartness-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.isometry-difference-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A
{{#concept "proper closed interval" Disambiguation="in ℝ" Agda=proper-closed-interval-ℝ}}
in the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[closed interval](real-numbers.closed-intervals-real-numbers.md) in which the
lower bound is
[strictly less than](real-numbers.strict-inequality-real-numbers.md) the upper
bound.

## Definition

```agda
proper-closed-interval-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
proper-closed-interval-ℝ l1 l2 = Σ (ℝ l1) (λ x → Σ (ℝ l2) (λ y → le-ℝ x y))

closed-interval-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → closed-interval-ℝ l1 l2
closed-interval-proper-closed-interval-ℝ (a , b , a<b) =
  ((a , b) , leq-le-ℝ a<b)

lower-bound-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ l1
lower-bound-proper-closed-interval-ℝ (a , b , a<b) = a

upper-bound-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ l2
upper-bound-proper-closed-interval-ℝ (a , b , a<b) = b

subtype-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  subset-ℝ (l1 ⊔ l2 ⊔ l) l
subtype-proper-closed-interval-ℝ l (a , b , _) x =
  leq-prop-ℝ a x ∧ leq-prop-ℝ x b

is-in-proper-closed-interval-ℝ :
  {l1 l2 l3 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ l3 → UU (l1 ⊔ l2 ⊔ l3)
is-in-proper-closed-interval-ℝ (a , b , _) x = leq-ℝ a x × leq-ℝ x b

type-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  UU (l1 ⊔ l2 ⊔ lsuc l)
type-proper-closed-interval-ℝ l [a,b] =
  type-subtype (subtype-proper-closed-interval-ℝ l [a,b])
```

## Properties

### The metric space associated with a proper closed interval

```agda
metric-space-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
metric-space-proper-closed-interval-ℝ l [a,b] =
  metric-space-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```

### The metric space associated with a proper closed interval is closed

```agda
abstract
  is-closed-subset-proper-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-closed-subset-Metric-Space
      ( metric-space-ℝ l3)
      ( subtype-proper-closed-interval-ℝ l3 [a,b])
  is-closed-subset-proper-closed-interval-ℝ [a,b] =
    is-closed-subset-closed-interval-ℝ
      ( closed-interval-proper-closed-interval-ℝ [a,b])

closed-subset-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  closed-subset-Metric-Space (l1 ⊔ l2 ⊔ l) (metric-space-ℝ l)
closed-subset-proper-closed-interval-ℝ l [a,b] =
  closed-subset-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```

### The complete metric space associated with a proper closed interval

```agda
complete-metric-space-proper-closed-interval-ℝ :
  {l1 l2 : Level} (l : Level) → proper-closed-interval-ℝ l1 l2 →
  Complete-Metric-Space (l1 ⊔ l2 ⊔ lsuc l) l
complete-metric-space-proper-closed-interval-ℝ l [a,b] =
  complete-metric-space-closed-interval-ℝ
    ( l)
    ( closed-interval-proper-closed-interval-ℝ [a,b])
```

### The clamp function

```agda
clamp-proper-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) → ℝ l3 →
  type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b]
clamp-proper-closed-interval-ℝ [a,b] =
  clamp-closed-interval-ℝ (closed-interval-proper-closed-interval-ℝ [a,b])
```

### The clamp function is a short function

```agda
abstract
  is-short-map-clamp-proper-closed-interval-ℝ :
    {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
    is-short-map-Metric-Space
      ( metric-space-ℝ l3)
      ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
      ( clamp-proper-closed-interval-ℝ [a,b])
  is-short-map-clamp-proper-closed-interval-ℝ [a,b] =
    is-short-map-clamp-closed-interval-ℝ
      ( closed-interval-proper-closed-interval-ℝ [a,b])

short-map-clamp-proper-closed-interval-ℝ :
  {l1 l2 l3 : Level} ([a,b] : proper-closed-interval-ℝ l1 l2) →
  short-map-Metric-Space
    ( metric-space-ℝ l3)
    ( metric-space-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
short-map-clamp-proper-closed-interval-ℝ [a,b] =
  short-map-clamp-closed-interval-ℝ (closed-interval-proper-closed-interval-ℝ [a,b])
```

### Every real number in a proper closed interval is an accumulation point in that proper closed interval

Note that this cannot be made more universe-polymorphic.

```agda
abstract
  is-accumulation-point-le-upper-bound-proper-closed-interval-ℝ :
    {l : Level} ([a,b] : proper-closed-interval-ℝ l l) →
    (x : ℝ l) → is-in-proper-closed-interval-ℝ [a,b] x →
    le-ℝ x (upper-bound-proper-closed-interval-ℝ [a,b]) →
    is-accumulation-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l [a,b])
      ( x)
  is-accumulation-point-le-upper-bound-proper-closed-interval-ℝ
    {l} [a,b]@(a , b , a<b) x (a≤x , x≤b) x<b =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      motive =
        is-accumulation-point-prop-subset-ℝ
          ( subtype-proper-closed-interval-ℝ _ [a,b])
          ( x)
      short-map-clamp-add =
        comp-short-map-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-ℝ lzero)
          ( metric-space-proper-closed-interval-ℝ l [a,b])
          ( comp-short-map-Metric-Space
            ( metric-space-ℝ lzero)
            ( metric-space-ℝ l)
            ( metric-space-proper-closed-interval-ℝ l [a,b])
            ( short-map-clamp-proper-closed-interval-ℝ [a,b])
            ( short-map-left-add-ℝ x))
          ( short-map-isometry-Metric-Space
            ( metric-space-ℚ)
            ( metric-space-ℝ lzero)
            ( isometry-metric-space-real-ℚ))
      short-inclusion =
        short-inclusion-subspace-Metric-Space
          ( metric-space-ℝ l)
          ( subtype-proper-closed-interval-ℝ l [a,b])
      approx-clamp-add =
        map-cauchy-approximation-short-map-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-proper-closed-interval-ℝ l [a,b])
          ( short-map-clamp-add)
          ( cauchy-approximation-rational-ℚ⁺)
    in
      intro-exists
        ( approx-clamp-add)
        ( ( λ ε →
            apart-located-metric-space-apart-ℝ _ _
              ( apart-le-ℝ'
                ( concatenate-le-leq-ℝ
                  ( x)
                  ( min-ℝ b (x +ℝ real-ℚ⁺ ε))
                  ( max-ℝ a (min-ℝ b (x +ℝ real-ℚ⁺ ε)))
                  ( le-min-le-le-ℝ
                    ( x<b)
                    ( le-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ ε)))
                  ( leq-right-max-ℝ _ _)))) ,
          tr
            ( is-limit-cauchy-approximation-Metric-Space
              ( metric-space-ℝ l)
              ( map-cauchy-approximation-short-map-Metric-Space
                ( metric-space-proper-closed-interval-ℝ l [a,b])
                ( metric-space-ℝ l)
                ( short-inclusion)
                ( approx-clamp-add)))
            ( equational-reasoning
              max-ℝ a (min-ℝ b (x +ℝ zero-ℝ))
              ＝ max-ℝ a (min-ℝ b x)
                by ap-max-ℝ refl (ap-min-ℝ refl (right-unit-law-add-ℝ x))
              ＝ max-ℝ a x
                by ap-max-ℝ refl (eq-sim-ℝ (right-leq-left-min-ℝ x≤b))
              ＝ x
                by eq-sim-ℝ (left-leq-right-max-ℝ a≤x))
            ( preserves-limit-map-cauchy-approximation-short-map-Metric-Space
              ( metric-space-ℚ)
              ( metric-space-ℝ l)
              ( comp-short-map-Metric-Space
                ( metric-space-ℚ)
                ( metric-space-proper-closed-interval-ℝ l [a,b])
                ( metric-space-ℝ l)
                ( short-inclusion)
                ( short-map-clamp-add))
              ( cauchy-approximation-rational-ℚ⁺)
              ( zero-ℚ)
              ( is-zero-limit-rational-ℚ⁺)))

  is-accumulation-point-le-lower-bound-proper-closed-interval-ℝ :
    {l : Level} ([a,b] : proper-closed-interval-ℝ l l) →
    (x : ℝ l) → is-in-proper-closed-interval-ℝ [a,b] x →
    le-ℝ (lower-bound-proper-closed-interval-ℝ [a,b]) x →
    is-accumulation-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l [a,b])
      ( x)
  is-accumulation-point-le-lower-bound-proper-closed-interval-ℝ
    {l} [a,b]@(a , b , a<b) x (a≤x , x≤b) a<x =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
      motive =
        is-accumulation-point-prop-subset-ℝ
          ( subtype-proper-closed-interval-ℝ _ [a,b])
          ( x)
      short-map-clamp-diff =
        comp-short-map-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-ℝ lzero)
          ( metric-space-proper-closed-interval-ℝ l [a,b])
          ( comp-short-map-Metric-Space
            ( metric-space-ℝ lzero)
            ( metric-space-ℝ l)
            ( metric-space-proper-closed-interval-ℝ l [a,b])
            ( short-map-clamp-proper-closed-interval-ℝ [a,b])
            ( short-map-left-diff-ℝ x))
          ( short-map-isometry-Metric-Space
            ( metric-space-ℚ)
            ( metric-space-ℝ lzero)
            ( isometry-metric-space-real-ℚ))
      short-inclusion =
        short-inclusion-subspace-Metric-Space
          ( metric-space-ℝ l)
          ( subtype-proper-closed-interval-ℝ l [a,b])
      approx-clamp-diff =
        map-cauchy-approximation-short-map-Metric-Space
          ( metric-space-ℚ)
          ( metric-space-proper-closed-interval-ℝ l [a,b])
          ( short-map-clamp-diff)
          ( cauchy-approximation-rational-ℚ⁺)
    in
      intro-exists
        ( approx-clamp-diff)
        ( ( λ ε →
            apart-located-metric-space-apart-ℝ _ _
              ( apart-le-ℝ
                ( le-max-le-le-ℝ
                  ( a<x)
                  ( concatenate-leq-le-ℝ
                    ( min-ℝ b (x -ℝ real-ℚ⁺ ε))
                    ( x -ℝ real-ℚ⁺ ε)
                    ( x)
                    ( leq-right-min-ℝ _ _)
                    ( le-diff-real-ℝ⁺ x (positive-real-ℚ⁺ ε)))))) ,
          tr
            ( is-limit-cauchy-approximation-Metric-Space
              ( metric-space-ℝ l)
              ( map-cauchy-approximation-short-map-Metric-Space
                ( metric-space-proper-closed-interval-ℝ l [a,b])
                ( metric-space-ℝ l)
                ( short-inclusion)
                ( approx-clamp-diff)))
            ( equational-reasoning
              max-ℝ a (min-ℝ b (x -ℝ zero-ℝ))
              ＝ max-ℝ a (min-ℝ b x)
                by ap-max-ℝ refl (ap-min-ℝ refl (right-unit-law-diff-ℝ x))
              ＝ max-ℝ a x
                by
                  ap-max-ℝ refl (eq-sim-ℝ (right-leq-left-min-ℝ x≤b))
              ＝ x
                by eq-sim-ℝ (left-leq-right-max-ℝ a≤x))
            ( preserves-limit-map-cauchy-approximation-short-map-Metric-Space
              ( metric-space-ℚ)
              ( metric-space-ℝ l)
              ( comp-short-map-Metric-Space
                ( metric-space-ℚ)
                ( metric-space-proper-closed-interval-ℝ l [a,b])
                ( metric-space-ℝ l)
                ( short-inclusion)
                ( short-map-clamp-diff))
              ( cauchy-approximation-rational-ℚ⁺)
              ( zero-ℚ)
              ( is-zero-limit-rational-ℚ⁺)))

  is-accumulation-point-is-in-proper-closed-interval-ℝ :
    {l : Level} ([a,b] : proper-closed-interval-ℝ l l) →
    (x : ℝ l) → is-in-proper-closed-interval-ℝ [a,b] x →
    is-accumulation-point-subset-ℝ
      ( subtype-proper-closed-interval-ℝ l [a,b])
      ( x)
  is-accumulation-point-is-in-proper-closed-interval-ℝ
    {l} [a,b]@(a , b , a<b) x a≤x≤b =
    elim-disjunction
      ( is-accumulation-point-prop-subset-ℝ
        ( subtype-proper-closed-interval-ℝ _ [a,b])
        ( x))
      ( is-accumulation-point-le-lower-bound-proper-closed-interval-ℝ
        ( [a,b])
        ( x)
        ( a≤x≤b))
      ( is-accumulation-point-le-upper-bound-proper-closed-interval-ℝ
        ( [a,b])
        ( x)
        ( a≤x≤b))
      ( cotransitive-le-ℝ a b x a<b)
```
