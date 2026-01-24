# Proper closed intervals in the real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.proper-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

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
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.isometry-addition-real-numbers
open import real-numbers.isometry-difference-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
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

positive-width-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ⁺ (l1 ⊔ l2)
positive-width-proper-closed-interval-ℝ (a , b , a<b) = positive-diff-le-ℝ a<b

width-proper-closed-interval-ℝ :
  {l1 l2 : Level} → proper-closed-interval-ℝ l1 l2 → ℝ (l1 ⊔ l2)
width-proper-closed-interval-ℝ (a , b , _) = b -ℝ a
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

### The clamp function is a short map

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
  short-map-clamp-closed-interval-ℝ
    ( closed-interval-proper-closed-interval-ℝ [a,b])
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
            ( isometry-real-ℚ))
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
            ( isometry-real-ℚ))
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

### Given any two elements `x` and `y` of a proper closed interval in an `ε`-neighborhood of each other, there exists a third point `z` in an `ε`-neighborhood of both `x` and `y` but apart from both of them

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  (x y : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
  (ε : ℚ⁺)
  (Nεxy : neighborhood-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 x) (pr1 y))
  where

  abstract
    exists-element-apart-from-both-in-neighborhood-le-proper-closed-interval-ℝ :
      le-ℝ (pr1 x) (pr1 y) →
      exists
        ( type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( λ z →
          apart-prop-ℝ (pr1 z) (pr1 x) ∧
          apart-prop-ℝ (pr1 z) (pr1 y) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 x) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 y))
    exists-element-apart-from-both-in-neighborhood-le-proper-closed-interval-ℝ
      x<y =
      let
        l123 = l1 ⊔ l2 ⊔ l3
        (xℝ , a≤x , x≤b) = x
        (yℝ , a≤y , y≤b) = y
        [x,y] = ((xℝ , yℝ) , leq-le-ℝ x<y)
        (a , b , a<b) = [a,b]
        motive =
          ∃ ( type-proper-closed-interval-ℝ l123 [a,b])
            ( λ z →
              apart-prop-ℝ (pr1 z) (pr1 x) ∧
              apart-prop-ℝ (pr1 z) (pr1 y) ∧
              neighborhood-prop-ℝ l123 ε (pr1 z) (pr1 x) ∧
              neighborhood-prop-ℝ l123 ε (pr1 z) (pr1 y))
        open do-syntax-trunc-Prop motive
      in do
        (z , x<z , z<y) ← dense-le-ℝ xℝ yℝ x<y
        let
          z' = raise-ℝ l123 z
          x<z' = preserves-le-right-raise-ℝ l123 x<z
          z'<y = preserves-le-left-raise-ℝ l123 z<y
          z'∈[x,y] = (leq-le-ℝ x<z' , leq-le-ℝ z'<y)
        intro-exists
          ( z' ,
            leq-le-ℝ (concatenate-leq-le-ℝ a xℝ z' a≤x x<z') ,
            leq-le-ℝ (concatenate-le-leq-ℝ z' yℝ b z'<y y≤b))
          ( apart-le-ℝ' x<z' ,
            apart-le-ℝ z'<y ,
            is-symmetric-neighborhood-ℝ
              ( ε)
              ( xℝ)
              ( z')
              ( subset-closed-interval-neighborhood-ℝ
                ( [x,y])
                ( ε)
                ( xℝ)
                ( is-reflexive-neighborhood-ℝ ε xℝ)
                ( Nεxy)
                ( z')
                ( z'∈[x,y])) ,
            is-symmetric-neighborhood-ℝ
              ( ε)
              ( yℝ)
              ( z')
              ( subset-closed-interval-neighborhood-ℝ
                ( [x,y])
                ( ε)
                ( yℝ)
                ( is-symmetric-neighborhood-ℝ ε xℝ yℝ Nεxy)
                ( is-reflexive-neighborhood-ℝ ε yℝ)
                ( z')
                ( z'∈[x,y])))

    exists-element-apart-from-both-in-neighborhood-bound-diff-le-lower-bound-proper-closed-interval-ℝ :
      (δ ε' : ℚ⁺) →
      le-ℝ (lower-bound-proper-closed-interval-ℝ [a,b] +ℝ real-ℚ⁺ δ) (pr1 x) →
      le-ℚ⁺ (ε' +ℚ⁺ ε') ε →
      le-ℝ (pr1 x -ℝ pr1 y) (real-ℚ⁺ (min-ℚ⁺ ε' δ)) →
      le-ℝ (pr1 y -ℝ pr1 x) (real-ℚ⁺ (min-ℚ⁺ ε' δ)) →
      exists
        ( type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( λ z →
          apart-prop-ℝ (pr1 z) (pr1 x) ∧
          apart-prop-ℝ (pr1 z) (pr1 y) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 x) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 y))
    exists-element-apart-from-both-in-neighborhood-bound-diff-le-lower-bound-proper-closed-interval-ℝ
      δ ε' a+δ<x ε'+ε'<ε x-y<ε'' y-x<ε'' =
      let
        (xℝ , a≤x , x≤b) = x
        (yℝ , a≤y , y≤b) = y
        (a , b , a<b) = [a,b]
        a<x = transitive-le-ℝ _ _ _ a+δ<x (le-left-add-real-ℚ⁺ a δ)
        ε'' = min-ℚ⁺ ε' δ
        z = max-ℝ a (xℝ -ℝ real-ℚ⁺ ε')
        x-ε''<y =
          le-transpose-right-add-ℝ _ _ _
            ( le-transpose-left-diff-ℝ' _ _ _ x-y<ε'')
        y-ε''<x =
          le-transpose-right-add-ℝ _ _ _
            ( le-transpose-left-diff-ℝ' _ _ _ y-x<ε'')
        z<x : le-ℝ z xℝ
        z<x =
          le-max-le-le-ℝ
            ( a<x)
            ( le-diff-real-ℚ⁺ xℝ ε')
        ε'<ε = transitive-le-ℚ⁺ ε' (ε' +ℚ⁺ ε') ε ε'+ε'<ε (le-right-add-ℚ⁺ ε' ε')
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        intro-exists
          ( z ,
            leq-left-max-ℝ _ _ ,
            transitive-leq-ℝ z xℝ b x≤b (leq-le-ℝ z<x))
          ( apart-le-ℝ z<x ,
            symmetric-apart-ℝ
              ( apart-max-apart-ℝ
                ( apart-le-ℝ'
                  ( transitive-le-ℝ
                    ( a)
                    ( xℝ -ℝ real-ℚ⁺ δ)
                    ( yℝ)
                    ( concatenate-leq-le-ℝ
                      ( xℝ -ℝ real-ℚ⁺ δ)
                      ( xℝ -ℝ real-ℚ⁺ ε'')
                      ( yℝ)
                      ( reverses-leq-left-diff-ℝ
                        ( xℝ)
                        ( preserves-leq-real-ℚ
                          ( leq-right-min-ℚ _ _)))
                      ( x-ε''<y))
                    ( le-transpose-left-add-ℝ _ _ _ a+δ<x)))
                ( apart-le-ℝ'
                  ( concatenate-leq-le-ℝ
                    ( xℝ -ℝ real-ℚ⁺ ε')
                    ( xℝ -ℝ real-ℚ⁺ ε'')
                    ( yℝ)
                    ( reverses-leq-left-diff-ℝ
                      ( xℝ)
                      ( preserves-leq-real-ℚ
                        ( leq-left-min-ℚ _ _)))
                    ( x-ε''<y)))) ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( z)
              ( xℝ)
              ( chain-of-inequalities
                z
                ≤ xℝ
                  by leq-le-ℝ z<x
                ≤ xℝ +ℝ real-ℚ⁺ ε
                  by leq-left-add-real-ℚ⁺ xℝ ε)
              ( leq-transpose-left-diff-ℝ _ _ _
                ( chain-of-inequalities
                  xℝ -ℝ real-ℚ⁺ ε
                  ≤ xℝ -ℝ real-ℚ⁺ ε'
                    by
                      reverses-leq-left-diff-ℝ
                        ( xℝ)
                        ( leq-le-ℝ (preserves-le-real-ℚ ε'<ε))
                  ≤ z
                    by leq-right-max-ℝ _ _)) ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( z)
              ( yℝ)
              ( leq-max-leq-leq-ℝ _ _ _
                ( transitive-leq-ℝ _ _ _
                  ( leq-left-add-real-ℚ⁺ yℝ ε)
                  ( a≤y))
                ( chain-of-inequalities
                  xℝ -ℝ real-ℚ⁺ ε'
                  ≤ xℝ -ℝ real-ℚ⁺ ε''
                    by
                      reverses-leq-left-diff-ℝ
                        ( xℝ)
                        ( preserves-leq-real-ℚ
                          ( leq-left-min-ℚ _ _))
                  ≤ yℝ
                    by leq-le-ℝ x-ε''<y
                  ≤ yℝ +ℝ real-ℚ⁺ ε
                    by leq-left-add-real-ℚ⁺ yℝ ε))
              ( leq-transpose-left-diff-ℝ _ _ _
                ( chain-of-inequalities
                  yℝ -ℝ real-ℚ⁺ ε
                  ≤ yℝ -ℝ (real-ℚ⁺ (ε' +ℚ⁺ ε'))
                    by
                      reverses-leq-left-diff-ℝ
                        ( yℝ)
                        ( leq-le-ℝ
                          ( preserves-le-real-ℚ ε'+ε'<ε))
                  ≤ yℝ -ℝ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                    by
                      leq-eq-ℝ
                        ( ap-diff-ℝ refl (inv (add-real-ℚ _ _)))
                  ≤ (yℝ -ℝ real-ℚ⁺ ε') -ℝ real-ℚ⁺ ε'
                    by
                      leq-eq-ℝ
                        ( inv (associative-diff-ℝ _ _ _))
                  ≤ (yℝ -ℝ real-ℚ⁺ ε'') -ℝ real-ℚ⁺ ε'
                    by
                      preserves-leq-right-add-ℝ _ _ _
                        ( reverses-leq-left-diff-ℝ
                          ( yℝ)
                          ( preserves-leq-real-ℚ
                            ( leq-left-min-ℚ _ _)))
                  ≤ xℝ -ℝ real-ℚ⁺ ε'
                    by
                      preserves-leq-right-add-ℝ _ _ _
                        ( leq-le-ℝ y-ε''<x)
                  ≤ z
                    by leq-right-max-ℝ _ _)))

    exists-element-apart-from-both-in-neighborhood-bound-diff-le-upper-bound-proper-closed-interval-ℝ :
      (δ ε' : ℚ⁺) →
      le-ℝ (pr1 x +ℝ real-ℚ⁺ δ) (upper-bound-proper-closed-interval-ℝ [a,b]) →
      le-ℚ⁺ (ε' +ℚ⁺ ε') ε →
      le-ℝ (pr1 x -ℝ pr1 y) (real-ℚ⁺ (min-ℚ⁺ ε' δ)) →
      le-ℝ (pr1 y -ℝ pr1 x) (real-ℚ⁺ (min-ℚ⁺ ε' δ)) →
      exists
        ( type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( λ z →
          apart-prop-ℝ (pr1 z) (pr1 x) ∧
          apart-prop-ℝ (pr1 z) (pr1 y) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 x) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 y))
    exists-element-apart-from-both-in-neighborhood-bound-diff-le-upper-bound-proper-closed-interval-ℝ
      δ ε' x+δ<b ε'+ε'<ε x-y<ε'' y-x<ε'' =
      let
        (xℝ , a≤x , x≤b) = x
        (yℝ , a≤y , y≤b) = y
        (a , b , a<b) = [a,b]
        x<b = transitive-le-ℝ _ _ _ x+δ<b (le-left-add-real-ℚ⁺ xℝ δ)
        ε'' = min-ℚ⁺ ε' δ
        z = min-ℝ b (xℝ +ℝ real-ℚ⁺ ε')
        x<y+ε'' = le-transpose-left-diff-ℝ' _ _ _ x-y<ε''
        y<x+ε'' = le-transpose-left-diff-ℝ' _ _ _ y-x<ε''
        ε'<ε = transitive-le-ℚ⁺ ε' (ε' +ℚ⁺ ε') ε ε'+ε'<ε (le-right-add-ℚ⁺ ε' ε')
        x<z =
          le-min-le-le-ℝ
            ( x<b)
            ( le-left-add-real-ℚ⁺ xℝ ε')
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        intro-exists
          ( z ,
            transitive-leq-ℝ a xℝ z (leq-le-ℝ x<z) a≤x ,
            leq-left-min-ℝ _ _)
          ( apart-le-ℝ' x<z ,
            symmetric-apart-ℝ
              ( apart-min-apart-ℝ
                ( apart-le-ℝ
                  ( transitive-le-ℝ _ _ _
                    ( x+δ<b)
                    ( concatenate-le-leq-ℝ _ _ _
                      ( y<x+ε'')
                      ( preserves-leq-left-add-ℝ _ _ _
                        ( preserves-leq-real-ℚ (leq-right-min-ℚ _ _))))))
                ( apart-le-ℝ
                  ( concatenate-le-leq-ℝ _ _ _
                    ( y<x+ε'')
                    ( preserves-leq-left-add-ℝ _ _ _
                      ( preserves-leq-real-ℚ (leq-left-min-ℚ _ _)))))) ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( z)
              ( xℝ)
              ( chain-of-inequalities
                z
                ≤ xℝ +ℝ real-ℚ⁺ ε'
                  by leq-right-min-ℝ _ _
                ≤ xℝ +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-left-add-ℝ _ _ _
                      ( leq-le-ℝ (preserves-le-real-ℚ ε'<ε)))
              ( transitive-leq-ℝ _ _ _
                ( leq-left-add-real-ℚ⁺ z ε)
                ( leq-le-ℝ x<z)) ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( z)
              ( yℝ)
              ( chain-of-inequalities
                z
                ≤ xℝ +ℝ real-ℚ⁺ ε'
                  by leq-right-min-ℝ _ _
                ≤ (yℝ +ℝ real-ℚ⁺ ε'') +ℝ real-ℚ⁺ ε'
                  by preserves-leq-right-add-ℝ _ _ _ (leq-le-ℝ x<y+ε'')
                ≤ (yℝ +ℝ real-ℚ⁺ ε') +ℝ real-ℚ⁺ ε'
                  by
                    preserves-leq-right-add-ℝ _ _ _
                      ( preserves-leq-left-add-ℝ _ _ _
                        ( preserves-leq-real-ℚ (leq-left-min-ℚ _ _)))
                ≤ yℝ +ℝ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                  by leq-eq-ℝ (associative-add-ℝ _ _ _)
                ≤ yℝ +ℝ real-ℚ⁺ (ε' +ℚ⁺ ε')
                  by leq-eq-ℝ (ap-add-ℝ refl (add-real-ℚ _ _))
                ≤ yℝ +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-left-add-ℝ _ _ _
                      ( leq-le-ℝ (preserves-le-real-ℚ ε'+ε'<ε)))
              ( chain-of-inequalities
                yℝ
                ≤ xℝ +ℝ real-ℚ⁺ ε''
                  by leq-le-ℝ y<x+ε''
                ≤ z +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-add-ℝ
                      ( leq-le-ℝ x<z)
                      ( preserves-leq-real-ℚ
                        ( transitive-leq-ℚ _ _ _
                          ( leq-le-ℚ ε'<ε)
                          ( leq-left-min-ℚ _ _)))))

module _
  {l1 l2 : Level}
  (l3 : Level)
  ([a,b] : proper-closed-interval-ℝ l1 l2)
  (x y : type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
  (ε : ℚ⁺)
  (Nεxy : neighborhood-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 x) (pr1 y))
  where

  abstract
    exists-element-apart-from-both-in-neighborhood-proper-closed-interval-ℝ :
      exists
        ( type-proper-closed-interval-ℝ (l1 ⊔ l2 ⊔ l3) [a,b])
        ( λ z →
          apart-prop-ℝ (pr1 z) (pr1 x) ∧
          apart-prop-ℝ (pr1 z) (pr1 y) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 x) ∧
          neighborhood-prop-ℝ (l1 ⊔ l2 ⊔ l3) ε (pr1 z) (pr1 y))
    exists-element-apart-from-both-in-neighborhood-proper-closed-interval-ℝ =
      let
        l123 = l1 ⊔ l2 ⊔ l3
        (xℝ , a≤x , x≤b) = x
        (yℝ , a≤y , y≤b) = y
        (a , b , a<b) = [a,b]
        motive =
          ∃ ( type-proper-closed-interval-ℝ l123 [a,b])
            ( λ z →
              apart-prop-ℝ (pr1 z) (pr1 x) ∧
              apart-prop-ℝ (pr1 z) (pr1 y) ∧
              neighborhood-prop-ℝ l123 ε (pr1 z) (pr1 x) ∧
              neighborhood-prop-ℝ l123 ε (pr1 z) (pr1 y))
        open do-syntax-trunc-Prop motive
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        (ε' , ε'+ε'<ε) = bound-double-le-ℚ⁺ ε
        case-y<x : le-ℝ yℝ xℝ → type-Prop motive
        case-y<x y<x =
          map-tot-exists
            ( λ z (z#y , z#x , Nzy , Nzx) →
              ( z#x , z#y , Nzx , Nzy))
            ( exists-element-apart-from-both-in-neighborhood-le-proper-closed-interval-ℝ
              ( l3)
              ( [a,b])
              ( y)
              ( x)
              ( ε)
              ( is-symmetric-neighborhood-ℝ ε xℝ yℝ Nεxy)
              ( y<x))
        case-x<y : le-ℝ xℝ yℝ → type-Prop motive
        case-x<y =
          exists-element-apart-from-both-in-neighborhood-le-proper-closed-interval-ℝ
            ( l3)
            ( [a,b])
            ( x)
            ( y)
            ( ε)
            ( Nεxy)
      in
        elim-disjunction
          ( motive)
          ( λ a<x →
            do
              (δ , a+δ<x) ← exists-positive-rational-separation-le-ℝ a<x
              let ε'' = min-ℚ⁺ ε' δ
              elim-disjunction
                ( motive)
                ( λ 0<x-y → case-y<x (le-is-positive-diff-ℝ 0<x-y))
                ( λ x-y<ε'' →
                  elim-disjunction
                    ( motive)
                    ( λ 0<y-x → case-x<y (le-is-positive-diff-ℝ 0<y-x))
                    ( exists-element-apart-from-both-in-neighborhood-bound-diff-le-lower-bound-proper-closed-interval-ℝ
                      ( l3)
                      ( [a,b])
                      ( x)
                      ( y)
                      ( ε)
                      ( Nεxy)
                      ( δ)
                      ( ε')
                      ( a+δ<x)
                      ( ε'+ε'<ε)
                      ( x-y<ε''))
                    ( cotransitive-le-ℝ _ _
                      ( yℝ -ℝ xℝ)
                      ( is-positive-real-ℚ⁺ ε'')))
                ( cotransitive-le-ℝ _ _ (xℝ -ℝ yℝ) (is-positive-real-ℚ⁺ ε'')))
          ( λ x<b →
            do
              (δ , x+δ<b) ← exists-positive-rational-separation-le-ℝ x<b
              let ε'' = min-ℚ⁺ ε' δ
              elim-disjunction
                ( motive)
                ( λ 0<x-y → case-y<x (le-is-positive-diff-ℝ 0<x-y))
                ( λ x-y<ε'' →
                  elim-disjunction
                    ( motive)
                    ( λ 0<y-x → case-x<y (le-is-positive-diff-ℝ 0<y-x))
                    ( exists-element-apart-from-both-in-neighborhood-bound-diff-le-upper-bound-proper-closed-interval-ℝ
                        ( l3)
                        ( [a,b])
                        ( x)
                        ( y)
                        ( ε)
                        ( Nεxy)
                        ( δ)
                        ( ε')
                        ( x+δ<b)
                        ( ε'+ε'<ε)
                        ( x-y<ε''))
                    ( cotransitive-le-ℝ _ _
                      ( yℝ -ℝ xℝ)
                      ( is-positive-real-ℚ⁺ ε'')))
                ( cotransitive-le-ℝ _ _ (xℝ -ℝ yℝ) (is-positive-real-ℚ⁺ ε'')))
          ( cotransitive-le-ℝ a b xℝ a<b)
```
