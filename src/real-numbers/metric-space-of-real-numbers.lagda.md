# The metric space of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-cartesian-products-of-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.extensional-premetric-structures
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.premetric-spaces
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.saturated-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The type of [real numbers](real-numbers.dedekind-real-numbers.md) equipped with
the [premetric](metric-spaces.premetric-structures.md) where `x y : ℝ` are
`d`-neighbors when for any `r : ℚ` the following two conditions hold:

- if `r + d` is in the lower cut of `y`, `r` is in the lower cut of `x`
- if `r + d` is in the lower cut of `x`, `r` is in the lower cut of `y`

is a [saturated metric space](metric-spaces.saturated-metric-spaces.md). It is
the
{{#concept "standard metric space of real numbers" Agda=metric-space-leq-ℝ}}.

## Definitions

### The standard premetric on the real numbers

```agda
module _
  {l : Level} (d : ℚ⁺) (x y : ℝ l)
  where

  is-in-lower-neighborhood-leq-prop-ℝ : Prop l
  is-in-lower-neighborhood-leq-prop-ℝ =
    Π-Prop
      ( ℚ)
      ( λ r →
        hom-Prop
          ( lower-cut-ℝ y (r +ℚ (rational-ℚ⁺ d)))
            ( lower-cut-ℝ x r))

  is-in-lower-neighborhood-leq-ℝ : UU l
  is-in-lower-neighborhood-leq-ℝ =
    type-Prop is-in-lower-neighborhood-leq-prop-ℝ

premetric-leq-ℝ : (l : Level) → Premetric l (ℝ l)
premetric-leq-ℝ l d x y =
  product-Prop
    ( is-in-lower-neighborhood-leq-prop-ℝ d x y)
    ( is-in-lower-neighborhood-leq-prop-ℝ d y x)

is-in-neighborhood-leq-ℝ : (l : Level) → ℚ⁺ → Relation l (ℝ l)
is-in-neighborhood-leq-ℝ l d x y = type-Prop (premetric-leq-ℝ l d x y)
```

## Properties

### `x` is in a `d`-neighborhood of `y` if and only if `x - d ≤ y ≤ x + d`

```agda
is-in-lower-neighborhood-real-bound-leq-ℝ :
  {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
  leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d)) →
  is-in-lower-neighborhood-leq-ℝ d x y
is-in-lower-neighborhood-real-bound-leq-ℝ d⁺@(d , _) x y y≤x+d q q+d<y =
  is-in-lower-cut-le-real-ℚ
    ( q)
    ( x)
    ( concatenate-le-leq-ℝ
      ( real-ℚ q)
      ( y -ℝ real-ℚ d)
      ( x)
      ( le-transpose-left-add-ℝ
        ( real-ℚ q)
        ( real-ℚ d) y
        ( inv-tr
          ( λ z → le-ℝ z y)
          ( add-real-ℚ q d)
          ( le-real-is-in-lower-cut-ℚ (q +ℚ d) y q+d<y)))
      ( leq-transpose-right-add-ℝ y x (real-ℚ d) y≤x+d))

real-bound-is-in-lower-neighborhhod-leq-ℝ :
  {l : Level} → (d : ℚ⁺) (x y : ℝ l) →
  is-in-lower-neighborhood-leq-ℝ d x y →
  leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d))
real-bound-is-in-lower-neighborhhod-leq-ℝ d⁺@(d , _) x y H r I =
  is-in-lower-cut-le-real-ℚ
    ( r)
    ( x +ℝ real-ℚ d)
    ( le-transpose-left-diff-ℝ
      ( real-ℚ r)
      ( real-ℚ d)
      ( x)
      ( inv-tr
        ( λ z → le-ℝ z x)
        ( diff-real-ℚ r d)
        ( le-real-is-in-lower-cut-ℚ
          ( r -ℚ d)
          ( x)
          ( H
            ( r -ℚ d)
            ( inv-tr
              ( is-in-lower-cut-ℝ y)
              ( ( associative-add-ℚ
                  ( r)
                  ( neg-ℚ d)
                  ( d)) ∙
                ( ap
                  ( add-ℚ r)
                  ( left-inverse-law-add-ℚ d)) ∙
                ( right-unit-law-add-ℚ r))
            ( I))))))

module _
  {l : Level} (d : ℚ⁺) (x y : ℝ l)
  where

  neighborhood-real-bound-each-leq-ℝ :
    leq-ℝ x (y +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d)) →
    is-in-neighborhood-leq-ℝ l d x y
  neighborhood-real-bound-each-leq-ℝ x≤y+d y≤x+d =
    ( is-in-lower-neighborhood-real-bound-leq-ℝ d x y y≤x+d ,
      is-in-lower-neighborhood-real-bound-leq-ℝ d y x x≤y+d)

  left-real-bound-neighborhood-leq-ℝ :
    is-in-neighborhood-leq-ℝ l d x y →
    leq-ℝ x (y +ℝ real-ℚ (rational-ℚ⁺ d))
  left-real-bound-neighborhood-leq-ℝ (_ , K) =
    real-bound-is-in-lower-neighborhhod-leq-ℝ d y x K

  right-real-bound-neighborhood-leq-ℝ :
    is-in-neighborhood-leq-ℝ l d x y →
    leq-ℝ y (x +ℝ real-ℚ (rational-ℚ⁺ d))
  right-real-bound-neighborhood-leq-ℝ (H , _) =
    real-bound-is-in-lower-neighborhhod-leq-ℝ d x y H
```

### The standard premetric on the real numbers is a metric structure

The triangle inequality is the [91st](literature.100-theorems.md#91) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
is-reflexive-premetric-leq-ℝ :
  {l : Level} → is-reflexive-Premetric (premetric-leq-ℝ l)
is-reflexive-premetric-leq-ℝ d x =
  diagonal-product
    ( (r : ℚ) →
      is-in-lower-cut-ℝ x (r +ℚ (rational-ℚ⁺ d)) → is-in-lower-cut-ℝ x r)
    ( λ r →
      le-lower-cut-ℝ x r (r +ℚ rational-ℚ⁺ d) (le-right-add-rational-ℚ⁺ r d))

is-symmetric-premetric-leq-ℝ :
  {l : Level} → is-symmetric-Premetric (premetric-leq-ℝ l)
is-symmetric-premetric-leq-ℝ d x y (H , K) = (K , H)

is-tight-premetric-leq-ℝ : {l : Level} → is-tight-Premetric (premetric-leq-ℝ l)
is-tight-premetric-leq-ℝ x y H =
  eq-eq-lower-cut-ℝ
    ( x)
    ( y)
    ( antisymmetric-leq-subtype
      ( lower-cut-ℝ x)
      ( lower-cut-ℝ y)
      ( λ r Lxr →
        elim-exists
          ( lower-cut-ℝ y r)
          ( λ s (r<s , Lxs) →
            pr2
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ x u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lxs)))
          ( forward-implication (is-rounded-lower-cut-ℝ x r) Lxr))
      ( λ r Lyr →
        elim-exists
          ( lower-cut-ℝ x r)
          ( λ s (r<s , Lys) →
            pr1
              ( H (positive-diff-le-ℚ r s r<s))
              ( r)
              ( inv-tr
                ( λ u → is-in-lower-cut-ℝ y u)
                ( right-law-positive-diff-le-ℚ r s r<s)
                ( Lys)))
          ( forward-implication (is-rounded-lower-cut-ℝ y r) Lyr)))

is-local-premetric-leq-ℝ : {l : Level} → is-local-Premetric (premetric-leq-ℝ l)
is-local-premetric-leq-ℝ {l} =
  is-local-is-tight-Premetric
    ( premetric-leq-ℝ l)
    ( is-tight-premetric-leq-ℝ)

is-triangular-premetric-leq-ℝ :
  {l : Level} → is-triangular-Premetric (premetric-leq-ℝ l)
pr1 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr1 Hxy r ∘
  pr1 Hyz (r +ℚ rational-ℚ⁺ dxy) ∘
  inv-tr
    ( is-in-lower-cut-ℝ z)
    ( associative-add-ℚ r (rational-ℚ⁺ dxy) (rational-ℚ⁺ dyz))
pr2 (is-triangular-premetric-leq-ℝ x y z dxy dyz Hyz Hxy) r =
  pr2 Hyz r ∘
  pr2 Hxy (r +ℚ rational-ℚ⁺ dyz) ∘
  inv-tr
    ( is-in-lower-cut-ℝ x)
    ( associative-add-ℚ r (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy) ∙
      ap (add-ℚ r) (commutative-add-ℚ (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy)))

is-pseudometric-premetric-leq-ℝ :
  {l : Level} → is-pseudometric-Premetric (premetric-leq-ℝ l)
is-pseudometric-premetric-leq-ℝ =
  is-reflexive-premetric-leq-ℝ ,
  is-symmetric-premetric-leq-ℝ ,
  is-triangular-premetric-leq-ℝ

is-metric-premetric-leq-ℝ :
  {l : Level} → is-metric-Premetric (premetric-leq-ℝ l)
pr1 is-metric-premetric-leq-ℝ = is-pseudometric-premetric-leq-ℝ
pr2 is-metric-premetric-leq-ℝ = is-local-premetric-leq-ℝ
```

### The standard saturated metric space of real numbers

```agda
module _
  (l : Level)
  where

  premetric-space-leq-ℝ : Premetric-Space (lsuc l) l
  premetric-space-leq-ℝ = ℝ l , premetric-leq-ℝ l

  metric-space-leq-ℝ : Metric-Space (lsuc l) l
  pr1 metric-space-leq-ℝ = premetric-space-leq-ℝ
  pr2 metric-space-leq-ℝ = is-metric-premetric-leq-ℝ
```

## Properties

### The standard metric space of real numbers is saturated

```agda
module _
  {l : Level} (x y : ℝ l) (ε : ℚ⁺)
  (H : (δ : ℚ⁺) → is-in-lower-neighborhood-leq-ℝ (ε +ℚ⁺ δ) x y)
  where

  is-closed-lower-neighborhood-leq-ℝ :
    is-in-lower-neighborhood-leq-ℝ ε x y
  is-closed-lower-neighborhood-leq-ℝ r I =
    elim-exists
      ( lower-cut-ℝ x r)
      ( λ r' (K , I') →
        H ( positive-diff-le-ℚ (r +ℚ rational-ℚ⁺ ε) r' K)
          ( r)
          ( tr
            ( is-in-lower-cut-ℝ y)
            ( ( inv
                ( right-law-positive-diff-le-ℚ
                  ( r +ℚ rational-ℚ⁺ ε)
                  ( r')
                  ( K))) ∙
              ( associative-add-ℚ
                ( r)
                ( rational-ℚ⁺ ε)
                    ( r' -ℚ (r +ℚ rational-ℚ⁺ ε))))
            ( I')))
      ( forward-implication
        ( is-rounded-lower-cut-ℝ y (r +ℚ rational-ℚ⁺ ε)) I)
```

```agda
module _
  {l : Level}
  where

  is-saturated-metric-space-leq-ℝ :
    is-saturated-Metric-Space (metric-space-leq-ℝ l)
  is-saturated-metric-space-leq-ℝ ε x y H =
    ( is-closed-lower-neighborhood-leq-ℝ x y ε (pr1 ∘ H)) ,
    ( is-closed-lower-neighborhood-leq-ℝ y x ε (pr2 ∘ H))
```

### The canonical embedding from rational to real numbers is an isometry between metric spaces

```agda
is-isometry-metric-space-leq-real-ℚ :
  is-isometry-Metric-Space
    ( metric-space-leq-ℚ)
    ( metric-space-leq-ℝ lzero)
    ( real-ℚ)
is-isometry-metric-space-leq-real-ℚ d x y =
  pair
    ( map-product
      ( le-le-add-positive-leq-add-positive-ℚ x y d)
      ( le-le-add-positive-leq-add-positive-ℚ y x d))
    ( map-product
      ( leq-add-positive-le-le-add-positive-ℚ x y d)
      ( leq-add-positive-le-le-add-positive-ℚ y x d))
```

## References

{{#bibliography}}
