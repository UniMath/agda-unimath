# The metric space of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.metric-space-of-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
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

open import metric-spaces.extensionality-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-rational-numbers
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.reflexive-rational-neighborhood-relations
open import metric-spaces.saturated-rational-neighborhood-relations
open import metric-spaces.symmetric-rational-neighborhood-relations
open import metric-spaces.triangular-rational-neighborhood-relations

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.transposition-addition-subtraction-cuts-dedekind-real-numbers
```

</details>

## Idea

The {{#concept "standard metric space of real numbers" Agda=metric-space-ℝ}} is
the [metric space](metric-spaces.metric-spaces.md) with carrier type
[`ℝ`](real-numbers.dedekind-real-numbers.md) and the
[rational neighborhood relation](metric-spaces.rational-neighborhood-relations.md)
where `x y : ℝ` are `d`-neighbors when for any `r : ℚ` the following two
conditions hold:

- if `r + d` is in the lower cut of `y`, `r` is in the lower cut of `x`
- if `r + d` is in the lower cut of `x`, `r` is in the lower cut of `y`

## Definitions

### The standard neighborhood relation on the real numbers

```agda
module _
  {l : Level} (d : ℚ⁺) (x y : ℝ l)
  where

  lower-neighborhood-prop-ℝ : Prop l
  lower-neighborhood-prop-ℝ =
    Π-Prop
      ( ℚ)
      ( λ r →
        hom-Prop
          ( lower-cut-ℝ y (r +ℚ (rational-ℚ⁺ d)))
            ( lower-cut-ℝ x r))

  lower-neighborhood-ℝ : UU l
  lower-neighborhood-ℝ =
    type-Prop lower-neighborhood-prop-ℝ

  is-prop-lower-neighborhood-ℝ : is-prop lower-neighborhood-ℝ
  is-prop-lower-neighborhood-ℝ = is-prop-type-Prop lower-neighborhood-prop-ℝ

opaque
  neighborhood-ℝ : (l : Level) → ℚ⁺ → Relation l (ℝ l)
  neighborhood-ℝ l d x y =
    lower-neighborhood-ℝ d x y × lower-neighborhood-ℝ d y x

  is-prop-neighborhood-ℝ :
    (l : Level) → (ε : ℚ⁺) (x y : ℝ l) → is-prop (neighborhood-ℝ l ε x y)
  is-prop-neighborhood-ℝ l ε x y =
    is-prop-product
      ( is-prop-lower-neighborhood-ℝ ε x y)
      ( is-prop-lower-neighborhood-ℝ ε y x)

neighborhood-prop-ℝ : (l : Level) → Rational-Neighborhood-Relation l (ℝ l)
neighborhood-prop-ℝ l d x y =
  ( neighborhood-ℝ l d x y , is-prop-neighborhood-ℝ l d x y)
```

## Properties

### The standard rational neighborhood relation on the real numbers is a metric structure

The triangle inequality is the [91st](literature.100-theorems.md#91) theorem on
[Freek Wiedijk](http://www.cs.ru.nl/F.Wiedijk/)'s list of
[100 theorems](literature.100-theorems.md) {{#cite 100theorems}}.

```agda
module _
  {l : Level}
  where

  opaque
    unfolding neighborhood-ℝ

    is-reflexive-neighborhood-ℝ :
      is-reflexive-Rational-Neighborhood-Relation (neighborhood-prop-ℝ l)
    is-reflexive-neighborhood-ℝ d x =
      diagonal-product
        ( (r : ℚ) →
          is-in-lower-cut-ℝ x (r +ℚ (rational-ℚ⁺ d)) → is-in-lower-cut-ℝ x r)
        ( λ r → le-lower-cut-ℝ x (le-right-add-rational-ℚ⁺ r d))

    is-symmetric-neighborhood-ℝ :
      is-symmetric-Rational-Neighborhood-Relation (neighborhood-prop-ℝ l)
    is-symmetric-neighborhood-ℝ d x y (H , K) = (K , H)

    is-triangular-neighborhood-ℝ :
      is-triangular-Rational-Neighborhood-Relation (neighborhood-prop-ℝ l)
    pr1 (is-triangular-neighborhood-ℝ x y z dxy dyz Hyz Hxy) r =
      pr1 Hxy r ∘
      pr1 Hyz (r +ℚ rational-ℚ⁺ dxy) ∘
      inv-tr
        ( is-in-lower-cut-ℝ z)
        ( associative-add-ℚ r (rational-ℚ⁺ dxy) (rational-ℚ⁺ dyz))
    pr2 (is-triangular-neighborhood-ℝ x y z dxy dyz Hyz Hxy) r =
      pr2 Hyz r ∘
      pr2 Hxy (r +ℚ rational-ℚ⁺ dyz) ∘
      inv-tr
        ( is-in-lower-cut-ℝ x)
        ( associative-add-ℚ r (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy) ∙
          ap (add-ℚ r) (commutative-add-ℚ (rational-ℚ⁺ dyz) (rational-ℚ⁺ dxy)))

    is-saturated-neighborhood-ℝ :
      is-saturated-Rational-Neighborhood-Relation (neighborhood-prop-ℝ l)
    is-saturated-neighborhood-ℝ ε x y H =
      ( is-closed-lower-neighborhood-ℝ x y ε (pr1 ∘ H) ,
        is-closed-lower-neighborhood-ℝ y x ε (pr2 ∘ H))
      where

      is-closed-lower-neighborhood-ℝ :
        (x y : ℝ l) (ε : ℚ⁺) →
        ((δ : ℚ⁺) → lower-neighborhood-ℝ (ε +ℚ⁺ δ) x y) →
        lower-neighborhood-ℝ ε x y
      is-closed-lower-neighborhood-ℝ x y ε H r I =
        elim-exists
          ( lower-cut-ℝ x r)
          ( λ r' (K , I') →
            H ( positive-diff-le-ℚ K)
              ( r)
              ( tr
                ( is-in-lower-cut-ℝ y)
                ( ( inv (right-law-positive-diff-le-ℚ K)) ∙
                  ( associative-add-ℚ
                    ( r)
                    ( rational-ℚ⁺ ε)
                        ( r' -ℚ (r +ℚ rational-ℚ⁺ ε))))
                ( I')))
          ( forward-implication
            ( is-rounded-lower-cut-ℝ y (r +ℚ rational-ℚ⁺ ε)) I)

module _
  (l : Level)
  where

  pseudometric-space-ℝ : Pseudometric-Space (lsuc l) l
  pseudometric-space-ℝ =
    ( ℝ l ,
      neighborhood-prop-ℝ l ,
      is-reflexive-neighborhood-ℝ ,
      is-symmetric-neighborhood-ℝ ,
      is-triangular-neighborhood-ℝ ,
      is-saturated-neighborhood-ℝ)

module _
  {l : Level}
  where

  opaque
    unfolding neighborhood-ℝ

    is-tight-pseudometric-space-ℝ :
      is-tight-Pseudometric-Space (pseudometric-space-ℝ l)
    is-tight-pseudometric-space-ℝ x y H =
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
                  ( H (positive-diff-le-ℚ r<s))
                  ( r)
                  ( inv-tr
                    ( λ u → is-in-lower-cut-ℝ x u)
                    ( right-law-positive-diff-le-ℚ r<s)
                    ( Lxs)))
              ( forward-implication (is-rounded-lower-cut-ℝ x r) Lxr))
          ( λ r Lyr →
            elim-exists
              ( lower-cut-ℝ x r)
              ( λ s (r<s , Lys) →
                pr1
                  ( H (positive-diff-le-ℚ r<s))
                  ( r)
                  ( inv-tr
                    ( λ u → is-in-lower-cut-ℝ y u)
                    ( right-law-positive-diff-le-ℚ r<s)
                    ( Lys)))
              ( forward-implication (is-rounded-lower-cut-ℝ y r) Lyr)))

  is-extensional-pseudometric-space-ℝ :
    is-extensional-Pseudometric-Space (pseudometric-space-ℝ l)
  is-extensional-pseudometric-space-ℝ =
    is-extensional-is-tight-Pseudometric-Space
      (pseudometric-space-ℝ l)
      (is-tight-pseudometric-space-ℝ)
```

### The standard metric space of real numbers

```agda
module _
  (l : Level)
  where

  metric-space-ℝ : Metric-Space (lsuc l) l
  metric-space-ℝ =
    make-Metric-Space
      ( ℝ l)
      ( neighborhood-prop-ℝ l)
      ( is-reflexive-neighborhood-ℝ)
      ( is-symmetric-neighborhood-ℝ)
      ( is-triangular-neighborhood-ℝ)
      ( is-saturated-neighborhood-ℝ)
      ( is-extensional-pseudometric-space-ℝ)
```

## Properties

### The element `x` is in a `d`-neighborhood of `y` if and only if `x ≤ y + d` and `y ≤ x + d`

```agda
module _
  {l : Level}
  where

  abstract
    lower-neighborhood-real-bound-leq-ℝ :
      (d : ℚ⁺) (x y : ℝ l) →
      leq-ℝ y (x +ℝ real-ℚ⁺ d) →
      lower-neighborhood-ℝ d x y
    lower-neighborhood-real-bound-leq-ℝ (d , _) x y y≤x+d q q+d<y =
      is-in-lower-cut-le-real-ℚ
        ( x)
        ( concatenate-le-leq-ℝ
          ( real-ℚ q)
          ( y -ℝ real-ℚ d)
          ( x)
          ( le-transpose-left-add-ℝ
            ( real-ℚ q)
            ( real-ℚ d)
            ( y)
            ( inv-tr
              ( λ z → le-ℝ z y)
              ( add-real-ℚ q d)
              ( le-real-is-in-lower-cut-ℝ y q+d<y)))
          ( leq-transpose-right-add-ℝ y x (real-ℚ d) y≤x+d))

  opaque
    unfolding leq-ℝ

    real-bound-leq-lower-neighborhood-ℝ :
      (d : ℚ⁺) (x y : ℝ l) →
      lower-neighborhood-ℝ d x y →
      leq-ℝ y (x +ℝ real-ℚ⁺ d)
    real-bound-leq-lower-neighborhood-ℝ (d , _) x y H r =
      ( transpose-diff-is-in-lower-cut-ℝ x r d) ∘
      ( H (r -ℚ d)) ∘
      ( inv-tr
        ( is-in-lower-cut-ℝ y)
        ( ( associative-add-ℚ r (neg-ℚ d) d) ∙
          ( ap (add-ℚ r) (left-inverse-law-add-ℚ d)) ∙
          ( right-unit-law-add-ℚ r)))

module _
  {l : Level} (d : ℚ⁺) (x y : ℝ l)
  where

  opaque
    unfolding neighborhood-ℝ

    neighborhood-real-bound-each-leq-ℝ :
      leq-ℝ x (y +ℝ real-ℚ⁺ d) →
      leq-ℝ y (x +ℝ real-ℚ⁺ d) →
      neighborhood-ℝ l d x y
    neighborhood-real-bound-each-leq-ℝ x≤y+d y≤x+d =
      ( lower-neighborhood-real-bound-leq-ℝ d x y y≤x+d) ,
      ( lower-neighborhood-real-bound-leq-ℝ d y x x≤y+d)

    left-leq-real-bound-neighborhood-ℝ :
      neighborhood-ℝ l d x y → leq-ℝ x (y +ℝ real-ℚ⁺ d)
    left-leq-real-bound-neighborhood-ℝ (_ , K) =
      real-bound-leq-lower-neighborhood-ℝ d y x K

    right-leq-real-bound-neighborhood-ℝ :
      neighborhood-ℝ l d x y → leq-ℝ y (x +ℝ real-ℚ⁺ d)
    right-leq-real-bound-neighborhood-ℝ (H , _) =
      real-bound-leq-lower-neighborhood-ℝ d x y H
```

### `x + real-ℚ⁺ d` is in a `d`-neighborhood of `x`

```agda
abstract
  neighborhood-right-add-real-ℚ⁺ :
    {l : Level} (x : ℝ l) (d : ℚ⁺) →
    neighborhood-ℝ l d x (x +ℝ real-ℚ⁺ d)
  neighborhood-right-add-real-ℚ⁺ x d =
    neighborhood-real-bound-each-leq-ℝ d _ _
      ( transitive-leq-ℝ _ _ _
        ( leq-left-add-real-ℝ⁰⁺ _ (nonnegative-real-ℚ⁺ d))
        ( leq-left-add-real-ℝ⁰⁺ _ (nonnegative-real-ℚ⁺ d)))
      ( refl-leq-ℝ _)
```

### Similarity of real numbers preserves neighborhoods

```agda
module _
  {l1 l2 : Level} (d : ℚ⁺) (x y : ℝ l1) (x' y' : ℝ l2)
  (x~x' : x ~ℝ x') (y~y' : y ~ℝ y')
  where

  preserves-neighborhood-sim-ℝ :
    neighborhood-ℝ l1 d x y → neighborhood-ℝ l2 d x' y'
  preserves-neighborhood-sim-ℝ H =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( x')
      ( y')
      ( preserves-leq-sim-ℝ
        ( x~x')
        ( preserves-sim-right-add-ℝ
          ( real-ℚ⁺ d)
          ( y)
          ( y')
          ( y~y'))
        ( left-leq-real-bound-neighborhood-ℝ d x y H))
      ( preserves-leq-sim-ℝ
        ( y~y')
        ( preserves-sim-right-add-ℝ
          ( real-ℚ⁺ d)
          ( x)
          ( x')
          ( x~x'))
        ( right-leq-real-bound-neighborhood-ℝ d x y H))
```

### The neighborhood relation on the real numbers is weakly monotonic

```agda
abstract
  weakly-monotonic-neighborhood-ℝ :
    {l : Level} (x y : ℝ l) (d₁ d₂ : ℚ⁺) → leq-ℚ⁺ d₁ d₂ →
    neighborhood-ℝ l d₁ x y → neighborhood-ℝ l d₂ x y
  weakly-monotonic-neighborhood-ℝ {l} =
    weakly-monotonic-neighborhood-Metric-Space (metric-space-ℝ l)
```

### The canonical embedding from rational to real numbers is an isometry between metric spaces

```agda
opaque
  unfolding neighborhood-ℝ real-ℚ

  is-isometry-real-ℚ :
    is-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ lzero)
      ( real-ℚ)
  is-isometry-real-ℚ d x y =
    pair
      ( map-product
        ( le-le-add-positive-leq-add-positive-ℚ x y d)
        ( le-le-add-positive-leq-add-positive-ℚ y x d))
      ( map-product
        ( leq-add-positive-le-le-add-positive-ℚ x y d)
        ( leq-add-positive-le-le-add-positive-ℚ y x d))

isometry-real-ℚ :
  isometry-Metric-Space
    ( metric-space-ℚ)
    ( metric-space-ℝ lzero)
isometry-real-ℚ =
  ( real-ℚ , is-isometry-real-ℚ)
```

### Raising real numbers is an isometry

```agda
module _
  {l0 : Level} (l : Level)
  where

  abstract
    is-isometry-raise-ℝ :
      is-isometry-Metric-Space
        ( metric-space-ℝ l0)
        ( metric-space-ℝ (l0 ⊔ l))
        ( raise-ℝ l)
    pr1 (is-isometry-raise-ℝ d x y) =
      preserves-neighborhood-sim-ℝ
        ( d)
        ( x)
        ( y)
        ( raise-ℝ l x)
        ( raise-ℝ l y)
        ( sim-raise-ℝ l x)
        ( sim-raise-ℝ l y)
    pr2 (is-isometry-raise-ℝ d x y) =
      preserves-neighborhood-sim-ℝ
        ( d)
        ( raise-ℝ l x)
        ( raise-ℝ l y)
        ( x)
        ( y)
        ( symmetric-sim-ℝ (sim-raise-ℝ l x))
        ( symmetric-sim-ℝ (sim-raise-ℝ l y))

  isometry-raise-ℝ :
    isometry-Metric-Space
      ( metric-space-ℝ l0)
      ( metric-space-ℝ (l0 ⊔ l))
  isometry-raise-ℝ =
    ( raise-ℝ l , is-isometry-raise-ℝ)
```

### Raising rational numbers to real numbers is an isometry

```agda
module _
  (l : Level)
  where

  isometry-raise-real-ℚ :
    isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ l)
  isometry-raise-real-ℚ =
    comp-isometry-Metric-Space
      ( metric-space-ℚ)
      ( metric-space-ℝ lzero)
      ( metric-space-ℝ l)
      ( isometry-raise-ℝ l)
      ( isometry-real-ℚ)

  abstract
    is-isometry-raise-real-ℚ :
      is-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ l)
        ( raise-real-ℚ l)
    is-isometry-raise-real-ℚ =
      is-isometry-map-isometry-Metric-Space
        ( metric-space-ℚ)
        ( metric-space-ℝ l)
        ( isometry-raise-real-ℚ)
```

## References

{{#bibliography}}
