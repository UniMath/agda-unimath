# Dense subsets of the real numbers

```agda
module real-numbers.dense-subsets-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.intersections-subtypes
open import foundation.propositional-truncations
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import metric-spaces.dense-subsets-metric-spaces

open import order-theory.large-posets

open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-approximates-of-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.subsets-real-numbers
```

</details>

## Idea

A {{#concept "dense subset" Disambiguation="of ℝ" Agda=dense-subset-ℝ}} of the
[real numbers](real-numbers.dedekind-real-numbers.md) `ℝ` is a
[dense subset](metric-spaces.dense-subsets-metric-spaces.md) of the
[metric space of real numbers](real-numbers.metric-space-of-real-numbers.md),
which means that it is a [subset](real-numbers.subsets-real-numbers.md) `S ⊆ ℝ`
such that for any `x : ℝ` and any
[positive rational](elementary-number-theory.positive-rational-numbers.md) `ε`,
there is a `y` in an `ε`-neighborhood of `X` that is also in `S`.

## Definition

```agda
is-dense-subset-ℝ : {l1 l2 : Level} → subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
is-dense-subset-ℝ = is-dense-subset-Metric-Space (metric-space-ℝ _)

dense-subset-ℝ : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
dense-subset-ℝ l1 l2 = dense-subset-Metric-Space l1 (metric-space-ℝ l2)

subset-dense-subset-ℝ : {l1 l2 : Level} → dense-subset-ℝ l1 l2 → subset-ℝ l1 l2
subset-dense-subset-ℝ = pr1

is-dense-subset-dense-subset-ℝ :
  {l1 l2 : Level} (S : dense-subset-ℝ l1 l2) (x : ℝ l2) (ε : ℚ⁺) →
  intersect-subtype (neighborhood-prop-ℝ l2 ε x) (subset-dense-subset-ℝ S)
is-dense-subset-dense-subset-ℝ = pr2

type-dense-subset-ℝ : {l1 l2 : Level} → dense-subset-ℝ l1 l2 → UU (l1 ⊔ lsuc l2)
type-dense-subset-ℝ S = type-subtype (subset-dense-subset-ℝ S)

inclusion-dense-subset-ℝ :
  {l1 l2 : Level} (S : dense-subset-ℝ l1 l2) →
  type-dense-subset-ℝ S → ℝ l2
inclusion-dense-subset-ℝ S = inclusion-subtype (subset-dense-subset-ℝ S)

is-in-dense-subset-ℝ : {l1 l2 : Level} → dense-subset-ℝ l1 l2 → ℝ l2 → UU l1
is-in-dense-subset-ℝ S =
  is-in-subtype (subset-dense-subset-ℝ S)
```

## Properties

### The rational reals are dense in `ℝ`

```agda
abstract
  is-dense-rational-real-ℝ :
    (l : Level) → is-dense-subset-ℝ (subtype-rational-real {l})
  is-dense-rational-real-ℝ l x ε =
    map-exists
      ( _)
      ( raise-real-ℚ l)
      ( λ q Nεxq → ( Nεxq , q , is-rational-raise-real-ℚ l q))
      ( exists-rational-approximate-ℝ x ε)

dense-subset-rational-real-ℝ :
  (l : Level) → dense-subset-ℝ l l
dense-subset-rational-real-ℝ l =
  ( subtype-rational-real , is-dense-rational-real-ℝ l)
```

### Given a dense subset `S ⊆ R`, two reals `x < y`, and positive rationals `δx`, `δy`, there are `x' < y'` with `x' ∈ S`, `y' ∈ S`, `x'` in a `δx`-neighborhood of `x` and correspondingly for `y`

```agda
module _
  {l1 l2 : Level}
  (S : dense-subset-ℝ l1 l2)
  where

  abstract
    exist-close-le-elements-dense-subset-ℝ :
      {x y : ℝ l2} (δx δy : ℚ⁺) → le-ℝ x y →
      exists
        ( type-dense-subset-ℝ S × type-dense-subset-ℝ S)
        ( λ ((x' , x'∈S) , (y' , y'∈S)) →
          ( le-prop-ℝ x' y') ∧
          ( neighborhood-prop-ℝ l2 δx x x') ∧
          ( neighborhood-prop-ℝ l2 δy y y'))
    exist-close-le-elements-dense-subset-ℝ {x} {y} δx δy x<y =
      let
        open
          do-syntax-trunc-Prop
            ( ∃
              ( type-dense-subset-ℝ S × type-dense-subset-ℝ S)
              ( λ ((x' , x'∈S) , (y' , y'∈S)) →
                ( le-prop-ℝ x' y') ∧
                ( neighborhood-prop-ℝ l2 δx x x') ∧
                ( neighborhood-prop-ℝ l2 δy y y')))
      in do
        (ε , x+ε<y) ← exists-positive-rational-separation-le-ℝ x<y
        let (εx , εy , εx+εy=ε) = split-ℚ⁺ ε
        (x' , Nxx' , x'∈S) ←
          is-dense-subset-dense-subset-ℝ S x (min-ℚ⁺ δx εx)
        (y' , Nyy' , y'∈S) ←
          is-dense-subset-dense-subset-ℝ S y (min-ℚ⁺ δy εy)
        intro-exists
          ( (x' , x'∈S) , (y' , y'∈S))
          ( concatenate-leq-le-ℝ
              ( x')
              ( x +ℝ real-ℚ⁺ εx)
              ( y')
              ( right-leq-real-bound-neighborhood-ℝ
                ( εx)
                ( x)
                ( x')
                ( weakly-monotonic-neighborhood-ℝ
                  ( x)
                  ( x')
                  ( min-ℚ⁺ δx εx)
                  ( εx)
                  ( leq-right-min-ℚ⁺ δx εx)
                  ( Nxx')))
              ( concatenate-le-leq-ℝ
                ( x +ℝ real-ℚ⁺ εx)
                ( y -ℝ real-ℚ⁺ εy)
                ( y')
                ( le-transpose-left-add-ℝ
                  ( x +ℝ real-ℚ⁺ εx)
                  ( real-ℚ⁺ εy)
                  ( y)
                  ( inv-tr
                    ( λ z → le-ℝ z y)
                    ( ( associative-add-ℝ _ _ _) ∙
                      ( ap-add-ℝ
                        ( refl)
                        ( ( add-real-ℚ _ _ ∙ ap real-ℚ⁺ εx+εy=ε))))
                    ( x+ε<y)))
                ( leq-transpose-right-add-ℝ
                  ( y)
                  ( y')
                  ( real-ℚ⁺ εy)
                  ( left-leq-real-bound-neighborhood-ℝ
                    ( εy)
                    ( y)
                    ( y')
                    ( weakly-monotonic-neighborhood-ℝ
                      ( y)
                      ( y')
                      ( min-ℚ⁺ δy εy)
                      ( εy)
                      ( leq-right-min-ℚ⁺ δy εy)
                      ( Nyy'))))) ,
            weakly-monotonic-neighborhood-ℝ
              ( x)
              ( x')
              ( min-ℚ⁺ δx εx)
              ( δx)
              ( leq-left-min-ℚ⁺ δx εx)
              ( Nxx') ,
            weakly-monotonic-neighborhood-ℝ
              ( y)
              ( y')
              ( min-ℚ⁺ δy εy)
              ( δy)
              ( leq-left-min-ℚ⁺ δy εy)
              ( Nyy'))
```

### Given a dense subset `S ⊆ ℝ`, for any `x : ℝ` and `ε : ℚ⁺` there is an element of `S` in an `ε`-neighborhood of `x` that is greater than or equal to `x`

```agda
module _
  {l1 l2 : Level}
  (S : dense-subset-ℝ l1 l2)
  (x : ℝ l2)
  where

  abstract
    is-dense-above-dense-subset-ℝ :
      (ε : ℚ⁺) →
      exists
        ( ℝ l2)
        ( λ y →
          ( leq-prop-ℝ x y) ∧
          ( subset-dense-subset-ℝ S y) ∧
          ( neighborhood-prop-ℝ l2 ε x y))
    is-dense-above-dense-subset-ℝ ε =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l2)
              ( λ y →
                ( leq-prop-ℝ x y) ∧
                ( subset-dense-subset-ℝ S y) ∧
                ( neighborhood-prop-ℝ l2 ε x y)))
      in do
        (ε' , 2ε'<ε) ← double-le-ℚ⁺ ε
        (y , N , y∈S) ←
          is-dense-subset-dense-subset-ℝ S (x +ℝ real-ℚ⁺ ε') ε'
        let
          x≤y : leq-ℝ x y
          x≤y =
            reflects-leq-right-add-ℝ
              ( real-ℚ⁺ ε')
              ( x)
              ( y)
              ( left-leq-real-bound-neighborhood-ℝ ε' (x +ℝ real-ℚ⁺ ε') y N)
        intro-exists
          ( y)
          ( x≤y ,
            y∈S ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( x)
              ( y)
              ( chain-of-inequalities
                x
                ≤ y
                  by x≤y
                ≤ y +ℝ real-ℚ⁺ ε
                  by leq-left-add-real-ℝ⁺ y (positive-real-ℚ⁺ ε))
              ( chain-of-inequalities
                y
                ≤ (x +ℝ real-ℚ⁺ ε') +ℝ real-ℚ⁺ ε'
                  by right-leq-real-bound-neighborhood-ℝ ε' _ _ N
                ≤ x +ℝ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                  by leq-eq-ℝ (associative-add-ℝ _ _ _)
                ≤ x +ℝ real-ℚ⁺ (ε' +ℚ⁺ ε')
                  by leq-eq-ℝ (ap-add-ℝ refl (add-real-ℚ _ _))
                ≤ x +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-left-add-ℝ x _ _
                      ( preserves-leq-real-ℚ (leq-le-ℚ 2ε'<ε))))
```

### Given a dense subset `S ⊆ ℝ`, for any `x : ℝ` and `ε : ℚ⁺` there is an element of `S` in an `ε`-neighborhood of `x` that is less than or equal to `x`

```agda
module _
  {l1 l2 : Level}
  (S : dense-subset-ℝ l1 l2)
  (x : ℝ l2)
  where

  abstract
    is-dense-below-dense-subset-ℝ :
      (ε : ℚ⁺) →
      exists
        ( ℝ l2)
        ( λ y →
          ( leq-prop-ℝ y x) ∧
          ( subset-dense-subset-ℝ S y) ∧
          ( neighborhood-prop-ℝ l2 ε x y))
    is-dense-below-dense-subset-ℝ ε =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l2)
              ( λ y →
                ( leq-prop-ℝ y x) ∧
                ( subset-dense-subset-ℝ S y) ∧
                ( neighborhood-prop-ℝ l2 ε x y)))
      in do
        (ε' , 2ε'<ε) ← double-le-ℚ⁺ ε
        (y , N , y∈S) ←
          is-dense-subset-dense-subset-ℝ S (x -ℝ real-ℚ⁺ ε') ε'
        let
          y≤x =
            tr
              ( leq-ℝ y)
              ( eq-sim-ℝ (cancel-right-diff-add-ℝ x (real-ℚ⁺ ε')))
              ( right-leq-real-bound-neighborhood-ℝ ε' _ _ N)
        intro-exists
          ( y)
          ( y≤x ,
            y∈S ,
            neighborhood-real-bound-each-leq-ℝ
              ( ε)
              ( x)
              ( y)
              ( chain-of-inequalities
                x
                ≤ (x -ℝ real-ℚ⁺ ε') +ℝ real-ℚ⁺ ε'
                  by
                    leq-sim-ℝ
                      ( symmetric-sim-ℝ
                        ( cancel-right-diff-add-ℝ x (real-ℚ⁺ ε')))
                ≤ (y +ℝ real-ℚ⁺ ε') +ℝ real-ℚ⁺ ε'
                  by
                    preserves-leq-right-add-ℝ
                      ( real-ℚ⁺ ε')
                      ( x -ℝ real-ℚ⁺ ε')
                      ( y +ℝ real-ℚ⁺ ε')
                      ( left-leq-real-bound-neighborhood-ℝ ε' _ _ N)
                ≤ y +ℝ (real-ℚ⁺ ε' +ℝ real-ℚ⁺ ε')
                  by leq-eq-ℝ (associative-add-ℝ _ _ _)
                ≤ y +ℝ real-ℚ⁺ (ε' +ℚ⁺ ε')
                  by leq-eq-ℝ (ap-add-ℝ refl (add-real-ℚ _ _))
                ≤ y +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-left-add-ℝ
                      ( y)
                      ( _)
                      ( _)
                      ( preserves-leq-real-ℚ (leq-le-ℚ 2ε'<ε)))
              ( chain-of-inequalities
                y
                ≤ x
                  by y≤x
                ≤ x +ℝ real-ℚ⁺ ε
                  by leq-left-add-real-ℝ⁺ x (positive-real-ℚ⁺ ε)))
```

### If `S` is dense in `ℝ` and `x < y`, then there is an `s ∈ S` with `x < s < y`

```agda
module _
  {l1 l2 : Level}
  (S : dense-subset-ℝ l1 l2)
  {x y : ℝ l2}
  (x<y : le-ℝ x y)
  where

  abstract
    dense-le-dense-subset-ℝ :
      exists
        ( ℝ l2)
        ( λ s → subset-dense-subset-ℝ S s ∧ le-prop-ℝ x s ∧ le-prop-ℝ s y)
    dense-le-dense-subset-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
        open
          do-syntax-trunc-Prop
            ( ∃
              ( ℝ l2)
              ( λ s →
                subset-dense-subset-ℝ S s ∧ le-prop-ℝ x s ∧ le-prop-ℝ s y))
      in do
        (a , x<a , a<y) ← dense-le-ℝ x y x<y
        (b , a<b , b<y) ← dense-le-ℝ a y a<y
        (ε , a+ε<b) ← exists-positive-rational-separation-le-ℝ a<b
        (c , a≤c , c∈S , Nεac) ←
          is-dense-above-dense-subset-ℝ S (raise-ℝ l2 a) ε
        intro-exists
          ( c)
          ( c∈S ,
            concatenate-le-leq-ℝ
              ( x)
              ( a)
              ( c)
              ( x<a)
              ( preserves-leq-left-sim-ℝ (sim-raise-ℝ' l2 a) a≤c) ,
            concatenate-leq-le-ℝ
              ( c)
              ( b)
              ( y)
              ( chain-of-inequalities
                c
                ≤ raise-ℝ l2 a +ℝ real-ℚ⁺ ε
                  by right-leq-real-bound-neighborhood-ℝ ε _ _ Nεac
                ≤ a +ℝ real-ℚ⁺ ε
                  by
                    preserves-leq-right-add-ℝ _ _ _
                      ( leq-sim-ℝ (sim-raise-ℝ' l2 a))
                ≤ b
                  by leq-le-ℝ a+ε<b)
              ( b<y))
```
