# Multiplicative inverses of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.binary-transport
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjoint-subtypes
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.functoriality-existential-quantification

open import order-theory.large-posets

open import real-numbers.addition-positive-and-negative-real-numbers
open import real-numbers.addition-positive-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-positive-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.invertibility-strictly-increasing-unbounded-continuous-functions-real-numbers
open import real-numbers.lipschitz-continuity-multiplication-real-numbers
open import real-numbers.multiplication-positive-and-negative-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.pointwise-continuous-functions-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-positive-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-positive-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.strictly-increasing-functions-real-numbers
open import real-numbers.unbounded-functions-real-numbers
```

</details>

## Idea

If a [real number](real-numbers.dedekind-real-numbers.md) `x` is
[positive](real-numbers.positive-real-numbers.md), then it has a
{{#concept "multiplicative inverse" Disambiguation="positive real numbers" Agda=inv-ℝ⁺}},
a unique, positive real number `y` such that the
[product](real-numbers.multiplication-real-numbers.md) of `x` and `y` is 1.

This definition is adapted from Lemma 11.2.4 of {{#cite UF13}}.

## Definition

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  abstract
    is-unbounded-above-left-mul-real-ℝ⁺ :
      is-unbounded-above-function-ℝ (mul-ℝ {l} {l} (real-ℝ⁺ x))
    is-unbounded-above-left-mul-real-ℝ⁺ q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ (ℝ l) (λ y → le-prop-ℝ (real-ℚ q) (real-ℝ⁺ x *ℝ y)))
      in do
        (p , p<x) ← exists-ℚ⁺-in-lower-cut-ℝ⁺ x
        let
          q' = max-ℝ one-ℝ (real-ℚ q)
          q'⁺ =
            ( q' ,
              is-positive-leq-ℝ⁺ one-ℝ⁺ q' (leq-left-max-ℝ one-ℝ (real-ℚ q)))
        intro-exists
          ( raise-ℝ l (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ q'))
          ( tr
            ( λ y →
              le-ℝ y (( real-ℝ⁺ x *ℝ raise-ℝ l (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ q'))))
            ( equational-reasoning
              real-ℚ⁺ p *ℝ (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ real-ℚ q)
              ＝ real-ℚ⁺ p *ℝ real-ℚ (rational-inv-ℚ⁺ p *ℚ q)
                by ap-mul-ℝ refl (mul-real-ℚ _ _)
              ＝ real-ℚ (rational-ℚ⁺ p *ℚ (rational-inv-ℚ⁺ p *ℚ q))
                by mul-real-ℚ _ _
              ＝ real-ℚ q
                by ap real-ℚ (is-section-left-div-ℚ⁺ p q))
            ( concatenate-leq-le-ℝ
              ( real-ℚ⁺ p *ℝ (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ real-ℚ q))
              ( real-ℚ⁺ p *ℝ raise-ℝ l (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ q'))
              ( real-ℝ⁺ x *ℝ raise-ℝ l (real-ℚ⁺ (inv-ℚ⁺ p) *ℝ q'))
              ( preserves-leq-left-mul-ℝ⁺
                ( positive-real-ℚ⁺ p)
                ( preserves-leq-right-raise-ℝ
                  ( l)
                  ( preserves-leq-left-mul-ℝ⁺
                    ( positive-real-ℚ⁺ (inv-ℚ⁺ p))
                    ( leq-right-max-ℝ _ _))))
              ( preserves-le-right-mul-ℝ⁺
                ( raise-ℝ⁺ l (positive-real-ℚ⁺ (inv-ℚ⁺ p) *ℝ⁺ q'⁺))
                ( le-real-is-in-lower-cut-ℝ (real-ℝ⁺ x) p<x))))

    is-unbounded-below-left-mul-real-ℝ⁺ :
      is-unbounded-below-function-ℝ (mul-ℝ {l} {l} (real-ℝ⁺ x))
    is-unbounded-below-left-mul-real-ℝ⁺ q =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ (ℝ l) (λ y → le-prop-ℝ (real-ℝ⁺ x *ℝ y) (real-ℚ q)))
      in do
        (y , -q<xy) ← is-unbounded-above-left-mul-real-ℝ⁺ (neg-ℚ q)
        intro-exists
          ( neg-ℝ y)
          ( binary-tr
            ( le-ℝ)
            ( inv (right-negative-law-mul-ℝ _ _))
            ( ap neg-ℝ (inv (neg-real-ℚ q)) ∙ neg-neg-ℝ _)
            ( neg-le-ℝ -q<xy))

    is-SIPCUB-left-mul-real-ℝ⁺ :
      is-SIPCUB-function-ℝ (mul-ℝ {l} {l} (real-ℝ⁺ x))
    is-SIPCUB-left-mul-real-ℝ⁺ =
      ( (λ _ _ → preserves-le-left-mul-ℝ⁺ x) ,
        is-pointwise-continuous-map-uniformly-continuous-function-ℝ
          ( uniformly-continuous-right-mul-ℝ l (real-ℝ⁺ x)) ,
        is-unbounded-above-left-mul-real-ℝ⁺ ,
        is-unbounded-below-left-mul-real-ℝ⁺)

  SIPCUB-function-left-mul-real-ℝ⁺ : SIPCUB-function-ℝ l l
  SIPCUB-function-left-mul-real-ℝ⁺ =
    ( mul-ℝ (real-ℝ⁺ x) , is-SIPCUB-left-mul-real-ℝ⁺)

  opaque
    real-inv-ℝ⁺ : ℝ l
    real-inv-ℝ⁺ =
      map-inv-SIPCUB-function-ℝ
        ( SIPCUB-function-left-mul-real-ℝ⁺)
        ( raise-one-ℝ l)
```

## Properties

### The multiplicative inverse is a multiplicative inverse

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  abstract opaque
    unfolding real-inv-ℝ⁺

    eq-right-inverse-law-mul-ℝ⁺ : real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x ＝ raise-one-ℝ l
    eq-right-inverse-law-mul-ℝ⁺ =
      is-section-map-inv-SIPCUB-function-ℝ
        ( SIPCUB-function-left-mul-real-ℝ⁺ x)
        ( raise-one-ℝ l)

    eq-left-inverse-law-mul-ℝ⁺ : real-inv-ℝ⁺ x *ℝ real-ℝ⁺ x ＝ raise-one-ℝ l
    eq-left-inverse-law-mul-ℝ⁺ =
      commutative-mul-ℝ _ _ ∙ eq-right-inverse-law-mul-ℝ⁺

    right-inverse-law-mul-ℝ⁺ : sim-ℝ (real-ℝ⁺ x *ℝ real-inv-ℝ⁺ x) one-ℝ
    right-inverse-law-mul-ℝ⁺ =
      inv-tr
        ( λ y → sim-ℝ y one-ℝ)
        ( eq-right-inverse-law-mul-ℝ⁺)
        ( sim-raise-ℝ' l one-ℝ)

    left-inverse-law-mul-ℝ⁺ : sim-ℝ (real-inv-ℝ⁺ x *ℝ real-ℝ⁺ x) one-ℝ
    left-inverse-law-mul-ℝ⁺ =
      tr
        ( λ y → sim-ℝ y one-ℝ)
        ( commutative-mul-ℝ _ _)
        ( right-inverse-law-mul-ℝ⁺)
```

### The multiplicative inverse of a positive real number is positive

```agda
module _
  {l : Level} (x : ℝ⁺ l)
  where

  abstract
    is-positive-inv-ℝ⁺ : is-positive-ℝ (real-inv-ℝ⁺ x)
    is-positive-inv-ℝ⁺ =
      is-positive-right-factor-is-positive-left-factor-is-positive-mul-ℝ
        ( real-ℝ⁺ x)
        ( real-inv-ℝ⁺ x)
        ( is-positive-real-ℝ⁺ x)
        ( inv-tr
          ( is-positive-ℝ)
          ( eq-right-inverse-law-mul-ℝ⁺ x)
          ( is-positive-real-ℝ⁺ (raise-one-ℝ⁺ l)))

  inv-ℝ⁺ : ℝ⁺ l
  inv-ℝ⁺ = (real-inv-ℝ⁺ x , is-positive-inv-ℝ⁺)
```

### Cancellation laws

```agda
abstract
  cancel-left-div-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) →
    sim-ℝ (real-inv-ℝ⁺ x *ℝ (real-ℝ⁺ x *ℝ y)) y
  cancel-left-div-mul-ℝ⁺ x⁺@(x , _) y =
    similarity-reasoning-ℝ
      real-inv-ℝ⁺ x⁺ *ℝ (x *ℝ y)
      ~ℝ (real-inv-ℝ⁺ x⁺ *ℝ x) *ℝ y
        by sim-eq-ℝ (inv (associative-mul-ℝ _ _ _))
      ~ℝ one-ℝ *ℝ y
        by preserves-sim-right-mul-ℝ y _ _ (left-inverse-law-mul-ℝ⁺ x⁺)
      ~ℝ y
        by sim-eq-ℝ (left-unit-law-mul-ℝ y)

  cancel-left-mul-div-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ l2) →
    sim-ℝ (real-ℝ⁺ x *ℝ (real-inv-ℝ⁺ x *ℝ y)) y
  cancel-left-mul-div-ℝ⁺ x⁺@(x , _) y =
    similarity-reasoning-ℝ
      x *ℝ (real-inv-ℝ⁺ x⁺ *ℝ y)
      ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ y
        by sim-eq-ℝ (inv (associative-mul-ℝ _ _ _))
      ~ℝ one-ℝ *ℝ y
        by preserves-sim-right-mul-ℝ y _ _ (right-inverse-law-mul-ℝ⁺ x⁺)
      ~ℝ y
        by sim-eq-ℝ (left-unit-law-mul-ℝ y)
```

### The multiplicative inverse is unique up to similarity

```agda
abstract
  unique-right-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    sim-ℝ (real-ℝ⁺ x *ℝ real-ℝ⁺ y) one-ℝ →
    sim-ℝ (real-ℝ⁺ y) (real-inv-ℝ⁺ x)
  unique-right-inv-ℝ⁺ {l1} {l2} x⁺@(x , _) y⁺@(y , _) xy~1 =
    similarity-reasoning-ℝ
      y
      ~ℝ real-inv-ℝ⁺ x⁺ *ℝ (x *ℝ y)
        by symmetric-sim-ℝ (cancel-left-div-mul-ℝ⁺ x⁺ y)
      ~ℝ real-inv-ℝ⁺ x⁺ *ℝ one-ℝ
        by preserves-sim-left-mul-ℝ _ _ _ xy~1
      ~ℝ real-inv-ℝ⁺ x⁺
        by sim-eq-ℝ (right-unit-law-mul-ℝ _)

  unique-left-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    sim-ℝ (real-ℝ⁺ x *ℝ real-ℝ⁺ y) one-ℝ →
    sim-ℝ (real-ℝ⁺ x) (real-inv-ℝ⁺ y)
  unique-left-inv-ℝ⁺ x y xy~1 =
    unique-right-inv-ℝ⁺
      ( y)
      ( x)
      ( tr (λ z → sim-ℝ z one-ℝ) (commutative-mul-ℝ _ _) xy~1)
```

### The multiplicative inverse operation preserves similarity

```agda
abstract
  preserves-sim-inv-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) → sim-ℝ⁺ x y →
    sim-ℝ⁺ (inv-ℝ⁺ x) (inv-ℝ⁺ y)
  preserves-sim-inv-ℝ⁺ x y x~y =
    unique-left-inv-ℝ⁺
      ( inv-ℝ⁺ x)
      ( y)
      ( similarity-reasoning-ℝ
        real-inv-ℝ⁺ x *ℝ real-ℝ⁺ y
        ~ℝ real-inv-ℝ⁺ x *ℝ real-ℝ⁺ x
          by preserves-sim-left-mul-ℝ _ _ _ (symmetric-sim-ℝ x~y)
        ~ℝ one-ℝ
          by left-inverse-law-mul-ℝ⁺ x)
```

### The multiplicative inverse is distributive over multiplication

```agda
abstract
  distributive-real-inv-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    real-inv-ℝ⁺ (x *ℝ⁺ y) ＝ real-inv-ℝ⁺ x *ℝ real-inv-ℝ⁺ y
  distributive-real-inv-mul-ℝ⁺ x⁺@(x , _) y⁺@(y , _) =
    eq-sim-ℝ
      ( symmetric-sim-ℝ
        ( unique-right-inv-ℝ⁺
          ( x⁺ *ℝ⁺ y⁺)
          ( inv-ℝ⁺ x⁺ *ℝ⁺ inv-ℝ⁺ y⁺)
          ( similarity-reasoning-ℝ
            (x *ℝ y) *ℝ (real-inv-ℝ⁺ x⁺ *ℝ real-inv-ℝ⁺ y⁺)
            ~ℝ (x *ℝ real-inv-ℝ⁺ x⁺) *ℝ (y *ℝ real-inv-ℝ⁺ y⁺)
              by sim-eq-ℝ (interchange-law-mul-mul-ℝ _ _ _ _)
            ~ℝ one-ℝ *ℝ one-ℝ
              by
                preserves-sim-mul-ℝ
                  ( right-inverse-law-mul-ℝ⁺ x⁺)
                  ( right-inverse-law-mul-ℝ⁺ y⁺)
            ~ℝ one-ℝ
              by sim-eq-ℝ (left-unit-law-mul-ℝ one-ℝ))))

  distributive-inv-mul-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    inv-ℝ⁺ (x *ℝ⁺ y) ＝ inv-ℝ⁺ x *ℝ⁺ inv-ℝ⁺ y
  distributive-inv-mul-ℝ⁺ x y =
    eq-ℝ⁺ _ _ (distributive-real-inv-mul-ℝ⁺ x y)
```

### Multiplication by a positive real number reflects strict inequality

```agda
abstract
  reflects-le-left-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} →
    le-ℝ (real-ℝ⁺ x *ℝ y) (real-ℝ⁺ x *ℝ z) → le-ℝ y z
  reflects-le-left-mul-ℝ⁺ x {y} {z} xy<xz =
    preserves-le-sim-ℝ
      ( cancel-left-div-mul-ℝ⁺ x y)
      ( cancel-left-div-mul-ℝ⁺ x z)
      ( preserves-le-left-mul-ℝ⁺ (inv-ℝ⁺ x) xy<xz)

  reflects-le-right-mul-ℝ⁺ :
    {l1 l2 l3 : Level} (x : ℝ⁺ l1) {y : ℝ l2} {z : ℝ l3} →
    le-ℝ (y *ℝ real-ℝ⁺ x) (z *ℝ real-ℝ⁺ x) → le-ℝ y z
  reflects-le-right-mul-ℝ⁺ x yx<zx =
    reflects-le-left-mul-ℝ⁺ x
      ( binary-tr
        ( le-ℝ)
        ( commutative-mul-ℝ _ _)
        ( commutative-mul-ℝ _ _)
        ( yx<zx))
```

### The multiplicative inverse operation reverses strict inequality

```agda
abstract
  inv-le-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    le-ℝ⁺ x y → le-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-le-ℝ⁺ x y x<y =
    reflects-le-left-mul-ℝ⁺
      ( y)
      ( preserves-le-left-sim-ℝ _ _ _
        ( transitive-sim-ℝ _ _ _
          ( symmetric-sim-ℝ (right-inverse-law-mul-ℝ⁺ y))
          ( right-inverse-law-mul-ℝ⁺ x))
        ( preserves-le-right-mul-ℝ⁺ (inv-ℝ⁺ x) x<y))
```

### The multiplicative inverse operation reverses inequality

```agda
abstract
  inv-leq-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    leq-ℝ⁺ x y → leq-ℝ⁺ (inv-ℝ⁺ y) (inv-ℝ⁺ x)
  inv-leq-ℝ⁺ x⁺@(x , _) y⁺@(y , _) x≤y =
    double-negation-elim-leq-ℝ
      ( real-inv-ℝ⁺ y⁺)
      ( real-inv-ℝ⁺ x⁺)
      ( map-double-negation
        ( rec-coproduct
          ( λ x~y → leq-sim-ℝ' (preserves-sim-inv-ℝ⁺ x⁺ y⁺ x~y))
          ( λ x<y → leq-le-ℝ (inv-le-ℝ⁺ x⁺ y⁺ x<y)))
        ( irrefutable-sim-or-le-leq-ℝ x y x≤y))
```

### For nonnegative `x`, `(x + ε)⁻¹ x ≤ 1`

```agda
abstract
  leq-one-mul-inv-add-positive-ℝ⁰⁺ :
    {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁺ l2) →
    leq-ℝ (real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x y) *ℝ real-ℝ⁰⁺ x) one-ℝ
  leq-one-mul-inv-add-positive-ℝ⁰⁺ x⁰⁺@(x , _) y⁺@(y , _) =
    let
      open inequality-reasoning-Large-Poset ℝ-Large-Poset
    in
      chain-of-inequalities
      real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ x
      ≤ real-inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺) *ℝ (x +ℝ y)
        by
          preserves-leq-left-mul-ℝ⁺
            ( inv-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
            ( leq-left-add-real-ℝ⁺ x y⁺)
      ≤ one-ℝ
        by
          leq-sim-ℝ
            ( left-inverse-law-mul-ℝ⁺ (add-nonnegative-positive-ℝ x⁰⁺ y⁺))
```
