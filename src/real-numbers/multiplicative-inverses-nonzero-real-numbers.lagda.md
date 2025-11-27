# Multiplicative inverses of nonzero real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.multiplicative-inverses-nonzero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.invertible-elements-commutative-rings

open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.minimum-rational-numbers
open import elementary-number-theory.multiplication-closed-intervals-rational-numbers
open import elementary-number-theory.multiplication-positive-and-negative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.large-ring-of-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-negative-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonzero-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) has a
{{#concept "multiplicative inverse" Disambiguation="nonzero real numbers" Agda=inv-nonzero-ℝ}}
[if and only if](foundation.logical-equivalences.md) it is
[nonzero](real-numbers.nonzero-real-numbers.md).

## Definition

### The property of having a multiplicative inverse

```agda
has-nonzero-inv-ℝ : {l : Level} → ℝ l → UU (lsuc l)
has-nonzero-inv-ℝ {l} x =
  Σ (nonzero-ℝ l) (λ y → sim-ℝ (x *ℝ real-nonzero-ℝ y) one-ℝ)

abstract
  is-prop-has-nonzero-inv-ℝ :
    {l : Level} (x : ℝ l) → is-prop (has-nonzero-inv-ℝ x)
  is-prop-has-nonzero-inv-ℝ x =
    is-prop-all-elements-equal
      ( λ ((y , _) , xy=1) ((z , _) , xz=1) →
        eq-type-subtype
          ( λ (w , _) → sim-prop-ℝ (x *ℝ w) one-ℝ)
          ( eq-nonzero-ℝ _ _
            ( eq-sim-ℝ
              ( similarity-reasoning-ℝ
                y
                ~ℝ one-ℝ *ℝ y
                  by sim-eq-ℝ (inv (left-unit-law-mul-ℝ y))
                ~ℝ (x *ℝ z) *ℝ y
                  by preserves-sim-right-mul-ℝ y _ _ (symmetric-sim-ℝ xz=1)
                ~ℝ (x *ℝ y) *ℝ z
                  by sim-eq-ℝ (right-swap-mul-ℝ x z y)
                ~ℝ one-ℝ *ℝ z
                  by preserves-sim-right-mul-ℝ z _ _ xy=1
                ~ℝ z
                  by sim-eq-ℝ (left-unit-law-mul-ℝ z)))))

has-nonzero-inv-prop-ℝ : {l : Level} → ℝ l → Prop (lsuc l)
has-nonzero-inv-prop-ℝ x = (has-nonzero-inv-ℝ x , is-prop-has-nonzero-inv-ℝ x)
```

## Properties

### Nonzero real numbers have (nonzero) multiplicative inverses

```agda
module _
  {l : Level} (x : nonzero-ℝ l)
  where

  abstract
    has-nonzero-inv-nonzero-ℝ : has-nonzero-inv-ℝ (real-nonzero-ℝ x)
    has-nonzero-inv-nonzero-ℝ =
      elim-disjunction
        ( has-nonzero-inv-prop-ℝ (real-nonzero-ℝ x))
        ( λ is-neg-x →
          ( nonzero-ℝ⁻ (inv-ℝ⁻ (real-nonzero-ℝ x , is-neg-x)) ,
            right-inverse-law-mul-ℝ⁻ (real-nonzero-ℝ x , is-neg-x)))
        ( λ is-pos-x →
          ( nonzero-ℝ⁺ (inv-ℝ⁺ (real-nonzero-ℝ x , is-pos-x)) ,
            right-inverse-law-mul-ℝ⁺ (real-nonzero-ℝ x , is-pos-x)))
        ( is-nonzero-real-nonzero-ℝ x)

  inv-nonzero-ℝ : nonzero-ℝ l
  inv-nonzero-ℝ = pr1 has-nonzero-inv-nonzero-ℝ

  real-inv-nonzero-ℝ : ℝ l
  real-inv-nonzero-ℝ = real-nonzero-ℝ inv-nonzero-ℝ

  right-inverse-law-mul-nonzero-ℝ :
    sim-ℝ (real-nonzero-ℝ x *ℝ real-inv-nonzero-ℝ) one-ℝ
  right-inverse-law-mul-nonzero-ℝ = pr2 has-nonzero-inv-nonzero-ℝ

  abstract
    left-inverse-law-mul-nonzero-ℝ :
      sim-ℝ (real-inv-nonzero-ℝ *ℝ real-nonzero-ℝ x) one-ℝ
    left-inverse-law-mul-nonzero-ℝ =
      tr
        ( λ y → sim-ℝ y one-ℝ)
        ( commutative-mul-ℝ _ _)
        ( right-inverse-law-mul-nonzero-ℝ)

is-invertible-is-nonzero-ℝ :
  {l : Level} (x : ℝ l) → is-nonzero-ℝ x →
  is-invertible-element-Commutative-Ring (commutative-ring-ℝ l) x
is-invertible-is-nonzero-ℝ x x≠0 =
  ( real-inv-nonzero-ℝ (x , x≠0) ,
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ _ _)
        ( right-inverse-law-mul-nonzero-ℝ (x , x≠0))) ,
    eq-sim-ℝ
      ( transitive-sim-ℝ _ _ _
        ( sim-raise-ℝ _ _)
        ( left-inverse-law-mul-nonzero-ℝ (x , x≠0))))
```

### The multiplicative inverse is unique

```agda
abstract
  unique-right-inv-nonzero-ℝ :
    {l1 l2 : Level} (x : nonzero-ℝ l1) (y : nonzero-ℝ l2) →
    sim-ℝ (real-nonzero-ℝ x *ℝ real-nonzero-ℝ y) one-ℝ →
    sim-ℝ (real-nonzero-ℝ y) (real-inv-nonzero-ℝ x)
  unique-right-inv-nonzero-ℝ xnz@(x , _) ynz@(y , _) xy=1 =
    similarity-reasoning-ℝ
      y
      ~ℝ one-ℝ *ℝ y
        by sim-eq-ℝ (inv (left-unit-law-mul-ℝ y))
      ~ℝ (x *ℝ real-inv-nonzero-ℝ xnz) *ℝ y
        by
          preserves-sim-right-mul-ℝ y _ _
            ( symmetric-sim-ℝ (right-inverse-law-mul-nonzero-ℝ xnz))
      ~ℝ (x *ℝ y) *ℝ real-inv-nonzero-ℝ xnz
        by sim-eq-ℝ (right-swap-mul-ℝ _ _ _)
      ~ℝ one-ℝ *ℝ real-inv-nonzero-ℝ xnz
        by preserves-sim-right-mul-ℝ _ _ _ xy=1
      ~ℝ real-inv-nonzero-ℝ xnz
        by sim-eq-ℝ (left-unit-law-mul-ℝ _)

  unique-left-inv-nonzero-ℝ :
    {l1 l2 : Level} (x : nonzero-ℝ l1) (y : nonzero-ℝ l2) →
    sim-ℝ (real-nonzero-ℝ x *ℝ real-nonzero-ℝ y) one-ℝ →
    sim-ℝ (real-nonzero-ℝ x) (real-inv-nonzero-ℝ y)
  unique-left-inv-nonzero-ℝ x y xy=1 =
    unique-right-inv-nonzero-ℝ y x
      ( tr (λ z → sim-ℝ z one-ℝ) (commutative-mul-ℝ _ _) xy=1)
```

### If two nonzero real numbers are similar, so are their inverses

```agda
abstract
  preserves-sim-inv-nonzero-ℝ :
    {l1 l2 : Level} (x : nonzero-ℝ l1) (y : nonzero-ℝ l2) →
    sim-ℝ (real-nonzero-ℝ x) (real-nonzero-ℝ y) →
    sim-ℝ (real-inv-nonzero-ℝ x) (real-inv-nonzero-ℝ y)
  preserves-sim-inv-nonzero-ℝ (x , x≠0) (y , y≠0) x~y =
    symmetric-sim-ℝ
      ( unique-right-inv-nonzero-ℝ
        ( x , x≠0)
        ( inv-nonzero-ℝ (y , y≠0))
        ( similarity-reasoning-ℝ
          x *ℝ real-inv-nonzero-ℝ (y , y≠0)
          ~ℝ y *ℝ real-inv-nonzero-ℝ (y , y≠0)
            by preserves-sim-right-mul-ℝ _ _ _ x~y
          ~ℝ one-ℝ
            by right-inverse-law-mul-nonzero-ℝ (y , y≠0)))
```
