# The absolute value function on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.absolute-value-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-nonnegative-rational-numbers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.difference-rational-numbers
open import elementary-number-theory.inequalities-positive-and-negative-rational-numbers
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-nonnegative-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.nonpositive-rational-numbers
open import elementary-number-theory.positive-and-negative-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The
{{#concept "absolute value" Disambiguation="of a rational number" Agda=abs-ℚ WD="absolute value" WDID=Q120812}}
of a [rational number](elementary-number-theory.rational-numbers.md) is the
[greater](elementary-number-theory.maximum-rational-numbers.md) of itself and
its negation.

## Definition

```agda
rational-abs-ℚ : ℚ → ℚ
rational-abs-ℚ q = max-ℚ q (neg-ℚ q)

abstract
  is-nonnegative-rational-abs-ℚ : (q : ℚ) → is-nonnegative-ℚ (rational-abs-ℚ q)
  is-nonnegative-rational-abs-ℚ q =
    rec-coproduct
      ( λ is-nonpos-q →
        inv-tr
          ( is-nonnegative-ℚ)
          ( left-leq-right-max-ℚ _ _
            ( leq-nonpositive-nonnegative-ℚ
              ( q , is-nonpos-q)
              ( neg-ℚ⁰⁻ (q , is-nonpos-q))))
          ( is-nonnegative-neg-is-nonpositive-ℚ is-nonpos-q))
      ( λ is-nonneg-q →
        inv-tr
          ( is-nonnegative-ℚ)
          ( right-leq-left-max-ℚ _ _
            ( leq-nonpositive-nonnegative-ℚ
              ( neg-ℚ⁰⁺ (q , is-nonneg-q))
              ( q , is-nonneg-q)))
          ( is-nonneg-q))
      ( is-nonpositive-or-nonnegative-ℚ q)

abs-ℚ : ℚ → ℚ⁰⁺
pr1 (abs-ℚ q) = rational-abs-ℚ q
pr2 (abs-ℚ q) = is-nonnegative-rational-abs-ℚ q
```

## Properties

### Bounds on both `p` and `-p` are bounds on `|p|`

```agda
abstract
  leq-abs-leq-leq-neg-ℚ :
    (p q : ℚ) → leq-ℚ p q → leq-ℚ (neg-ℚ p) q → leq-ℚ (rational-abs-ℚ p) q
  leq-abs-leq-leq-neg-ℚ p q = leq-max-leq-both-ℚ q p (neg-ℚ p)

  le-abs-le-le-neg-ℚ :
    (p q : ℚ) → le-ℚ p q → le-ℚ (neg-ℚ p) q → le-ℚ (rational-abs-ℚ p) q
  le-abs-le-le-neg-ℚ p q = le-max-le-both-ℚ q p (neg-ℚ p)
```

### The absolute value of the negation of `q` is the absolute value of `q`

```agda
abstract
  abs-neg-ℚ : (q : ℚ) → abs-ℚ (neg-ℚ q) ＝ abs-ℚ q
  abs-neg-ℚ q =
    eq-ℚ⁰⁺
      ( ap (max-ℚ (neg-ℚ q)) (neg-neg-ℚ q) ∙ commutative-max-ℚ _ _)

  rational-abs-neg-ℚ : (q : ℚ) → rational-abs-ℚ (neg-ℚ q) ＝ rational-abs-ℚ q
  rational-abs-neg-ℚ q = ap rational-ℚ⁰⁺ (abs-neg-ℚ q)
```

### The absolute value of a nonnegative rational number is the number itself

```agda
abstract
  abs-rational-ℚ⁰⁺ : (q : ℚ⁰⁺) → abs-ℚ (rational-ℚ⁰⁺ q) ＝ q
  abs-rational-ℚ⁰⁺ q =
    eq-ℚ⁰⁺
      ( right-leq-left-max-ℚ _ _ (leq-nonpositive-nonnegative-ℚ (neg-ℚ⁰⁺ q) q))

  rational-abs-zero-leq-ℚ : (q : ℚ) → leq-ℚ zero-ℚ q → rational-abs-ℚ q ＝ q
  rational-abs-zero-leq-ℚ q 0≤q =
    ap rational-ℚ⁰⁺ (abs-rational-ℚ⁰⁺ (q , is-nonnegative-leq-zero-ℚ 0≤q))

  rational-abs-leq-zero-ℚ :
    (q : ℚ) → leq-ℚ q zero-ℚ → rational-abs-ℚ q ＝ neg-ℚ q
  rational-abs-leq-zero-ℚ q q≤0 =
    equational-reasoning
      rational-abs-ℚ q
      ＝ rational-abs-ℚ (neg-ℚ q)
        by inv (rational-abs-neg-ℚ q)
      ＝ neg-ℚ q
        by
          ap rational-ℚ⁰⁺
            ( abs-rational-ℚ⁰⁺ (neg-ℚ⁰⁻ (q , is-nonpositive-leq-zero-ℚ q≤0)))
```

### The absolute value of a positive rational number is the number itself

```agda
abstract
  rational-abs-rational-ℚ⁺ :
    (q : ℚ⁺) → rational-abs-ℚ (rational-ℚ⁺ q) ＝ rational-ℚ⁺ q
  rational-abs-rational-ℚ⁺ q =
    ap rational-ℚ⁰⁺ (abs-rational-ℚ⁰⁺ (nonnegative-ℚ⁺ q))
```

### `q` is less than or equal to `abs-ℚ q`

```agda
abstract
  leq-abs-ℚ : (q : ℚ) → leq-ℚ q (rational-abs-ℚ q)
  leq-abs-ℚ q = leq-left-max-ℚ q (neg-ℚ q)

  neg-leq-abs-ℚ : (q : ℚ) → leq-ℚ (neg-ℚ q) (rational-abs-ℚ q)
  neg-leq-abs-ℚ q = leq-right-max-ℚ q (neg-ℚ q)
```

### The absolute value of `q` is zero iff `q` is zero

```agda
abstract
  eq-zero-eq-abs-zero-ℚ : {q : ℚ} → abs-ℚ q ＝ zero-ℚ⁰⁺ → q ＝ zero-ℚ
  eq-zero-eq-abs-zero-ℚ {q} abs=0 =
    antisymmetric-leq-ℚ
      ( q)
      ( zero-ℚ)
      ( transitive-leq-ℚ
        ( q)
        ( rational-abs-ℚ q)
        ( zero-ℚ)
        ( leq-eq-ℚ _ _ (ap rational-ℚ⁰⁺ abs=0))
        ( leq-abs-ℚ q))
      ( binary-tr
        ( leq-ℚ)
        ( ap (neg-ℚ ∘ rational-ℚ⁰⁺) abs=0 ∙ neg-zero-ℚ)
        ( neg-neg-ℚ q)
        ( neg-leq-ℚ (neg-leq-abs-ℚ q)))

  abs-zero-ℚ : abs-ℚ zero-ℚ ＝ zero-ℚ⁰⁺
  abs-zero-ℚ =
    eq-ℚ⁰⁺
      ( equational-reasoning
        max-ℚ zero-ℚ (neg-ℚ zero-ℚ)
        ＝ max-ℚ zero-ℚ zero-ℚ by ap-max-ℚ refl neg-zero-ℚ
        ＝ zero-ℚ by idempotent-max-ℚ zero-ℚ)
```

### The triangle inequality

```agda
abstract
  triangle-inequality-abs-ℚ :
    (p q : ℚ) → leq-ℚ⁰⁺ (abs-ℚ (p +ℚ q)) (abs-ℚ p +ℚ⁰⁺ abs-ℚ q)
  triangle-inequality-abs-ℚ p q =
    leq-max-leq-both-ℚ
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      ( _)
      ( _)
      ( preserves-leq-add-ℚ
        { p}
        { rational-abs-ℚ p}
        { q}
        { rational-abs-ℚ q}
        ( leq-abs-ℚ p)
        ( leq-abs-ℚ q))
      ( inv-tr
        ( λ r → leq-ℚ r (rational-abs-ℚ p +ℚ rational-abs-ℚ q))
        ( distributive-neg-add-ℚ p q)
        ( preserves-leq-add-ℚ
          { neg-ℚ p}
          { rational-abs-ℚ p}
          { neg-ℚ q}
          { rational-abs-ℚ q}
          ( neg-leq-abs-ℚ p)
          ( neg-leq-abs-ℚ q)))

  triangle-inequality-abs-diff-ℚ :
    (p q : ℚ) → leq-ℚ⁰⁺ (abs-ℚ (p -ℚ q)) (abs-ℚ p +ℚ⁰⁺ abs-ℚ q)
  triangle-inequality-abs-diff-ℚ p q =
    tr
      ( leq-ℚ⁰⁺ (abs-ℚ (p -ℚ q)))
      ( ap-binary add-ℚ⁰⁺ (refl {x = abs-ℚ p}) (abs-neg-ℚ q))
      ( triangle-inequality-abs-ℚ p (neg-ℚ q))
```

### `|ab| = |a||b|`

```agda
abstract
  rational-abs-left-mul-nonnegative-ℚ :
    (q : ℚ) (p : ℚ⁰⁺) →
    rational-abs-ℚ (rational-ℚ⁰⁺ p *ℚ q) ＝ rational-ℚ⁰⁺ p *ℚ rational-abs-ℚ q
  rational-abs-left-mul-nonnegative-ℚ q p⁰⁺@(p , _) =
    equational-reasoning
      rational-abs-ℚ (p *ℚ q)
      ＝ max-ℚ (p *ℚ q) (p *ℚ neg-ℚ q)
        by ap-max-ℚ refl (inv (right-negative-law-mul-ℚ p q))
      ＝ p *ℚ rational-abs-ℚ q
        by inv (left-distributive-mul-max-ℚ⁰⁺ p⁰⁺ _ _)

  abs-mul-ℚ : (p q : ℚ) → abs-ℚ (p *ℚ q) ＝ abs-ℚ p *ℚ⁰⁺ abs-ℚ q
  abs-mul-ℚ p q =
    eq-ℚ⁰⁺
      ( rec-coproduct
        ( λ is-nonpos-p →
          equational-reasoning
            rational-abs-ℚ (p *ℚ q)
            ＝ rational-abs-ℚ (neg-ℚ (p *ℚ q))
              by inv (rational-abs-neg-ℚ _)
            ＝ rational-abs-ℚ (neg-ℚ p *ℚ q)
              by ap rational-abs-ℚ (inv (left-negative-law-mul-ℚ p q))
            ＝ neg-ℚ p *ℚ rational-abs-ℚ q
              by
                rational-abs-left-mul-nonnegative-ℚ
                  ( q)
                  ( neg-ℚ⁰⁻ (p , is-nonpos-p))
            ＝ rational-abs-ℚ p *ℚ rational-abs-ℚ q
              by
                ap-mul-ℚ
                  ( inv
                    ( rational-abs-leq-zero-ℚ
                      ( p)
                      ( leq-zero-is-nonpositive-ℚ is-nonpos-p)))
                  ( refl))
        ( λ is-nonneg-p →
          equational-reasoning
            rational-abs-ℚ (p *ℚ q)
            ＝ p *ℚ rational-abs-ℚ q
              by rational-abs-left-mul-nonnegative-ℚ q (p , is-nonneg-p)
            ＝ rational-abs-ℚ p *ℚ rational-abs-ℚ q
              by
                ap-mul-ℚ
                  ( inv (ap rational-ℚ⁰⁺ (abs-rational-ℚ⁰⁺ (p , is-nonneg-p))))
                  ( refl))
        ( is-nonpositive-or-nonnegative-ℚ p))

abstract
  rational-abs-mul-ℚ :
    (p q : ℚ) → rational-abs-ℚ (p *ℚ q) ＝ rational-abs-ℚ p *ℚ rational-abs-ℚ q
  rational-abs-mul-ℚ p q = ap rational-ℚ⁰⁺ (abs-mul-ℚ p q)
```
