# The absolute value function on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.absolute-value-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
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

opaque
  unfolding neg-ℚ

  is-nonnegative-rational-abs-ℚ : (q : ℚ) → is-nonnegative-ℚ (rational-abs-ℚ q)
  is-nonnegative-rational-abs-ℚ q =
    rec-coproduct
      ( λ 0≤q →
        inv-tr
          ( is-nonnegative-ℚ)
          ( right-leq-left-max-ℚ
            ( q)
            ( neg-ℚ q)
            ( transitive-leq-ℚ (neg-ℚ q) zero-ℚ q 0≤q (neg-leq-ℚ zero-ℚ q 0≤q)))
          ( is-nonnegative-leq-zero-ℚ q 0≤q))
      ( λ q≤0 →
        inv-tr
          ( is-nonnegative-ℚ)
          ( left-leq-right-max-ℚ
            ( q)
            ( neg-ℚ q)
            ( transitive-leq-ℚ q zero-ℚ (neg-ℚ q) (neg-leq-ℚ q zero-ℚ q≤0) q≤0))
          ( is-nonnegative-leq-zero-ℚ (neg-ℚ q) (neg-leq-ℚ q zero-ℚ q≤0)))
      ( linear-leq-ℚ zero-ℚ q)

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

### The absolute value of a nonnegative rational number is the number itself

```agda
opaque
  unfolding neg-ℚ

  abs-rational-ℚ⁰⁺ : (q : ℚ⁰⁺) → abs-ℚ (rational-ℚ⁰⁺ q) ＝ q
  abs-rational-ℚ⁰⁺ (q , nonneg-q) =
    eq-ℚ⁰⁺
      ( right-leq-left-max-ℚ
        ( q)
        ( neg-ℚ q)
        ( transitive-leq-ℚ
          ( neg-ℚ q)
          ( zero-ℚ)
          ( q)
          ( leq-zero-is-nonnegative-ℚ q nonneg-q)
          ( neg-leq-ℚ zero-ℚ q (leq-zero-is-nonnegative-ℚ q nonneg-q))))

  rational-abs-zero-leq-ℚ : (q : ℚ) → leq-ℚ zero-ℚ q → rational-abs-ℚ q ＝ q
  rational-abs-zero-leq-ℚ q 0≤q =
    ap rational-ℚ⁰⁺ (abs-rational-ℚ⁰⁺ (q , is-nonnegative-leq-zero-ℚ q 0≤q))

  rational-abs-leq-zero-ℚ :
    (q : ℚ) → leq-ℚ q zero-ℚ → rational-abs-ℚ q ＝ neg-ℚ q
  rational-abs-leq-zero-ℚ q q≤0 =
    left-leq-right-max-ℚ
      ( q)
      ( neg-ℚ q)
      ( transitive-leq-ℚ
        ( q)
        ( zero-ℚ)
        ( neg-ℚ q)
        ( neg-leq-ℚ q zero-ℚ q≤0)
        ( q≤0))
```

### The absolute value of the negation of `q` is the absolute value of `q`

```agda
abstract
  abs-neg-ℚ : (q : ℚ) → abs-ℚ (neg-ℚ q) ＝ abs-ℚ q
  abs-neg-ℚ q =
    eq-ℚ⁰⁺
      ( ap (max-ℚ (neg-ℚ q)) (neg-neg-ℚ q) ∙ commutative-max-ℚ _ _)
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
opaque
  unfolding neg-ℚ

  eq-zero-eq-abs-zero-ℚ : (q : ℚ) → abs-ℚ q ＝ zero-ℚ⁰⁺ → q ＝ zero-ℚ
  eq-zero-eq-abs-zero-ℚ q abs=0 =
    rec-coproduct
      ( λ 0≤q →
        antisymmetric-leq-ℚ
          ( q)
          ( zero-ℚ)
          ( tr (leq-ℚ q) (ap rational-ℚ⁰⁺ abs=0) (leq-abs-ℚ q)) 0≤q)
      ( λ q≤0 →
        antisymmetric-leq-ℚ
          ( q)
          ( zero-ℚ)
          ( q≤0)
          ( tr
            ( leq-ℚ zero-ℚ)
            ( neg-neg-ℚ q)
            ( neg-leq-ℚ
              ( neg-ℚ q)
              ( zero-ℚ)
              ( tr
                ( leq-ℚ (neg-ℚ q))
                ( ap rational-ℚ⁰⁺ abs=0)
                ( neg-leq-abs-ℚ q)))))
      ( linear-leq-ℚ zero-ℚ q)

  abs-zero-ℚ : abs-ℚ zero-ℚ ＝ zero-ℚ⁰⁺
  abs-zero-ℚ = eq-ℚ⁰⁺ (left-leq-right-max-ℚ _ _ (refl-leq-ℚ zero-ℚ))
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
```

### `|ab| = |a||b|`

```agda
opaque
  unfolding neg-ℚ

  abs-left-mul-nonnegative-ℚ :
    (q : ℚ) (p : ℚ⁰⁺) → abs-ℚ (rational-ℚ⁰⁺ p *ℚ q) ＝ p *ℚ⁰⁺ abs-ℚ q
  abs-left-mul-nonnegative-ℚ q p⁰⁺@(p , nonneg-p) with linear-leq-ℚ zero-ℚ q
  ... | inl 0≤q =
    eq-ℚ⁰⁺
      ( equational-reasoning
        rational-abs-ℚ (p *ℚ q)
        ＝ p *ℚ q
          by
            ap
              ( rational-ℚ⁰⁺)
              ( abs-rational-ℚ⁰⁺
                ( p⁰⁺ *ℚ⁰⁺ (q , is-nonnegative-leq-zero-ℚ q 0≤q)))
        ＝ p *ℚ rational-abs-ℚ q
          by ap (p *ℚ_) (inv (rational-abs-zero-leq-ℚ q 0≤q)))
  ... | inr q≤0 =
    eq-ℚ⁰⁺
      ( equational-reasoning
        rational-abs-ℚ (p *ℚ q)
        ＝ rational-abs-ℚ (neg-ℚ (p *ℚ q))
          by ap rational-ℚ⁰⁺ (inv (abs-neg-ℚ (p *ℚ q)))
        ＝ rational-abs-ℚ (p *ℚ neg-ℚ q)
          by ap rational-abs-ℚ (inv (right-negative-law-mul-ℚ p q))
        ＝ p *ℚ neg-ℚ q
          by
            ap
              ( rational-ℚ⁰⁺)
              ( abs-rational-ℚ⁰⁺
                ( p⁰⁺ *ℚ⁰⁺
                  ( neg-ℚ q ,
                    is-nonnegative-leq-zero-ℚ
                      ( neg-ℚ q)
                      ( neg-leq-ℚ q zero-ℚ q≤0))))
        ＝ p *ℚ rational-abs-ℚ q
          by ap (p *ℚ_) (inv (rational-abs-leq-zero-ℚ q q≤0)))

  abs-mul-ℚ : (p q : ℚ) → abs-ℚ (p *ℚ q) ＝ abs-ℚ p *ℚ⁰⁺ abs-ℚ q
  abs-mul-ℚ p q with linear-leq-ℚ zero-ℚ p
  ... | inl 0≤p =
    eq-ℚ⁰⁺
      ( equational-reasoning
        rational-abs-ℚ (p *ℚ q)
        ＝ p *ℚ rational-abs-ℚ q
          by
            ap
              ( rational-ℚ⁰⁺)
              ( abs-left-mul-nonnegative-ℚ
                ( q)
                ( p , is-nonnegative-leq-zero-ℚ p 0≤p))
        ＝ rational-abs-ℚ p *ℚ rational-abs-ℚ q
          by ap (_*ℚ rational-abs-ℚ q) (inv (rational-abs-zero-leq-ℚ p 0≤p)))
  ... | inr p≤0 =
    eq-ℚ⁰⁺
      ( equational-reasoning
        rational-abs-ℚ (p *ℚ q)
        ＝ rational-abs-ℚ (neg-ℚ (p *ℚ q))
          by ap rational-ℚ⁰⁺ (inv (abs-neg-ℚ (p *ℚ q)))
        ＝ rational-abs-ℚ (neg-ℚ p *ℚ q)
          by ap rational-abs-ℚ (inv (left-negative-law-mul-ℚ p q))
        ＝ neg-ℚ p *ℚ rational-abs-ℚ q
          by
            ap
              ( rational-ℚ⁰⁺)
              ( abs-left-mul-nonnegative-ℚ
                ( q)
                ( neg-ℚ p ,
                  is-nonnegative-leq-zero-ℚ (neg-ℚ p) (neg-leq-ℚ p zero-ℚ p≤0)))
        ＝ rational-abs-ℚ p *ℚ rational-abs-ℚ q
          by ap (_*ℚ rational-abs-ℚ q) (inv (rational-abs-leq-zero-ℚ p p≤0)))
```
