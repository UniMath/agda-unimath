# The absolute value function on the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}
module elementary-number-theory.absolute-value-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.maximum-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.function-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
```

</details>

## Idea

The {{#concept "absolute value" Disambiguation="of a rational number" Agda=abs-ℚ WD="absolute value" WDID=Q120812}}
a rational number is the greater of itself and its negation.

## Definition

```agda
rational-abs-ℚ : ℚ → ℚ
rational-abs-ℚ q = max-ℚ q (neg-ℚ q)

abstract
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

### The absolute value of a nonnegative rational number is the number itself

```agda
abstract
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

  leq-neg-abs-ℚ : (q : ℚ) → leq-ℚ (neg-ℚ q) (rational-abs-ℚ q)
  leq-neg-abs-ℚ q = leq-right-max-ℚ q (neg-ℚ q)
```

### The absolute value of `q` is zero iff `q` is zero

```agda
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
            ( tr (leq-ℚ (neg-ℚ q)) (ap rational-ℚ⁰⁺ abs=0) (leq-neg-abs-ℚ q)))))
    (linear-leq-ℚ zero-ℚ q)

abs-zero-ℚ : abs-ℚ zero-ℚ ＝ zero-ℚ⁰⁺
abs-zero-ℚ = eq-ℚ⁰⁺ (left-leq-right-max-ℚ _ _ (refl-leq-ℚ zero-ℚ))
```

### The triangle inequality

```agda
abstract
  triangle-inequality-abs-ℚ :
    (p q : ℚ) → leq-ℚ⁰⁺ (abs-ℚ (p +ℚ q)) (abs-ℚ p +ℚ⁰⁺ abs-ℚ q)
  triangle-inequality-abs-ℚ p q
    with linear-leq-ℚ zero-ℚ p | linear-leq-ℚ zero-ℚ q
  ... | inl 0≤p | inl 0≤q =
    leq-eq-ℚ
      ( rational-abs-ℚ (p +ℚ q))
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      ( equational-reasoning
        rational-abs-ℚ (p +ℚ q)
        ＝ p +ℚ q
          by
            rational-abs-zero-leq-ℚ
              ( p +ℚ q)
              ( tr
                ( λ r → leq-ℚ r (p +ℚ q))
                ( left-unit-law-add-ℚ zero-ℚ)
                ( preserves-leq-add-ℚ {zero-ℚ} {p} {zero-ℚ} {q} 0≤p 0≤q))
        ＝ rational-abs-ℚ p +ℚ rational-abs-ℚ q
          by
            ap-binary
              ( add-ℚ)
              ( inv (rational-abs-zero-leq-ℚ p 0≤p))
              ( inv (rational-abs-zero-leq-ℚ q 0≤q)))
  ... | inl 0≤p | inr q≤0 =
    leq-max-leq-both-ℚ
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      ( p +ℚ q)
      ( neg-ℚ (p +ℚ q))
      ( transitive-leq-ℚ
        ( p +ℚ q)
        ( p)
        ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
        {!   !}
        {!   !})
      {!   !}
  ... | inr p≤0 | inl 0≤q =
    leq-max-leq-both-ℚ
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      ( p +ℚ q)
      ( neg-ℚ (p +ℚ q))
      {!   !}
      {!   !}
  ... | inr p≤0 | inr q≤0 =
    leq-eq-ℚ
      ( rational-abs-ℚ (p +ℚ q))
      ( rational-abs-ℚ p +ℚ rational-abs-ℚ q)
      {!   !}
```
