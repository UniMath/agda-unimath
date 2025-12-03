# Diagonal integer fractions

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.diagonal-integer-fractions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.positive-integers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

{{#concept "Diagonal integer fractions" Agda=diagonal-fraction-ℤ}} are
[integer fractions](elementary-number-theory.integer-fractions.md) of the form
`k/k`.

## Definition

```agda
is-diagonal-prop-fraction-ℤ : fraction-ℤ → Prop lzero
is-diagonal-prop-fraction-ℤ (p , q , _) = Id-Prop ℤ-Set p q

is-diagonal-fraction-ℤ : fraction-ℤ → UU lzero
is-diagonal-fraction-ℤ (p , q , _) = p ＝ q

in-diagonal-fraction-ℤ : ℤ⁺ → fraction-ℤ
in-diagonal-fraction-ℤ k⁺@(k , _) = (k , k⁺)

is-diagonal-in-diagonal-fraction-ℤ :
  (k : ℤ⁺) → is-diagonal-fraction-ℤ (in-diagonal-fraction-ℤ k)
is-diagonal-in-diagonal-fraction-ℤ _ = refl
```

## Properties

### A fraction is diagonal if and only if it is similar to 1

```agda
abstract
  sim-one-is-diagonal-fraction-ℤ :
    (p : fraction-ℤ) →
    is-diagonal-fraction-ℤ p → sim-fraction-ℤ p one-fraction-ℤ
  sim-one-is-diagonal-fraction-ℤ (p , _ , _) refl =
    commutative-mul-ℤ p one-ℤ

  is-diagonal-sim-one-fraction-ℤ :
    (p : fraction-ℤ) →
    sim-fraction-ℤ p one-fraction-ℤ →
    is-diagonal-fraction-ℤ p
  is-diagonal-sim-one-fraction-ℤ (p , q , _) p~q =
    equational-reasoning
      p
      ＝ p *ℤ one-ℤ
        by inv (right-unit-law-mul-ℤ p)
      ＝ one-ℤ *ℤ q
        by p~q
      ＝ q
        by left-unit-law-mul-ℤ q
```

### Multiplying a fraction by a diagonal fraction results in a similar fraction

```agda
abstract
  sim-right-mul-diagonal-fraction-ℤ :
    (p q : fraction-ℤ) → is-diagonal-fraction-ℤ q →
    sim-fraction-ℤ (p *fraction-ℤ q) p
  sim-right-mul-diagonal-fraction-ℤ p (q , .q , pos-q) refl =
    transitive-sim-fraction-ℤ
      ( p *fraction-ℤ (q , q , pos-q))
      ( p *fraction-ℤ one-fraction-ℤ)
      ( p)
      ( right-unit-law-mul-fraction-ℤ p)
      ( sim-fraction-mul-fraction-ℤ
        ( refl)
        ( sim-one-is-diagonal-fraction-ℤ _ refl))

  sim-left-mul-diagonal-fraction-ℤ :
    (p q : fraction-ℤ) → is-diagonal-fraction-ℤ p →
    sim-fraction-ℤ (p *fraction-ℤ q) q
  sim-left-mul-diagonal-fraction-ℤ p q H =
    transitive-sim-fraction-ℤ
      ( p *fraction-ℤ q)
      ( q *fraction-ℤ p)
      ( q)
      ( sim-right-mul-diagonal-fraction-ℤ q p H)
      ( commutative-mul-fraction-ℤ p q)
```
