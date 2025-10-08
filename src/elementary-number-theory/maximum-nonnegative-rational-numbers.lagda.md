# The maximum of nonnegative rational numbers

```agda
module elementary-number-theory.maximum-nonnegative-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-nonnegative-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-rational-numbers
open import elementary-number-theory.nonnegative-rational-numbers
open import elementary-number-theory.rational-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
```

</details>

## Idea

The {{#concept "maximum" Disambiguation="of two nonnegative rational numbers" Agda=max-ℚ⁰⁺}} of two
[nonnegative rational numbers](elementary-number-theory.nonnegative-rational-numbers.md)
is the
[greatest](elementary-number-theory.inequality-nonnegative-rational-numbers.md)
rational number of the two.

## Definition

```agda
abstract
  is-nonnegative-max-ℚ⁰⁺ :
    (p q : ℚ⁰⁺) → is-nonnegative-ℚ (max-ℚ (rational-ℚ⁰⁺ p) (rational-ℚ⁰⁺ q))
  is-nonnegative-max-ℚ⁰⁺ (p , is-nonneg-p) (q , is-nonneg-q) =
    is-nonnegative-leq-zero-ℚ _
      ( transitive-leq-ℚ
        ( zero-ℚ)
        ( p)
        ( max-ℚ p q)
        ( leq-left-max-ℚ p q)
        ( leq-zero-is-nonnegative-ℚ p is-nonneg-p))

max-ℚ⁰⁺ : ℚ⁰⁺ → ℚ⁰⁺ → ℚ⁰⁺
max-ℚ⁰⁺ p⁰⁺@(p , _) q⁰⁺@(q , _) = (max-ℚ p q , is-nonnegative-max-ℚ⁰⁺ p⁰⁺ q⁰⁺)
```

## Properties

### The binary maximum is associative

```agda
abstract
  associative-max-ℚ⁰⁺ :
    (x y z : ℚ⁰⁺) → max-ℚ⁰⁺ (max-ℚ⁰⁺ x y) z ＝ max-ℚ⁰⁺ x (max-ℚ⁰⁺ y z)
  associative-max-ℚ⁰⁺ (x , _) (y , _) (z , _) = eq-ℚ⁰⁺ (associative-max-ℚ x y z)
```

### The binary maximum is commutative

```agda
abstract
  commutative-max-ℚ⁰⁺ : (x y : ℚ⁰⁺) → max-ℚ⁰⁺ x y ＝ max-ℚ⁰⁺ y x
  commutative-max-ℚ⁰⁺ (x , _) (y , _) = eq-ℚ⁰⁺ (commutative-max-ℚ x y)
```

### The binary maximum is idempotent

```agda
abstract
  idempotent-max-ℚ⁰⁺ : (x : ℚ⁰⁺) → max-ℚ⁰⁺ x x ＝ x
  idempotent-max-ℚ⁰⁺ (x , _) = eq-ℚ⁰⁺ (idempotent-max-ℚ x)
```

### The binary maximum is an upper bound

```agda
abstract
  leq-left-max-ℚ⁰⁺ : (x y : ℚ⁰⁺) → leq-ℚ⁰⁺ x (max-ℚ⁰⁺ x y)
  leq-left-max-ℚ⁰⁺ _ _ = leq-left-max-ℚ _ _

  leq-right-max-ℚ⁰⁺ : (x y : ℚ⁰⁺) → leq-ℚ⁰⁺ y (max-ℚ⁰⁺ x y)
  leq-right-max-ℚ⁰⁺ _ _ = leq-right-max-ℚ _ _
```
