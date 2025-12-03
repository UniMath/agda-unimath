# Integer fraction powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.integer-fraction-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.diagonal-integer-fractions
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.reduced-integer-fractions

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.nonzero-natural-roots-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
```

</details>

## Idea

For any [positive](real-numbers.positive-real-numbers.md)
[real number](real-numbers.dedekind-real-numbers.md) `x` and any
[integer fraction](elementary-number-theory.integer-fractions.md) `p/q`, we can
define the
{{#concept "power operation" Disambiguation="positive real numbers to integer fraction powers" Agda=int-fraction-power-ℝ⁺}}
$x ↦ x^{p/q}$ to map `x` to the `q`th
[root](real-numbers.nonzero-natural-roots-positive-real-numbers.md) of the `p`th
[power](real-numbers.integer-powers-positive-real-numbers.md) of `x`.

## Definition

```agda
int-fraction-power-ℝ⁺ : {l : Level} → fraction-ℤ → ℝ⁺ l → ℝ⁺ l
int-fraction-power-ℝ⁺ (p , q⁺) x =
  nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ q⁺) (int-power-ℝ⁺ p x)
```

## Properties

### The canonical embedding of integers in the integer fractions preserves powers

```agda
abstract
  int-fraction-in-fraction-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (in-fraction-ℤ k) x ＝ int-power-ℝ⁺ k x
  int-fraction-in-fraction-power-ℝ⁺ k x =
    equational-reasoning
      nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ one-ℤ⁺) (int-power-ℝ⁺ k x)
      ＝ nonzero-nat-root-ℝ⁺ one-ℕ⁺ (int-power-ℝ⁺ k x)
        by
          ap
            ( λ l → nonzero-nat-root-ℝ⁺ l (int-power-ℝ⁺ k x))
            ( eq-nonzero-ℕ (refl {x = 1}))
      ＝ int-power-ℝ⁺ k x
        by one-ℕ⁺-root-ℝ⁺ _
```

### Powers by products of integer fractions are iterated integer fraction powers

```agda
abstract
  mul-int-fraction-power-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (mul-fraction-ℤ p q) x ＝
    int-fraction-power-ℝ⁺ q (int-fraction-power-ℝ⁺ p x)
  mul-int-fraction-power-ℝ⁺ (a , b⁺) (c , d⁺) x =
    inv
      ( equational-reasoning
        nonzero-nat-root-ℝ⁺
          ( positive-nat-ℤ⁺ d⁺)
          ( int-power-ℝ⁺
            ( c)
            ( nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ b⁺) (int-power-ℝ⁺ a x)))
        ＝
          nonzero-nat-root-ℝ⁺
            ( positive-nat-ℤ⁺ d⁺)
            ( nonzero-nat-root-ℝ⁺
              ( positive-nat-ℤ⁺ b⁺)
              ( int-power-ℝ⁺ c (int-power-ℝ⁺ a x)))
          by
            ap
              ( nonzero-nat-root-ℝ⁺ (positive-nat-ℤ⁺ d⁺))
              ( inv (commute-root-int-power-ℝ⁺ (positive-nat-ℤ⁺ b⁺) c _))
        ＝
          nonzero-nat-root-ℝ⁺
            ( positive-nat-ℤ⁺ d⁺ *ℕ⁺ positive-nat-ℤ⁺ b⁺)
            ( int-power-ℝ⁺ c (int-power-ℝ⁺ a x))
          by inv (mul-nonzero-nat-root-ℝ⁺ _ _ _)
        ＝
          nonzero-nat-root-ℝ⁺
            ( positive-nat-ℤ⁺ (d⁺ *ℤ⁺ b⁺))
            ( int-power-ℝ⁺ c (int-power-ℝ⁺ a x))
          by
            ap
              ( λ k → nonzero-nat-root-ℝ⁺ k (int-power-ℝ⁺ c (int-power-ℝ⁺ a x)))
              ( mul-positive-nat-ℤ⁺ d⁺ b⁺)
        ＝
          nonzero-nat-root-ℝ⁺
            ( positive-nat-ℤ⁺ (d⁺ *ℤ⁺ b⁺))
            ( int-power-ℝ⁺ (a *ℤ c) x)
          by
            ap
              ( nonzero-nat-root-ℝ⁺ _)
              ( inv (int-power-mul-ℝ⁺ a c x))
        ＝
          nonzero-nat-root-ℝ⁺
            ( positive-nat-ℤ⁺ (b⁺ *ℤ⁺ d⁺))
            ( int-power-ℝ⁺ (a *ℤ c) x)
          by
            ap
              ( λ k →
                nonzero-nat-root-ℝ⁺
                  ( positive-nat-ℤ⁺ k)
                  ( int-power-ℝ⁺ (a *ℤ c) x))
              ( commutative-mul-ℤ⁺ d⁺ b⁺))
```

### Powers by diagonal integer fractions are the identity

```agda
abstract
  is-identity-power-diagonal-int-fraction-ℝ⁺ :
    {l : Level} (k : fraction-ℤ) → is-diagonal-fraction-ℤ k →
    (x : ℝ⁺ l) → int-fraction-power-ℝ⁺ k x ＝ x
  is-identity-power-diagonal-int-fraction-ℝ⁺ (p , _ , pos-p) refl x =
    let
      n⁺@(n , _) = positive-nat-ℤ⁺ (p , pos-p)
    in
      equational-reasoning
        nonzero-nat-root-ℝ⁺ n⁺ (int-power-ℝ⁺ p x)
        ＝ nonzero-nat-root-ℝ⁺ n⁺ (int-power-ℝ⁺ (int-ℕ n) x)
          by
            ap
              ( λ k → nonzero-nat-root-ℝ⁺ n⁺ (int-power-ℝ⁺ k x))
              ( inv (ap int-ℤ⁺ (is-section-positive-nat-ℤ⁺ (p , pos-p))))
        ＝ nonzero-nat-root-ℝ⁺ n⁺ (power-ℝ⁺ n x)
          by ap (nonzero-nat-root-ℝ⁺ n⁺) (int-power-int-ℝ⁺ n x)
        ＝ x
          by is-retraction-nonzero-nat-power-ℝ⁺ n⁺ x
```

### Powers by integer fractions are equal to powers by reduced integer fractions

```agda
abstract
  reduce-int-fraction-power-ℝ⁺ :
    {l : Level} (k : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ k x ＝
    int-fraction-power-ℝ⁺ (reduce-fraction-ℤ k) x
  reduce-int-fraction-power-ℝ⁺ k x =
    equational-reasoning
      int-fraction-power-ℝ⁺ k x
      ＝
        int-fraction-power-ℝ⁺
          ( reduce-fraction-ℤ k *fraction-ℤ diagonal-gcd-fraction-ℤ k)
          ( x)
        by
          ap
            ( λ p → int-fraction-power-ℝ⁺ p x)
            ( eq-mul-reduce-diagonal-fraction-ℤ k)
      ＝
        int-fraction-power-ℝ⁺
          ( diagonal-gcd-fraction-ℤ k)
          ( int-fraction-power-ℝ⁺ (reduce-fraction-ℤ k) x)
        by mul-int-fraction-power-ℝ⁺ _ _ _
      ＝ int-fraction-power-ℝ⁺ (reduce-fraction-ℤ k) x
        by is-identity-power-diagonal-int-fraction-ℝ⁺ _ refl _
```

### Powers by integer fractions are equal to powers by similar integer fractions

```agda
abstract
  sim-int-fraction-power-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) → sim-fraction-ℤ p q →
    (x : ℝ⁺ l) → int-fraction-power-ℝ⁺ p x ＝ int-fraction-power-ℝ⁺ q x
  sim-int-fraction-power-ℝ⁺ p q p~q x =
    equational-reasoning
      int-fraction-power-ℝ⁺ p x
      ＝ int-fraction-power-ℝ⁺ (reduce-fraction-ℤ p) x
        by reduce-int-fraction-power-ℝ⁺ p x
      ＝ int-fraction-power-ℝ⁺ (reduce-fraction-ℤ q) x
        by
          ap
            ( λ k → int-fraction-power-ℝ⁺ k x)
            ( unique-reduce-fraction-ℤ p q p~q)
      ＝ int-fraction-power-ℝ⁺ q x
        by inv (reduce-int-fraction-power-ℝ⁺ q x)
```

### `xᵃ⁺ᵇ = xᵃxᵇ`

```agda
abstract
  add-numerator-int-fraction-power-ℝ⁺ :
    {l : Level} (p q : ℤ) (r : ℤ⁺) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (p +ℤ q , r) x ＝
    int-fraction-power-ℝ⁺ (p , r) x *ℝ⁺ int-fraction-power-ℝ⁺ (q , r) x
  add-numerator-int-fraction-power-ℝ⁺ p q r x =
    let
      rℕ = positive-nat-ℤ⁺ r
    in
      equational-reasoning
        nonzero-nat-root-ℝ⁺ rℕ (int-power-ℝ⁺ (p +ℤ q) x)
        ＝ nonzero-nat-root-ℝ⁺ rℕ (int-power-ℝ⁺ p x *ℝ⁺ int-power-ℝ⁺ q x)
          by
            ap
              ( nonzero-nat-root-ℝ⁺ rℕ)
              ( distributive-int-power-add-ℝ⁺ p q x)
        ＝
          ( nonzero-nat-root-ℝ⁺ rℕ (int-power-ℝ⁺ p x)) *ℝ⁺
          ( nonzero-nat-root-ℝ⁺ rℕ (int-power-ℝ⁺ q x))
          by
            distributive-nonzero-nat-root-mul-ℝ⁺ rℕ _ _

  distributive-add-integer-fraction-power-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (p +fraction-ℤ q) x ＝
    int-fraction-power-ℝ⁺ p x *ℝ⁺ int-fraction-power-ℝ⁺ q x
  distributive-add-integer-fraction-power-ℝ⁺
    (a , b⁺@(b , _)) (c , d⁺@(d , _)) x =
    inv
      ( equational-reasoning
        int-fraction-power-ℝ⁺ (a , b⁺) x *ℝ⁺ int-fraction-power-ℝ⁺ (c , d⁺) x
        ＝
          ( int-fraction-power-ℝ⁺ (a *ℤ d , b⁺ *ℤ⁺ d⁺) x) *ℝ⁺
          ( int-fraction-power-ℝ⁺ (b *ℤ c , b⁺ *ℤ⁺ d⁺) x)
          by
            ap-mul-ℝ⁺
              ( sim-int-fraction-power-ℝ⁺ _ _
                ( symmetric-sim-fraction-ℤ _ _
                  ( sim-right-mul-diagonal-fraction-ℤ (a , b⁺) _ refl))
                ( x))
              ( sim-int-fraction-power-ℝ⁺ _ _
                ( symmetric-sim-fraction-ℤ _ _
                  ( sim-left-mul-diagonal-fraction-ℤ _ (c , d⁺) refl))
                ( x))
        ＝
          ( int-fraction-power-ℝ⁺ (a *ℤ d , b⁺ *ℤ⁺ d⁺) x) *ℝ⁺
          ( int-fraction-power-ℝ⁺ (c *ℤ b , b⁺ *ℤ⁺ d⁺) x)
          by
            ap-mul-ℝ⁺
              ( refl)
              ( ap
                ( λ k → int-fraction-power-ℝ⁺ (k , b⁺ *ℤ⁺ d⁺) x)
                ( commutative-mul-ℤ b c))
        ＝ int-fraction-power-ℝ⁺ (a *ℤ d +ℤ c *ℤ b , b⁺ *ℤ⁺ d⁺) x
          by inv (add-numerator-int-fraction-power-ℝ⁺ _ _ _ _))
```

### Integer fraction powers distribute over multiplication

```agda
abstract
  distributive-int-fraction-power-mul-ℝ⁺ :
    {l1 l2 : Level} (q : fraction-ℤ) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    int-fraction-power-ℝ⁺ q (x *ℝ⁺ y) ＝
    int-fraction-power-ℝ⁺ q x *ℝ⁺ int-fraction-power-ℝ⁺ q y
  distributive-int-fraction-power-mul-ℝ⁺ (p , q⁺) x y =
    ( ap (nonzero-nat-root-ℝ⁺ _) (distributive-int-power-mul-ℝ⁺ p x y)) ∙
    ( distributive-nonzero-nat-root-mul-ℝ⁺ _ _ _)
```
