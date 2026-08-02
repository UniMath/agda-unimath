# Integer fraction powers of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.integer-fraction-powers-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
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
open import real-numbers.nonzero-roots-positive-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-positive-real-numbers
```

</details>

## Idea

Given an [integer fraction](elementary-number-theory.integer-fractions.md)
`p/q`, the `p/q`
{{#concept "power" Disambiguation="a positive real number to an integer fraction power" Agda=int-fraction-power-ℝ⁺}}
of a [positive real number](real-numbers.positive-real-numbers.md) `x` is the
`q`th [root](real-numbers.nonzero-roots-positive-real-numbers.md) of the `p`th
[power](real-numbers.integer-powers-positive-real-numbers.md) of `x`.

## Definition

```agda
int-fraction-power-ℝ⁺ :
  {l : Level} → fraction-ℤ → ℝ⁺ l → ℝ⁺ l
int-fraction-power-ℝ⁺ (p , q⁺) x =
  root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺) (int-power-ℝ⁺ p x)
```

## Properties

### `xᵃᵇ = (xᵃ)ᵇ`

```agda
abstract
  int-fraction-power-mul-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (p *fraction-ℤ q) x ＝
    int-fraction-power-ℝ⁺ q (int-fraction-power-ℝ⁺ p x)
  int-fraction-power-mul-ℝ⁺ p/q@(p , q⁺) r/s@(r , s⁺) x =
    equational-reasoning
      root-nonzero-nat-ℝ⁺
        ( positive-nat-ℤ⁺ (mul-positive-ℤ q⁺ s⁺))
        ( int-power-ℝ⁺ (p *ℤ r) x)
      ＝
        root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ q⁺ *ℕ⁺ positive-nat-ℤ⁺ s⁺)
          ( int-power-ℝ⁺ (p *ℤ r) x)
        by
          ap
            ( λ k → root-nonzero-nat-ℝ⁺ k _)
            ( positive-nat-mul-ℤ⁺ q⁺ s⁺)
      ＝
        root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ q⁺ *ℕ⁺ positive-nat-ℤ⁺ s⁺)
          ( int-power-ℝ⁺ r (int-power-ℝ⁺ p x))
          by
            ap
              ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺ *ℕ⁺ positive-nat-ℤ⁺ s⁺))
              ( int-power-mul-ℝ⁺ p r x)
      ＝
        root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ s⁺)
          ( root-nonzero-nat-ℝ⁺
            ( positive-nat-ℤ⁺ q⁺)
            ( int-power-ℝ⁺ r (int-power-ℝ⁺ p x)))
        by root-mul-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺) (positive-nat-ℤ⁺ s⁺) _
      ＝
        root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ s⁺)
          ( int-power-ℝ⁺
            ( r)
            ( root-nonzero-nat-ℝ⁺
              ( positive-nat-ℤ⁺ q⁺)
              ( int-power-ℝ⁺ p x)))
        by
          ap
            ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ s⁺))
            ( swap-root-nonzero-nat-int-power-ℝ⁺ (positive-nat-ℤ⁺ q⁺) r _)
```

### Similar integer fractions produce equal powers

```agda
abstract
  sim-int-fraction-power-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) (x : ℝ⁺ l) →
    sim-fraction-ℤ p q → int-fraction-power-ℝ⁺ p x ＝ int-fraction-power-ℝ⁺ q x
  sim-int-fraction-power-ℝ⁺ (p , q⁺) (r , s⁺) x ps=rq =
    is-injective-equiv
      ( aut-power-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ s⁺) ∘e
        aut-power-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺))
      ( equational-reasoning
        power-ℝ⁺
          ( nat-ℤ⁺ s⁺)
          ( power-ℝ⁺
            ( nat-ℤ⁺ q⁺)
            ( root-nonzero-nat-ℝ⁺
              ( positive-nat-ℤ⁺ q⁺)
              ( int-power-ℝ⁺ p x)))
        ＝ power-ℝ⁺ (nat-ℤ⁺ s⁺) (int-power-ℝ⁺ p x)
          by
            ap
              ( power-ℝ⁺ (nat-ℤ⁺ s⁺))
              ( is-section-root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺) _)
        ＝ int-power-ℝ⁺ (int-ℕ (nat-ℤ⁺ s⁺)) (int-power-ℝ⁺ p x)
          by inv (int-power-int-ℝ⁺ (nat-ℤ⁺ s⁺) (int-power-ℝ⁺ p x))
        ＝ int-power-ℝ⁺ (int-ℤ⁺ s⁺) (int-power-ℝ⁺ p x)
          by
            ap (λ k → int-power-ℝ⁺ (int-ℤ⁺ k) _) (is-section-positive-nat-ℤ⁺ s⁺)
        ＝ int-power-ℝ⁺ (p *ℤ int-ℤ⁺ s⁺) x
          by inv (int-power-mul-ℝ⁺ p (int-ℤ⁺ s⁺) x)
        ＝ int-power-ℝ⁺ (r *ℤ int-ℤ⁺ q⁺) x
          by ap (λ k → int-power-ℝ⁺ k _) ps=rq
        ＝ int-power-ℝ⁺ (int-ℤ⁺ q⁺) (int-power-ℝ⁺ r x)
          by int-power-mul-ℝ⁺ r (int-ℤ⁺ q⁺) x
        ＝ int-power-ℝ⁺ (int-ℕ (nat-ℤ⁺ q⁺)) (int-power-ℝ⁺ r x)
          by
            ap
              ( λ k → int-power-ℝ⁺ (int-ℤ⁺ k) _)
              ( inv (is-section-positive-nat-ℤ⁺ q⁺))
        ＝ power-ℝ⁺ (nat-ℤ⁺ q⁺) (int-power-ℝ⁺ r x)
          by int-power-int-ℝ⁺ (nat-ℤ⁺ q⁺) (int-power-ℝ⁺ r x)
        ＝
          power-ℝ⁺
            ( nat-ℤ⁺ s⁺)
            ( root-nonzero-nat-ℝ⁺
              ( positive-nat-ℤ⁺ s⁺)
              ( power-ℝ⁺ (nat-ℤ⁺ q⁺) (int-power-ℝ⁺ r x)))
          by inv (is-section-root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ s⁺) _)
        ＝
          power-ℝ⁺
            ( nat-ℤ⁺ s⁺)
            ( power-ℝ⁺
              ( nat-ℤ⁺ q⁺)
              ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ s⁺) (int-power-ℝ⁺ r x)))
          by
            ap
              ( power-ℝ⁺ (nat-ℤ⁺ s⁺))
              ( swap-root-nonzero-nat-power-ℝ⁺
                ( positive-nat-ℤ⁺ s⁺)
                ( nat-ℤ⁺ q⁺)
                ( _)))
```

### `xᵃ⁺ᵇ = xᵃxᵇ`

```agda
abstract
  int-fraction-power-add-ℝ⁺ :
    {l : Level} (p q : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (p +fraction-ℤ q) x ＝
    int-fraction-power-ℝ⁺ p x *ℝ⁺ int-fraction-power-ℝ⁺ q x
  int-fraction-power-add-ℝ⁺ p/q@(p , q⁺@(q , _)) r/s@(r , s⁺@(s , _)) x =
    equational-reasoning
      root-nonzero-nat-ℝ⁺
        ( positive-nat-ℤ⁺ (q⁺ *ℤ⁺ s⁺))
        ( int-power-ℝ⁺ (p *ℤ s +ℤ r *ℤ q) x)
      ＝
        root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ (q⁺ *ℤ⁺ s⁺))
          ( int-power-ℝ⁺ (p *ℤ s) x *ℝ⁺ int-power-ℝ⁺ (r *ℤ q) x)
        by
          ap
            ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ (q⁺ *ℤ⁺ s⁺)))
            ( distributive-int-power-add-ℝ⁺ (p *ℤ s) (r *ℤ q) x)
      ＝
        ( root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ (q⁺ *ℤ⁺ s⁺))
          ( int-power-ℝ⁺ (p *ℤ s) x)) *ℝ⁺
        ( root-nonzero-nat-ℝ⁺
          ( positive-nat-ℤ⁺ (q⁺ *ℤ⁺ s⁺))
          ( int-power-ℝ⁺ (r *ℤ q) x))
        by distributive-mul-root-nonzero-nat-ℝ⁺ _ _ _
      ＝ int-fraction-power-ℝ⁺ p/q x *ℝ⁺ int-fraction-power-ℝ⁺ r/s x
        by
          ap-mul-ℝ⁺
            ( sim-int-fraction-power-ℝ⁺ _ _ x
              ( associative-mul-ℤ p s q ∙ ap (p *ℤ_) (commutative-mul-ℤ s q)))
            ( sim-int-fraction-power-ℝ⁺ _ _ x (associative-mul-ℤ r q s))
```

### Reducing integer fractions preserves integer fraction powers

```agda
abstract
  reduce-int-fraction-power-ℝ⁺ :
    {l : Level} (q : fraction-ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (reduce-fraction-ℤ q) x ＝
    int-fraction-power-ℝ⁺ q x
  reduce-int-fraction-power-ℝ⁺ q x =
    sim-int-fraction-power-ℝ⁺
      ( reduce-fraction-ℤ q)
      ( q)
      ( x)
      ( symmetric-sim-fraction-ℤ _ _ (sim-reduced-fraction-ℤ q))
```

### `(xy)ᵖ = xᵖyᵖ`

```agda
abstract
  distributive-int-fraction-power-mul-ℝ⁺ :
    {l1 l2 : Level} (p : fraction-ℤ) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    int-fraction-power-ℝ⁺ p (x *ℝ⁺ y) ＝
    int-fraction-power-ℝ⁺ p x *ℝ⁺ int-fraction-power-ℝ⁺ p y
  distributive-int-fraction-power-mul-ℝ⁺ p/q@(p , q⁺) x y =
    ( ap
      ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺))
      ( distributive-int-power-mul-ℝ⁺ p x y)) ∙
    ( distributive-mul-root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺) _ _)
```

### The embedding of integers in integer fractions preserves powers

```agda
abstract
  in-int-fraction-power-ℝ⁺ :
    {l : Level} (k : ℤ) (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ (in-fraction-ℤ k) x ＝ int-power-ℝ⁺ k x
  in-int-fraction-power-ℝ⁺ k x =
    ( ap
      ( λ n → root-nonzero-nat-ℝ⁺ n (int-power-ℝ⁺ k x))
      ( eq-nonzero-ℕ {positive-nat-ℤ⁺ one-positive-ℤ} {one-ℕ⁺} refl)) ∙
    ( root-one-nonzero-nat-ℝ⁺ _)
```

### `x⁰ = 1`

```agda
abstract
  zero-int-fraction-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ zero-fraction-ℤ x ＝ raise-one-ℝ⁺ l
  zero-int-fraction-power-ℝ⁺ = in-int-fraction-power-ℝ⁺ zero-ℤ
```

### `x¹ = x`

```agda
abstract
  one-int-fraction-power-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) →
    int-fraction-power-ℝ⁺ one-fraction-ℤ x ＝ x
  one-int-fraction-power-ℝ⁺ x =
    in-int-fraction-power-ℝ⁺ one-ℤ x ∙ int-one-power-ℝ⁺ x
```

### `1ᵖ = 1`

```agda
abstract
  int-fraction-power-raise-one-ℝ⁺ :
    {l : Level} (p : fraction-ℤ) →
    int-fraction-power-ℝ⁺ p (raise-one-ℝ⁺ l) ＝ raise-one-ℝ⁺ l
  int-fraction-power-raise-one-ℝ⁺ (p , q⁺) =
    ( ap
      ( root-nonzero-nat-ℝ⁺ (positive-nat-ℤ⁺ q⁺))
      ( int-power-raise-one-ℝ⁺ _ p)) ∙
    ( root-nonzero-nat-raise-one-ℝ⁺ (positive-nat-ℤ⁺ q⁺))
```
