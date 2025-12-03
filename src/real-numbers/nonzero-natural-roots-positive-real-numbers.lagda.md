# Nonzero natural roots of positive real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-natural-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.multiplicative-inverses-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-natural-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
```

</details>

## Idea

For any [nonzero](elementary-number-theory.nonzero-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) `n`, there exists
an inverse to the [power function](real-numbers.powers-real-numbers.md) `x ↦ xⁿ`
on the [positive](real-numbers.positive-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
abstract
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    is-positive-ℝ (real-ℝ⁰⁺ x) →
    is-positive-ℝ (real-root-pair-expansion-ℝ⁰⁺ u v x)
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ 0 v (x , _) 0<x =
    is-positive-odd-root-ℝ _ _ x 0<x
  preserves-is-positive-root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x⁰⁺ 0<x =
    preserves-is-positive-root-pair-expansion-ℝ⁰⁺
      ( u)
      ( v)
      ( sqrt-ℝ⁰⁺ x⁰⁺)
      ( is-positive-sqrt-is-positive-ℝ⁰⁺ x⁰⁺ 0<x)

  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    is-positive-ℝ (real-ℝ⁰⁺ x) →
    is-positive-ℝ (real-nonzero-nat-root-ℝ⁰⁺ n x)
  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ (succ-ℕ n , H) =
    preserves-is-positive-root-pair-expansion-ℝ⁰⁺ _ _
  preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ (0 , H) = ex-falso (H refl)

nonzero-nat-root-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ⁺ l
nonzero-nat-root-ℝ⁺ n x⁺@(x , 0<x) =
  ( real-nonzero-nat-root-ℝ⁰⁺ n (nonnegative-ℝ⁺ x⁺) ,
    preserves-is-positive-nonzero-nat-root-ℝ⁰⁺ n _ 0<x)
```

## Properties

### The `1`st root of `x` is `x`

```agda
abstract
  one-ℕ⁺-root-ℝ⁺ : {l : Level} (x : ℝ⁺ l) → nonzero-nat-root-ℝ⁺ one-ℕ⁺ x ＝ x
  one-ℕ⁺-root-ℝ⁺ x =
    eq-ℝ⁺ _ _ (ap real-ℝ⁰⁺ (root-one-ℝ⁰⁺ (nonnegative-ℝ⁺ x)))
```

### For nonzero `n`, `power-ℝ⁰⁺ n` is an automorphism on the positive real numbers

```agda
abstract
  is-section-nonzero-nat-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) →
    is-section (power-ℝ⁺ {l} (nat-nonzero-ℕ n)) (nonzero-nat-root-ℝ⁺ n)
  is-section-nonzero-nat-power-ℝ⁺ n x =
    eq-ℝ⁺
      ( power-ℝ⁺ (nat-nonzero-ℕ n) (nonzero-nat-root-ℝ⁺ n x))
      ( x)
      ( ap real-ℝ⁰⁺ (is-section-nonzero-nat-power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x)))

  is-retraction-nonzero-nat-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) →
    is-retraction (power-ℝ⁺ {l} (nat-nonzero-ℕ n)) (nonzero-nat-root-ℝ⁺ n)
  is-retraction-nonzero-nat-power-ℝ⁺ n x =
    eq-ℝ⁺
      ( nonzero-nat-root-ℝ⁺ n (power-ℝ⁺ (nat-nonzero-ℕ n) x))
      ( x)
      ( equational-reasoning
        real-nonzero-nat-root-ℝ⁰⁺
          ( n)
          ( nonnegative-ℝ⁺ (power-ℝ⁺ (nat-nonzero-ℕ n) x))
        ＝
          real-nonzero-nat-root-ℝ⁰⁺
            ( n)
            ( power-ℝ⁰⁺ (nat-nonzero-ℕ n) (nonnegative-ℝ⁺ x))
          by
            ap
              ( real-nonzero-nat-root-ℝ⁰⁺ n)
              ( eq-ℝ⁰⁺ _ _ (refl {x = power-ℝ (nat-nonzero-ℕ n) (real-ℝ⁺ x)}))
        ＝ real-ℝ⁺ x
          by
            ap
              ( real-ℝ⁰⁺)
              ( is-retraction-nonzero-nat-power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x)))

is-equiv-nonzero-power-ℝ⁺ :
  {l : Level} (n : ℕ⁺) → is-equiv (power-ℝ⁺ {l} (nat-nonzero-ℕ n))
is-equiv-nonzero-power-ℝ⁺ {l} n =
  is-equiv-is-invertible
    ( nonzero-nat-root-ℝ⁺ n)
    ( is-section-nonzero-nat-power-ℝ⁺ n)
    ( is-retraction-nonzero-nat-power-ℝ⁺ n)

aut-nonzero-power-ℝ⁺ : {l : Level} (n : ℕ⁺) → Aut (ℝ⁺ l)
aut-nonzero-power-ℝ⁺ n =
  ( power-ℝ⁺ (nat-nonzero-ℕ n) , is-equiv-nonzero-power-ℝ⁺ n)

abstract
  is-injective-nonzero-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) → is-injective (power-ℝ⁺ {l} (nat-nonzero-ℕ n))
  is-injective-nonzero-power-ℝ⁺ n =
    is-injective-is-equiv (is-equiv-nonzero-power-ℝ⁺ n)
```

### Integer powers and roots commute

```agda
abstract
  commute-root-int-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (k : ℤ) (x : ℝ⁺ l) →
    nonzero-nat-root-ℝ⁺ n (int-power-ℝ⁺ k x) ＝
    int-power-ℝ⁺ k (nonzero-nat-root-ℝ⁺ n x)
  commute-root-int-power-ℝ⁺ n⁺@(n , _) k x =
    inv
      ( is-injective-nonzero-power-ℝ⁺
        ( n⁺)
        ( equational-reasoning
          power-ℝ⁺ n (int-power-ℝ⁺ k (nonzero-nat-root-ℝ⁺ n⁺ x))
          ＝ int-power-ℝ⁺ (int-ℕ n) (int-power-ℝ⁺ k (nonzero-nat-root-ℝ⁺ n⁺ x))
            by inv (int-power-int-ℝ⁺ n _)
          ＝ int-power-ℝ⁺ k (int-power-ℝ⁺ (int-ℕ n) (nonzero-nat-root-ℝ⁺ n⁺ x))
            by commute-int-power-ℝ⁺ (int-ℕ n) k _
          ＝ int-power-ℝ⁺ k (power-ℝ⁺ n (nonzero-nat-root-ℝ⁺ n⁺ x))
            by ap (int-power-ℝ⁺ k) (int-power-int-ℝ⁺ n _)
          ＝ int-power-ℝ⁺ k x
            by ap (int-power-ℝ⁺ k) (is-section-nonzero-nat-power-ℝ⁺ n⁺ x)
          ＝ power-ℝ⁺ n (nonzero-nat-root-ℝ⁺ n⁺ (int-power-ℝ⁺ k x))
            by inv (is-section-nonzero-nat-power-ℝ⁺ n⁺ _)))
```

### Roots by products of nonzero natural numbers are iterated roots

```agda
abstract
  mul-nonzero-nat-root-ℝ⁺ :
    {l : Level} (m n : ℕ⁺) (x : ℝ⁺ l) →
    nonzero-nat-root-ℝ⁺ (m *ℕ⁺ n) x ＝
    nonzero-nat-root-ℝ⁺ m (nonzero-nat-root-ℝ⁺ n x)
  mul-nonzero-nat-root-ℝ⁺ m n x =
    eq-ℝ⁺ _ _
      ( ( ap real-ℝ⁰⁺ (mul-nonzero-nat-root-ℝ⁰⁺ m n (nonnegative-ℝ⁺ x))) ∙
        ( ap
          ( real-nonzero-nat-root-ℝ⁰⁺ m)
          ( eq-ℝ⁰⁺ _ _
            ( refl {x = real-nonzero-nat-root-ℝ⁰⁺ n (nonnegative-ℝ⁺ x)}))))
```

### Nonzero natural roots distribute over multiplication

```agda
abstract
  distributive-nonzero-nat-root-mul-ℝ⁺ :
    {l1 l2 : Level} (n : ℕ⁺) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    nonzero-nat-root-ℝ⁺ n (x *ℝ⁺ y) ＝
    nonzero-nat-root-ℝ⁺ n x *ℝ⁺ nonzero-nat-root-ℝ⁺ n y
  distributive-nonzero-nat-root-mul-ℝ⁺ n x⁺@(x , _) y⁺@(y , _) =
    eq-ℝ⁺ _ _
      ( ap
        ( real-ℝ⁰⁺)
        ( ( ap (nonzero-nat-root-ℝ⁰⁺ n) (eq-ℝ⁰⁺ _ _ (refl {x = x *ℝ y}))) ∙
          ( distributive-nonzero-nat-root-mul-ℝ⁰⁺
            ( n)
            ( nonnegative-ℝ⁺ x⁺)
            ( nonnegative-ℝ⁺ y⁺))))
```

### Nonzero natural roots and multiplicative inverses commute

```agda
abstract
  commute-inv-nonzero-nat-root-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    inv-ℝ⁺ (nonzero-nat-root-ℝ⁺ n x) ＝ nonzero-nat-root-ℝ⁺ n (inv-ℝ⁺ x)
  commute-inv-nonzero-nat-root-ℝ⁺ n x =
    equational-reasoning
      inv-ℝ⁺ (nonzero-nat-root-ℝ⁺ n x)
      ＝ int-power-ℝ⁺ neg-one-ℤ (nonzero-nat-root-ℝ⁺ n x)
        by inv (int-neg-one-power-ℝ⁺ _)
      ＝ nonzero-nat-root-ℝ⁺ n (int-power-ℝ⁺ neg-one-ℤ x)
        by inv (commute-root-int-power-ℝ⁺ n neg-one-ℤ x)
      ＝ nonzero-nat-root-ℝ⁺ n (inv-ℝ⁺ x)
        by ap (nonzero-nat-root-ℝ⁺ n) (int-neg-one-power-ℝ⁺ x)
```

### Any root of 1 is 1

```agda
abstract
  nonzero-nat-root-one-ℝ⁺ :
    (n : ℕ⁺) → nonzero-nat-root-ℝ⁺ n one-ℝ⁺ ＝ one-ℝ⁺
  nonzero-nat-root-one-ℝ⁺ n =
    eq-ℝ⁺ _ _
      ( ap real-ℝ⁰⁺
        ( ( ap (nonzero-nat-root-ℝ⁰⁺ n) (eq-ℝ⁰⁺ _ _ (refl {x = one-ℝ}))) ∙
          ( nonzero-nat-root-one-ℝ⁰⁺ n)))
```

## See also

- [Nonzero natural roots of nonnegative real numbers](real-numbers.nonzero-natural-roots-nonnegative-real-numbers.md)
