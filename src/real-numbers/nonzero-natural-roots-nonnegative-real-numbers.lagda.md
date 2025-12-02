# Nonzero natural roots of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-natural-roots-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-of-two

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.injective-maps
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.odd-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

For any [nonzero](elementary-number-theory.nonzero-natural-numbers.md)
[natural number](elementary-number-theory.natural-numbers.md) `n`, there exists
an inverse to the [power function](real-numbers.powers-real-numbers.md) `x ↦ xⁿ`
on the [nonnegative](real-numbers.nonnegative-real-numbers.md)
[real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
root-pair-expansion-ℝ⁰⁺ : {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) → ℝ⁰⁺ l
root-pair-expansion-ℝ⁰⁺ 0 v x =
  odd-root-ℝ⁰⁺ (succ-ℕ (v *ℕ 2)) (is-odd-has-odd-expansion _ (v , refl)) x
root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x =
  root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x)

real-root-pair-expansion-ℝ⁰⁺ : {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) → ℝ l
real-root-pair-expansion-ℝ⁰⁺ u v x =
  real-ℝ⁰⁺ (root-pair-expansion-ℝ⁰⁺ u v x)

nonzero-nat-root-ℝ⁰⁺ : {l : Level} → ℕ⁺ → ℝ⁰⁺ l → ℝ⁰⁺ l
nonzero-nat-root-ℝ⁰⁺ (succ-ℕ n , H) =
  let
    ((u , v) , _) = has-pair-expansion n
  in root-pair-expansion-ℝ⁰⁺ u v
nonzero-nat-root-ℝ⁰⁺ (0 , H) = ex-falso (H refl)

real-nonzero-nat-root-ℝ⁰⁺ : {l : Level} → ℕ⁺ → ℝ⁰⁺ l → ℝ l
real-nonzero-nat-root-ℝ⁰⁺ n x = real-ℝ⁰⁺ (nonzero-nat-root-ℝ⁰⁺ n x)
```

## Properties

### The `n`th power of the `n`th root of `x` is `x`

```agda
abstract
  power-root-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    power-ℝ
      ( map-pair-expansion u v)
      ( real-root-pair-expansion-ℝ⁰⁺ u v x) ＝
    real-ℝ⁰⁺ x
  power-root-pair-expansion-ℝ⁰⁺ 0 v (x , _) =
    equational-reasoning
      power-ℝ (1 *ℕ succ-ℕ (v *ℕ 2)) _
      ＝
        power-ℝ
          ( succ-ℕ (v *ℕ 2))
          ( odd-root-ℝ
            ( succ-ℕ (v *ℕ 2))
            ( is-odd-has-odd-expansion _ (v , refl))
            ( x))
        by ap-binary power-ℝ (left-unit-law-mul-ℕ (succ-ℕ (v *ℕ 2))) refl
      ＝ x
        by
          odd-power-odd-root-ℝ
            ( succ-ℕ (v *ℕ 2))
            ( is-odd-has-odd-expansion _ (v , refl))
            ( x)
  power-root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x⁰⁺@(x , _) =
    equational-reasoning
      power-ℝ
        ( map-pair-expansion (succ-ℕ u) v)
        ( real-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x⁰⁺))
      ＝
        power-ℝ
          ( map-pair-expansion u v *ℕ 2)
          ( real-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x⁰⁺))
        by
          ap-binary
            ( power-ℝ)
            ( map-pair-expansion-succ-ℕ u v)
            ( refl)
      ＝
        square-ℝ
          ( power-ℝ
            ( map-pair-expansion u v)
            ( real-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x⁰⁺)))
        by power-mul-ℝ (map-pair-expansion u v) 2
      ＝ square-ℝ (real-sqrt-ℝ⁰⁺ x⁰⁺)
        by ap square-ℝ (power-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x⁰⁺))
      ＝ x
        by eq-real-square-sqrt-ℝ⁰⁺ x⁰⁺

abstract
  is-section-nonzero-nat-power-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    power-ℝ⁰⁺ (nat-nonzero-ℕ n) (nonzero-nat-root-ℝ⁰⁺ n x) ＝ x
  is-section-nonzero-nat-power-ℝ⁰⁺ (succ-ℕ n , H) x =
    let
      ((u , v) , H) = has-pair-expansion n
    in
      eq-ℝ⁰⁺ _ _
        ( ( ap-binary power-ℝ (inv H) refl) ∙
          ( power-root-pair-expansion-ℝ⁰⁺ u v x))
  is-section-nonzero-nat-power-ℝ⁰⁺ (0 , H) x = ex-falso (H refl)
```

### The `n`th root of the `n`th power of `x` is `x`

```agda
abstract
  root-power-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    real-ℝ⁰⁺
      ( root-pair-expansion-ℝ⁰⁺ u v (power-ℝ⁰⁺ (map-pair-expansion u v) x)) ＝
    real-ℝ⁰⁺ x
  root-power-pair-expansion-ℝ⁰⁺ 0 v (x , _) =
    equational-reasoning
      odd-root-ℝ
        ( succ-ℕ (v *ℕ 2))
        ( is-odd-has-odd-expansion _ (v , refl))
        ( power-ℝ (1 *ℕ succ-ℕ (v *ℕ 2)) x)
      ＝
        odd-root-ℝ
          ( succ-ℕ (v *ℕ 2))
          ( is-odd-has-odd-expansion _ (v , refl))
          ( power-ℝ (succ-ℕ (v *ℕ 2)) x)
        by
          ap
            ( λ n →
              odd-root-ℝ
                ( succ-ℕ (v *ℕ 2))
                ( is-odd-has-odd-expansion _ (v , refl))
                ( power-ℝ n x))
            ( left-unit-law-mul-ℕ (succ-ℕ (v *ℕ 2)))
      ＝ x
        by
          odd-root-odd-power-ℝ
            ( succ-ℕ (v *ℕ 2))
            ( is-odd-has-odd-expansion _ (v , refl))
            ( x)
  root-power-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x⁰⁺@(x , _) =
    equational-reasoning
      real-root-pair-expansion-ℝ⁰⁺
        ( u)
        ( v)
        ( sqrt-ℝ⁰⁺
          ( power-ℝ⁰⁺ (map-pair-expansion (succ-ℕ u) v) x⁰⁺))
      ＝
        real-root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( sqrt-ℝ⁰⁺
            ( power-ℝ⁰⁺ (map-pair-expansion u v *ℕ 2) x⁰⁺))
        by
          ap
            ( λ n →
              real-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ (power-ℝ⁰⁺ n x⁰⁺)))
            ( map-pair-expansion-succ-ℕ u v)
      ＝
        real-root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( sqrt-ℝ⁰⁺ (square-ℝ⁰⁺ (power-ℝ⁰⁺ (map-pair-expansion u v) x⁰⁺)))
        by
          ap
            ( λ y → real-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ y))
            ( eq-ℝ⁰⁺ _ _ (power-mul-ℝ (map-pair-expansion u v) 2))
      ＝
        real-root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( power-ℝ⁰⁺ (map-pair-expansion u v) x⁰⁺)
        by
          ap
            ( real-root-pair-expansion-ℝ⁰⁺ u v)
            ( is-retraction-square-ℝ⁰⁺ _)
      ＝ x
        by root-power-pair-expansion-ℝ⁰⁺ u v x⁰⁺

  is-retraction-nonzero-nat-power-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    nonzero-nat-root-ℝ⁰⁺ n (power-ℝ⁰⁺ (nat-nonzero-ℕ n) x) ＝ x
  is-retraction-nonzero-nat-power-ℝ⁰⁺ (succ-ℕ n , H) x =
    let
      ((u , v) , H) = has-pair-expansion n
    in
      eq-ℝ⁰⁺ _ _
        ( ( ap
            ( λ k → real-root-pair-expansion-ℝ⁰⁺ u v (power-ℝ⁰⁺ k x))
            ( inv H)) ∙
          ( root-power-pair-expansion-ℝ⁰⁺ u v x))
  is-retraction-nonzero-nat-power-ℝ⁰⁺ (0 , H) x = ex-falso (H refl)
```

### For nonzero `n`, `power-ℝ⁰⁺ n` is an automorphism on the nonnegative real numbers

```agda
is-equiv-nonzero-power-ℝ⁰⁺ :
  {l : Level} (n : ℕ⁺) → is-equiv (power-ℝ⁰⁺ {l} (nat-nonzero-ℕ n))
is-equiv-nonzero-power-ℝ⁰⁺ n =
  is-equiv-is-invertible
    ( nonzero-nat-root-ℝ⁰⁺ n)
    ( is-section-nonzero-nat-power-ℝ⁰⁺ n)
    ( is-retraction-nonzero-nat-power-ℝ⁰⁺ n)

aut-nonzero-power-ℝ⁰⁺ : {l : Level} (n : ℕ⁺) → Aut (ℝ⁰⁺ l)
aut-nonzero-power-ℝ⁰⁺ n⁺@(n , _) =
  ( power-ℝ⁰⁺ n , is-equiv-nonzero-power-ℝ⁰⁺ n⁺)
```

### The `1`st root of `x` is `x`

```agda
abstract
  root-one-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → nonzero-nat-root-ℝ⁰⁺ one-ℕ⁺ x ＝ x
  root-one-ℝ⁰⁺ x =
    is-injective-is-equiv
      ( is-equiv-nonzero-power-ℝ⁰⁺ one-ℕ⁺)
      ( ( is-section-nonzero-nat-power-ℝ⁰⁺ one-ℕ⁺ x) ∙
        ( eq-ℝ⁰⁺ _ _ (refl {x = real-ℝ⁰⁺ x})))
```

## See also

- [Nonzero natural roots of positive real numbers](real-numbers.nonzero-natural-roots-positive-real-numbers.md)
