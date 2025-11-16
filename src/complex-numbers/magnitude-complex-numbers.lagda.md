# Magnitude of complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.magnitude-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.multiplication-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.identity-types
open import foundation.universe-levels

open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

The
{{#concept "magnitude" WD="magnitude of a complex number" WDID=Q3317982 Agda=magnitude-ℂ}}
of a [complex number](complex-numbers.complex-numbers.md) $a + bi$ is defined as
$\sqrt{a^2 + b^2}$.

## Definition

```agda
nonnegative-squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-squared-magnitude-ℂ (a +iℂ b) =
  nonnegative-square-ℝ a +ℝ⁰⁺ nonnegative-square-ℝ b

squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ l
squared-magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

nonnegative-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-magnitude-ℂ z = sqrt-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

magnitude-ℂ : {l : Level} → ℂ l → ℝ l
magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-magnitude-ℂ z)
```

## Properties

### The square of the magnitude of `z` is the product of `z` and the conjugate of `z`

```agda
abstract
  eq-squared-magnitude-mul-conjugate-ℂ :
    {l : Level} (z : ℂ l) →
    z *ℂ conjugate-ℂ z ＝ complex-ℝ (squared-magnitude-ℂ z)
  eq-squared-magnitude-mul-conjugate-ℂ (a +iℂ b) =
    eq-ℂ
      ( equational-reasoning
        square-ℝ a -ℝ (b *ℝ neg-ℝ b)
        ＝ square-ℝ a -ℝ (neg-ℝ (square-ℝ b))
          by ap-diff-ℝ refl (right-negative-law-mul-ℝ _ _)
        ＝ square-ℝ a +ℝ square-ℝ b
          by ap-add-ℝ refl (neg-neg-ℝ _))
      ( eq-sim-ℝ
        ( similarity-reasoning-ℝ
          a *ℝ neg-ℝ b +ℝ b *ℝ a
          ~ℝ neg-ℝ (a *ℝ b) +ℝ a *ℝ b
            by
              sim-eq-ℝ
                ( ap-add-ℝ
                  ( right-negative-law-mul-ℝ a b)
                  ( commutative-mul-ℝ b a))
          ~ℝ zero-ℝ
            by left-inverse-law-add-ℝ (a *ℝ b)
          ~ℝ raise-ℝ _ zero-ℝ
            by sim-raise-ℝ _ _))
```

### The square of the magnitude of `zw` is the product of the squares of the magnitudes of `z` and `w`

```agda
abstract
  distributive-squared-magnitude-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    squared-magnitude-ℂ (z *ℂ w) ＝
    squared-magnitude-ℂ z *ℝ squared-magnitude-ℂ w
  distributive-squared-magnitude-mul-ℂ (a +iℂ b) (c +iℂ d) =
    equational-reasoning
      square-ℝ (a *ℝ c -ℝ b *ℝ d) +ℝ square-ℝ (a *ℝ d +ℝ b *ℝ c)
      ＝
        ( square-ℝ (a *ℝ c) +ℝ
          neg-ℝ (real-ℕ 2 *ℝ ((a *ℝ c) *ℝ (b *ℝ d))) +ℝ
          square-ℝ (b *ℝ d)) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)) +ℝ
          square-ℝ (b *ℝ c))
        by
          ap-add-ℝ
            ( square-diff-ℝ _ _)
            ( square-add-ℝ _ _)
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d) +ℝ
          neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d)))) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)))
        by
          ap-add-ℝ
            ( right-swap-add-ℝ _ _ _)
            ( right-swap-add-ℝ _ _ _)
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ ((a *ℝ c) *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)))
        by interchange-law-add-add-ℝ _ _ _ _
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ d *ℝ (c *ℝ b)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ
              ( refl)
              ( ap-mul-ℝ refl (ap-mul-ℝ refl (commutative-mul-ℝ b c))))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ c *ℝ (d *ℝ b)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ refl (ap-mul-ℝ refl (interchange-law-mul-mul-ℝ _ _ _ _)))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ
              ( refl)
              ( ap-mul-ℝ refl (ap-mul-ℝ refl (commutative-mul-ℝ d b))))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        zero-ℝ
        by eq-sim-ℝ (preserves-sim-left-add-ℝ _ _ _ (left-inverse-law-add-ℝ _))
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))
        by right-unit-law-add-ℝ _
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (a *ℝ d)) +ℝ
        ( square-ℝ (b *ℝ d) +ℝ square-ℝ (b *ℝ c))
        by interchange-law-add-add-ℝ _ _ _ _
      ＝
        ( square-ℝ a *ℝ square-ℝ c +ℝ square-ℝ a *ℝ square-ℝ d) +ℝ
        ( square-ℝ b *ℝ square-ℝ d +ℝ square-ℝ b *ℝ square-ℝ c)
        by
          ap-add-ℝ
            ( ap-add-ℝ
              ( distributive-square-mul-ℝ a c)
              ( distributive-square-mul-ℝ a d))
            ( ap-add-ℝ
              ( distributive-square-mul-ℝ b d)
              ( distributive-square-mul-ℝ b c))
      ＝
        square-ℝ a *ℝ (square-ℝ c +ℝ square-ℝ d) +ℝ
        square-ℝ b *ℝ (square-ℝ d +ℝ square-ℝ c)
        by
          inv
            ( ap-add-ℝ
              ( left-distributive-mul-add-ℝ _ _ _)
              ( left-distributive-mul-add-ℝ _ _ _))
      ＝
        square-ℝ a *ℝ (square-ℝ c +ℝ square-ℝ d) +ℝ
        square-ℝ b *ℝ (square-ℝ c +ℝ square-ℝ d)
        by ap-add-ℝ refl (ap-mul-ℝ refl (commutative-add-ℝ _ _))
      ＝
        (square-ℝ a +ℝ square-ℝ b) *ℝ (square-ℝ c +ℝ square-ℝ d)
        by
          inv
            ( right-distributive-mul-add-ℝ
              ( square-ℝ a)
              ( square-ℝ b)
              ( square-ℝ c +ℝ square-ℝ d))
```

### The magnitude of `zw` is the product of the magnitudes of `z` and `w`

```agda
abstract
  distributive-magnitude-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    magnitude-ℂ (z *ℂ w) ＝ magnitude-ℂ z *ℝ magnitude-ℂ w
  distributive-magnitude-mul-ℂ z w =
    equational-reasoning
      real-sqrt-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ (z *ℂ w))
      ＝
        real-sqrt-ℝ⁰⁺
          ( nonnegative-squared-magnitude-ℂ z *ℝ⁰⁺
            nonnegative-squared-magnitude-ℂ w)
        by
          ap
            ( real-sqrt-ℝ⁰⁺)
            ( eq-ℝ⁰⁺ _ _ (distributive-squared-magnitude-mul-ℂ z w))
      ＝ magnitude-ℂ z *ℝ magnitude-ℂ w
        by ap real-ℝ⁰⁺ (distributive-sqrt-mul-ℝ⁰⁺ _ _)
```
