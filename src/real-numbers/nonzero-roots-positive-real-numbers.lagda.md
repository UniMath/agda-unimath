# Nonzero roots of positive real numbers

```agda
module real-numbers.nonzero-roots-positive-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.parity-natural-numbers
open import elementary-number-theory.powers-of-two

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.integer-powers-of-elements-large-groups

open import real-numbers.dedekind-real-numbers
open import real-numbers.integer-powers-positive-real-numbers
open import real-numbers.large-multiplicative-group-of-positive-real-numbers
open import real-numbers.multiplication-positive-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.nonzero-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-positive-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.powers-nonnegative-real-numbers
open import real-numbers.powers-positive-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.square-roots-positive-real-numbers
```

</details>

## Idea

For [nonzero](elementary-number-theory.nonzero-natural-numbers.md) `n`, the
{{#concept "nth root" Disambiguation="of a positive real number" Agda=root-nonzero-nat-ℝ⁺}}
is the inverse operation to the `n`th
[power](real-numbers.powers-positive-real-numbers.md) operation on the
[positive real numbers](real-numbers.positive-real-numbers.md).

## Definition

```agda
real-root-pair-expansion-ℝ⁺ : {l : Level} → ℕ → ℕ → ℝ⁺ l → ℝ l
real-root-pair-expansion-ℝ⁺ u v x =
  real-root-pair-expansion-ℝ⁰⁺ u v (nonnegative-ℝ⁺ x)

real-root-nonzero-nat-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ l
real-root-nonzero-nat-ℝ⁺ n x =
  real-ℝ⁰⁺ (root-nonzero-nat-ℝ⁰⁺ n (nonnegative-ℝ⁺ x))

abstract opaque
  unfolding root-pair-expansion-ℝ⁰⁺

  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁺ l) →
    is-positive-ℝ (real-root-pair-expansion-ℝ⁺ u v x)
  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ zero-ℕ v x =
    is-positive-root-is-odd-exponent-real-ℝ⁺
      ( succ-ℕ (v *ℕ 2))
      ( is-odd-has-odd-expansion _ (v , refl))
      ( x)
  is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ (succ-ℕ u) v x =
    tr
      ( is-positive-ℝ ∘ real-root-pair-expansion-ℝ⁰⁺ u v)
      ( eq-ℝ⁰⁺ _ _ refl)
      ( is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ u v (sqrt-ℝ⁺ x))

  is-positive-real-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    is-positive-ℝ (real-root-nonzero-nat-ℝ⁺ n x)
  is-positive-real-root-nonzero-nat-ℝ⁺ (0 , H) = ex-falso (H refl)
  is-positive-real-root-nonzero-nat-ℝ⁺ (succ-ℕ n , _) x =
    let ((u , v) , _) = has-pair-expansion n in
    is-positive-real-root-pair-expansion-nonnegative-ℝ⁺ u v x

root-nonzero-nat-ℝ⁺ : {l : Level} → ℕ⁺ → ℝ⁺ l → ℝ⁺ l
root-nonzero-nat-ℝ⁺ n x =
  ( real-root-nonzero-nat-ℝ⁺ n x ,
    is-positive-real-root-nonzero-nat-ℝ⁺ n x)
```

## Properties

### The root operation is the inverse of the power operation

```agda
abstract
  is-section-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    power-ℝ⁺ (nat-ℕ⁺ n) (root-nonzero-nat-ℝ⁺ n x) ＝ x
  is-section-root-nonzero-nat-ℝ⁺ n⁺@(n , _) x =
    eq-ℝ⁺ _ _
      ( equational-reasoning
        real-ℝ⁺ (power-ℝ⁺ n (root-nonzero-nat-ℝ⁺ n⁺ x))
        ＝ power-ℝ n (real-root-nonzero-nat-ℝ⁺ n⁺ x)
          by real-power-ℝ⁺ n _
        ＝ real-ℝ⁰⁺ (power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))
          by inv (real-power-ℝ⁰⁺ n _)
        ＝ real-ℝ⁺ x
          by
            ap real-ℝ⁰⁺ (is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))

  is-retraction-root-nonzero-nat-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁺ l) →
    root-nonzero-nat-ℝ⁺ n (power-ℝ⁺ (nat-ℕ⁺ n) x) ＝ x
  is-retraction-root-nonzero-nat-ℝ⁺ n⁺@(n , _) x =
    eq-ℝ⁺ _ _
      ( equational-reasoning
        real-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ (power-ℝ⁺ n x))
        ＝ real-root-nonzero-nat-ℝ⁰⁺ n⁺ (power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x))
          by
            ap
              ( real-root-nonzero-nat-ℝ⁰⁺ n⁺)
              ( eq-ℝ⁰⁺ _ _
                ( ( real-power-ℝ⁺ n x) ∙
                  ( inv (real-power-ℝ⁰⁺ n (nonnegative-ℝ⁺ x)))))
        ＝ real-ℝ⁺ x
          by
            ap
              ( real-ℝ⁰⁺)
              ( is-retraction-root-nonzero-nat-ℝ⁰⁺ n⁺ (nonnegative-ℝ⁺ x)))

is-equiv-power-nonzero-nat-ℝ⁺ :
  {l : Level} (n : ℕ⁺) → is-equiv (power-ℝ⁺ {l} (nat-ℕ⁺ n))
is-equiv-power-nonzero-nat-ℝ⁺ n =
  is-equiv-is-invertible
    ( root-nonzero-nat-ℝ⁺ n)
    ( is-section-root-nonzero-nat-ℝ⁺ n)
    ( is-retraction-root-nonzero-nat-ℝ⁺ n)

aut-power-nonzero-nat-ℝ⁺ :
  {l : Level} (n : ℕ⁺) → Aut (ℝ⁺ l)
aut-power-nonzero-nat-ℝ⁺ n =
  ( power-ℝ⁺ (nat-ℕ⁺ n) ,
    is-equiv-power-nonzero-nat-ℝ⁺ n)
```

### Roots and integer powers commute

```agda
abstract
  swap-root-nonzero-nat-int-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (k : ℤ) (x : ℝ⁺ l) →
    root-nonzero-nat-ℝ⁺ n (int-power-ℝ⁺ k x) ＝
    int-power-ℝ⁺ k (root-nonzero-nat-ℝ⁺ n x)
  swap-root-nonzero-nat-int-power-ℝ⁺ n⁺@(n , _) k x =
    is-injective-equiv
      ( aut-power-nonzero-nat-ℝ⁺ n⁺)
      ( equational-reasoning
        power-ℝ⁺ n (root-nonzero-nat-ℝ⁺ n⁺ (int-power-ℝ⁺ k x))
        ＝ int-power-ℝ⁺ k x
          by is-section-root-nonzero-nat-ℝ⁺ n⁺ _
        ＝ int-power-ℝ⁺ k (power-ℝ⁺ n (root-nonzero-nat-ℝ⁺ n⁺ x))
          by ap (int-power-ℝ⁺ k) (inv (is-section-root-nonzero-nat-ℝ⁺ n⁺ x))
        ＝ power-ℝ⁺ n (int-power-ℝ⁺ k (root-nonzero-nat-ℝ⁺ n⁺ x))
          by swap-int-power-power-Large-Group large-group-mul-ℝ⁺ k n _)
```

### Roots and natural powers commute

```agda
abstract
  swap-root-nonzero-nat-power-ℝ⁺ :
    {l : Level} (n : ℕ⁺) (k : ℕ) (x : ℝ⁺ l) →
    root-nonzero-nat-ℝ⁺ n (power-ℝ⁺ k x) ＝
    power-ℝ⁺ k (root-nonzero-nat-ℝ⁺ n x)
  swap-root-nonzero-nat-power-ℝ⁺ n k x =
    equational-reasoning
      root-nonzero-nat-ℝ⁺ n (power-ℝ⁺ k x)
      ＝ root-nonzero-nat-ℝ⁺ n (int-power-ℝ⁺ (int-ℕ k) x)
        by ap (root-nonzero-nat-ℝ⁺ n) (inv (int-power-int-ℝ⁺ k x))
      ＝ int-power-ℝ⁺ (int-ℕ k) (root-nonzero-nat-ℝ⁺ n x)
        by swap-root-nonzero-nat-int-power-ℝ⁺ n (int-ℕ k) x
      ＝ power-ℝ⁺ k (root-nonzero-nat-ℝ⁺ n x)
        by int-power-int-ℝ⁺ k _
```

### The `mn`th root of `x` is the `n`th root of the `m`th root of `x`

```agda
abstract
  root-mul-nonzero-nat-ℝ⁺ :
    {l : Level} (m n : ℕ⁺) (x : ℝ⁺ l) →
    root-nonzero-nat-ℝ⁺ (m *ℕ⁺ n) x ＝
    root-nonzero-nat-ℝ⁺ n (root-nonzero-nat-ℝ⁺ m x)
  root-mul-nonzero-nat-ℝ⁺ m n x =
    eq-ℝ⁺ _ _
      ( ( ap
          ( real-ℝ⁰⁺)
          ( root-mul-nonzero-nat-ℝ⁰⁺ m n (nonnegative-ℝ⁺ x))) ∙
        ( ap
          ( real-root-nonzero-nat-ℝ⁰⁺ n)
          ( eq-ℝ⁰⁺ _ _ refl)))
```

### `n`th roots distribute over multiplication

```agda
abstract
  distributive-mul-root-nonzero-nat-ℝ⁺ :
    {l1 l2 : Level}
    (n : ℕ⁺) (x : ℝ⁺ l1) (y : ℝ⁺ l2) →
    root-nonzero-nat-ℝ⁺ n (x *ℝ⁺ y) ＝
    root-nonzero-nat-ℝ⁺ n x *ℝ⁺ root-nonzero-nat-ℝ⁺ n y
  distributive-mul-root-nonzero-nat-ℝ⁺ n x y =
    eq-ℝ⁺ _ _
      ( ( ap (real-root-nonzero-nat-ℝ⁰⁺ n) (eq-ℝ⁰⁺ _ _ refl)) ∙
        ( ap
          ( real-ℝ⁰⁺)
          ( distributive-mul-root-nonzero-nat-ℝ⁰⁺
            ( n)
            ( nonnegative-ℝ⁺ x)
            ( nonnegative-ℝ⁺ y))))
```

### The 1st root is the identity

```agda
abstract
  root-one-nonzero-nat-ℝ⁺ :
    {l : Level} (x : ℝ⁺ l) → root-nonzero-nat-ℝ⁺ one-ℕ⁺ x ＝ x
  root-one-nonzero-nat-ℝ⁺ = is-retraction-root-nonzero-nat-ℝ⁺ one-ℕ⁺
```

### Any root of 1 is 1

```agda
abstract
  root-nonzero-nat-raise-one-ℝ⁺ :
    {l : Level} (n : ℕ⁺) →
    root-nonzero-nat-ℝ⁺ n (raise-one-ℝ⁺ l) ＝ raise-one-ℝ⁺ l
  root-nonzero-nat-raise-one-ℝ⁺ n =
    ( ap (root-nonzero-nat-ℝ⁺ n) (inv (power-raise-one-ℝ⁺ (nat-ℕ⁺ n)))) ∙
    ( is-retraction-root-nonzero-nat-ℝ⁺ n _)
```
