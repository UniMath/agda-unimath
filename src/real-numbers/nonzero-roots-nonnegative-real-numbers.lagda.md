# Nonzero roots of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-roots-nonnegative-real-numbers where
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
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.universe-levels

open import group-theory.powers-of-elements-large-monoids

open import real-numbers.dedekind-real-numbers
open import real-numbers.large-multiplicative-monoid-of-nonnegative-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.odd-roots-nonnegative-real-numbers
open import real-numbers.odd-roots-real-numbers
open import real-numbers.powers-nonnegative-real-numbers
open import real-numbers.powers-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
```

</details>

## Idea

For [nonzero](elementary-number-theory.nonzero-natural-numbers.md) `n`, the
{{#concept "nth root" WDID=Q601053 WD="nth root" Disambiguation="of a nonnegative real number" Agda=root-nonzero-nat-ℝ⁰⁺}}
is the inverse operation to the `n`th
[power](real-numbers.powers-nonnegative-real-numbers.md) operation on the
[nonnegative real numbers](real-numbers.nonnegative-real-numbers.md).

## Definition

```agda
opaque
  root-pair-expansion-ℝ⁰⁺ : {l : Level} → ℕ → ℕ → ℝ⁰⁺ l → ℝ⁰⁺ l
  root-pair-expansion-ℝ⁰⁺ 0 v x =
    root-is-odd-exponent-ℝ⁰⁺ _ (is-odd-has-odd-expansion _ (v , refl)) x
  root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x =
    root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x)

  root-nonzero-nat-ℝ⁰⁺ : {l : Level} → ℕ⁺ → ℝ⁰⁺ l → ℝ⁰⁺ l
  root-nonzero-nat-ℝ⁰⁺ (0 , H) _ = ex-falso (H refl)
  root-nonzero-nat-ℝ⁰⁺ (succ-ℕ n , _) =
    let ((u , v) , _) = has-pair-expansion n in
    root-pair-expansion-ℝ⁰⁺ u v

real-root-pair-expansion-ℝ⁰⁺ : {l : Level} → ℕ → ℕ → ℝ⁰⁺ l → ℝ l
real-root-pair-expansion-ℝ⁰⁺ u v x = real-ℝ⁰⁺ (root-pair-expansion-ℝ⁰⁺ u v x)

real-root-nonzero-nat-ℝ⁰⁺ : {l : Level} → ℕ⁺ → ℝ⁰⁺ l → ℝ l
real-root-nonzero-nat-ℝ⁰⁺ n x = real-ℝ⁰⁺ (root-nonzero-nat-ℝ⁰⁺ n x)
```

## Properties

### For nonzero `n`, the `n`th root is a section of the `n`th power operation

```agda
abstract opaque
  unfolding root-nonzero-nat-ℝ⁰⁺

  is-section-root-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    power-ℝ⁰⁺
      ( nat-ℕ⁺ (nonzero-pair-expansion u v))
      ( root-pair-expansion-ℝ⁰⁺ u v x) ＝
    x
  is-section-root-pair-expansion-ℝ⁰⁺ 0 v x =
    ( ap-binary power-ℝ⁰⁺ (left-unit-law-mul-ℕ _) refl) ∙
    ( is-section-root-is-odd-exponent-ℝ⁰⁺ _ _ x)
  is-section-root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x =
    equational-reasoning
      power-ℝ⁰⁺
        ( exp-ℕ 2 (succ-ℕ u) *ℕ succ-ℕ (v *ℕ 2))
        ( root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x)
      ＝
        power-ℝ⁰⁺
          ( exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2) *ℕ 2)
          ( root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x))
        by
          ap-binary
            ( power-ℝ⁰⁺)
            ( right-swap-mul-ℕ (exp-ℕ 2 u) 2 (succ-ℕ (v *ℕ 2)))
            ( refl)
      ＝
        square-ℝ⁰⁺
          ( power-ℝ⁰⁺
            ( exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2))
            ( root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x)))
        by power-mul-ℝ⁰⁺ (exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2)) 2
      ＝ square-ℝ⁰⁺ (sqrt-ℝ⁰⁺ x)
        by
          ap
            ( square-ℝ⁰⁺)
            ( is-section-root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ x))
      ＝ x
        by is-section-sqrt-ℝ⁰⁺ x

  is-section-root-nonzero-nat-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    power-ℝ⁰⁺ (nat-ℕ⁺ n) (root-nonzero-nat-ℝ⁰⁺ n x) ＝ x
  is-section-root-nonzero-nat-ℝ⁰⁺ (0 , H) _ = ex-falso (H refl)
  is-section-root-nonzero-nat-ℝ⁰⁺ (succ-ℕ n , _) x =
    let
      ((u , v) , eq-pair-expansion-u-v) = has-pair-expansion n
    in
      ( ap-binary power-ℝ⁰⁺ (inv eq-pair-expansion-u-v) refl) ∙
      ( is-section-root-pair-expansion-ℝ⁰⁺ u v x)
```

### For nonzero `n`, the `n`th root is a retraction of the `n`th power operation

```agda
abstract opaque
  unfolding root-nonzero-nat-ℝ⁰⁺

  is-retraction-root-pair-expansion-ℝ⁰⁺ :
    {l : Level} (u v : ℕ) (x : ℝ⁰⁺ l) →
    root-pair-expansion-ℝ⁰⁺ u v
      ( power-ℝ⁰⁺ (nat-ℕ⁺ (nonzero-pair-expansion u v)) x) ＝
    x
  is-retraction-root-pair-expansion-ℝ⁰⁺ 0 v x =
    ( ap
      ( root-is-odd-exponent-ℝ⁰⁺ _ _)
      ( ap-binary power-ℝ⁰⁺ (left-unit-law-mul-ℕ _) refl)) ∙
    ( is-retraction-root-is-odd-exponent-ℝ⁰⁺ _ _ x)
  is-retraction-root-pair-expansion-ℝ⁰⁺ (succ-ℕ u) v x =
    equational-reasoning
      root-pair-expansion-ℝ⁰⁺
        ( u)
        ( v)
        ( sqrt-ℝ⁰⁺ (power-ℝ⁰⁺ (exp-ℕ 2 (succ-ℕ u) *ℕ succ-ℕ (v *ℕ 2)) x))
      ＝
        root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( sqrt-ℝ⁰⁺ (power-ℝ⁰⁺ (exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2) *ℕ 2) x))
        by
          ap
            ( λ n → root-pair-expansion-ℝ⁰⁺ u v (sqrt-ℝ⁰⁺ (power-ℝ⁰⁺ n x)))
            ( right-swap-mul-ℕ (exp-ℕ 2 u) 2 (succ-ℕ (v *ℕ 2)))
      ＝
        root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( sqrt-ℝ⁰⁺ (square-ℝ⁰⁺ (power-ℝ⁰⁺ (exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2)) x)))
        by
          ap
            ( root-pair-expansion-ℝ⁰⁺ u v ∘ sqrt-ℝ⁰⁺)
            ( power-mul-ℝ⁰⁺ (exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2)) 2)
      ＝
        root-pair-expansion-ℝ⁰⁺
          ( u)
          ( v)
          ( power-ℝ⁰⁺ (exp-ℕ 2 u *ℕ succ-ℕ (v *ℕ 2)) x)
        by ap (root-pair-expansion-ℝ⁰⁺ u v) (is-retraction-sqrt-ℝ⁰⁺ _)
      ＝ x
        by is-retraction-root-pair-expansion-ℝ⁰⁺ u v x

  is-retraction-root-nonzero-nat-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (x : ℝ⁰⁺ l) →
    root-nonzero-nat-ℝ⁰⁺ n (power-ℝ⁰⁺ (nat-ℕ⁺ n) x) ＝ x
  is-retraction-root-nonzero-nat-ℝ⁰⁺ (0 , H) _ = ex-falso (H refl)
  is-retraction-root-nonzero-nat-ℝ⁰⁺ n⁺@(succ-ℕ n , _) x =
    let
      ((u , v) , eq-pair-expansion-u-v) = has-pair-expansion n
    in
      ( ap
        ( root-nonzero-nat-ℝ⁰⁺ n⁺)
        ( ap-binary power-ℝ⁰⁺ (inv eq-pair-expansion-u-v) refl)) ∙
      ( is-retraction-root-pair-expansion-ℝ⁰⁺ u v x)
```

### For nonzero `n`, the `n`th power operation is an automorphism on the nonnegative real numbers

```agda
is-equiv-power-nonzero-nat-ℝ⁰⁺ :
  (l : Level) (n : ℕ⁺) → is-equiv (power-ℝ⁰⁺ {l} (nat-ℕ⁺ n))
is-equiv-power-nonzero-nat-ℝ⁰⁺ l n =
  is-equiv-is-invertible
    ( root-nonzero-nat-ℝ⁰⁺ n)
    ( is-section-root-nonzero-nat-ℝ⁰⁺ n)
    ( is-retraction-root-nonzero-nat-ℝ⁰⁺ n)

aut-power-nonzero-nat-ℝ⁰⁺ : (l : Level) (n : ℕ⁺) → Aut (ℝ⁰⁺ l)
aut-power-nonzero-nat-ℝ⁰⁺ l n =
  ( power-ℝ⁰⁺ (nat-ℕ⁺ n) ,
    is-equiv-power-nonzero-nat-ℝ⁰⁺ l n)
```

### Roots and integer powers commute

```agda
abstract
  swap-root-nonzero-nat-power-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) (k : ℕ) (x : ℝ⁰⁺ l) →
    root-nonzero-nat-ℝ⁰⁺ n (power-ℝ⁰⁺ k x) ＝
    power-ℝ⁰⁺ k (root-nonzero-nat-ℝ⁰⁺ n x)
  swap-root-nonzero-nat-power-ℝ⁰⁺ n⁺@(n , _) k x =
    is-injective-equiv
      ( aut-power-nonzero-nat-ℝ⁰⁺ _ n⁺)
      ( equational-reasoning
        power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ (power-ℝ⁰⁺ k x))
        ＝ power-ℝ⁰⁺ k x
          by is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ _
        ＝ power-ℝ⁰⁺ k (power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ x))
          by ap (power-ℝ⁰⁺ k) (inv (is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ x))
        ＝ power-ℝ⁰⁺ n (power-ℝ⁰⁺ k (root-nonzero-nat-ℝ⁰⁺ n⁺ x))
          by swap-power-Large-Monoid large-monoid-mul-ℝ⁰⁺ k n _)
```

### The `mn`th root of `x` is the `n`th root of the `m`th root of `x`

```agda
abstract
  root-mul-nonzero-nat-ℝ⁰⁺ :
    {l : Level} (m n : ℕ⁺) (x : ℝ⁰⁺ l) →
    root-nonzero-nat-ℝ⁰⁺ (m *ℕ⁺ n) x ＝
    root-nonzero-nat-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ m x)
  root-mul-nonzero-nat-ℝ⁰⁺ m⁺@(m , _) n⁺@(n , _) x =
    is-injective-equiv
      ( aut-power-nonzero-nat-ℝ⁰⁺ _ (m⁺ *ℕ⁺ n⁺))
      ( equational-reasoning
        power-ℝ⁰⁺ (m *ℕ n) (root-nonzero-nat-ℝ⁰⁺ (m⁺ *ℕ⁺ n⁺) x)
        ＝ x
          by is-section-root-nonzero-nat-ℝ⁰⁺ (m⁺ *ℕ⁺ n⁺) x
        ＝ power-ℝ⁰⁺ m (root-nonzero-nat-ℝ⁰⁺ m⁺ x)
          by inv (is-section-root-nonzero-nat-ℝ⁰⁺ m⁺ x)
        ＝
          power-ℝ⁰⁺
            ( n)
            ( root-nonzero-nat-ℝ⁰⁺ n⁺ (power-ℝ⁰⁺ m (root-nonzero-nat-ℝ⁰⁺ m⁺ x)))
          by inv (is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ _)
        ＝
          power-ℝ⁰⁺
            ( n)
            ( power-ℝ⁰⁺ m (root-nonzero-nat-ℝ⁰⁺ n⁺ (root-nonzero-nat-ℝ⁰⁺ m⁺ x)))
          by ap (power-ℝ⁰⁺ n) (swap-root-nonzero-nat-power-ℝ⁰⁺ n⁺ m _)
        ＝
          power-ℝ⁰⁺
            ( m *ℕ n)
            ( root-nonzero-nat-ℝ⁰⁺ n⁺ (root-nonzero-nat-ℝ⁰⁺ m⁺ x))
          by inv (power-mul-ℝ⁰⁺ m n))
```

### `n`th roots distribute over multiplication

```agda
abstract
  distributive-mul-root-nonzero-nat-ℝ⁰⁺ :
    {l1 l2 : Level}
    (n : ℕ⁺) (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) →
    root-nonzero-nat-ℝ⁰⁺ n (x *ℝ⁰⁺ y) ＝
    root-nonzero-nat-ℝ⁰⁺ n x *ℝ⁰⁺ root-nonzero-nat-ℝ⁰⁺ n y
  distributive-mul-root-nonzero-nat-ℝ⁰⁺ n⁺@(n , _) x y =
    is-injective-equiv
      ( aut-power-nonzero-nat-ℝ⁰⁺ _ n⁺)
      ( equational-reasoning
        power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ (x *ℝ⁰⁺ y))
        ＝ x *ℝ⁰⁺ y
          by is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ _
        ＝
          power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ x) *ℝ⁰⁺
          power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ y)
          by
            inv
              ( ap-mul-ℝ⁰⁺
                ( is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ x)
                ( is-section-root-nonzero-nat-ℝ⁰⁺ n⁺ y))
        ＝
          power-ℝ⁰⁺ n (root-nonzero-nat-ℝ⁰⁺ n⁺ x *ℝ⁰⁺ root-nonzero-nat-ℝ⁰⁺ n⁺ y)
          by inv (distributive-power-mul-ℝ⁰⁺ n))
```

### The 1st root is the identity

```agda
abstract
  root-one-nonzero-nat-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) →
    root-nonzero-nat-ℝ⁰⁺ one-ℕ⁺ x ＝ x
  root-one-nonzero-nat-ℝ⁰⁺ = is-retraction-root-nonzero-nat-ℝ⁰⁺ one-ℕ⁺
```

### Any root of 1 is 1

```agda
abstract
  root-nonzero-nat-raise-one-ℝ⁰⁺ :
    {l : Level} (n : ℕ⁺) →
    root-nonzero-nat-ℝ⁰⁺ n (raise-one-ℝ⁰⁺ l) ＝ raise-one-ℝ⁰⁺ l
  root-nonzero-nat-raise-one-ℝ⁰⁺ n =
    ( ap (root-nonzero-nat-ℝ⁰⁺ n) (inv (power-raise-one-ℝ⁰⁺ (nat-ℕ⁺ n)))) ∙
    ( is-retraction-root-nonzero-nat-ℝ⁰⁺ n _)
```

## See also

- [Odd roots of real numbers](real-numbers.odd-roots-real-numbers.md)
- [Square roots of nonnegative real numbers](real-numbers.square-roots-nonnegative-real-numbers.md)

## External links

- [nth root](https://en.wikipedia.org/wiki/Nth_root) on Wikipedia
