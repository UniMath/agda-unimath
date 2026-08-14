# The multiplicative group of positive rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.multiplicative-group-of-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.inequality-positive-rational-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-rational-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-monoid-of-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-integers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.submonoids
```

</details>

## Idea

The [submonoid](group-theory.submonoids.md) of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
in the
[multiplicative monoid of rational numbers](elementary-number-theory.multiplicative-monoid-of-rational-numbers.md)
is a [commutative group](group-theory.abelian-groups.md).

## Definitions

### The positive inverse of a positive rational number

```agda
opaque
  unfolding inv-is-positive-ℚ

  inv-ℚ⁺ : ℚ⁺ → ℚ⁺
  pr1 (inv-ℚ⁺ (x , P)) = inv-is-positive-ℚ x P
  pr2 (inv-ℚ⁺ (x , P)) = is-positive-denominator-ℚ x

rational-inv-ℚ⁺ : ℚ⁺ → ℚ
rational-inv-ℚ⁺ q = rational-ℚ⁺ (inv-ℚ⁺ q)

is-positive-rational-inv-ℚ⁺ : (q : ℚ⁺) → is-positive-ℚ (rational-inv-ℚ⁺ q)
is-positive-rational-inv-ℚ⁺ q = is-positive-rational-ℚ⁺ (inv-ℚ⁺ q)
```

### Inverse laws in the multiplicative group of positive rational numbers

```agda
opaque
  unfolding inv-ℚ⁺

  left-inverse-law-mul-ℚ⁺ : (x : ℚ⁺) → (inv-ℚ⁺ x) *ℚ⁺ x ＝ one-ℚ⁺
  left-inverse-law-mul-ℚ⁺ x =
    eq-ℚ⁺
      ( left-inverse-law-mul-is-positive-ℚ
        ( rational-ℚ⁺ x)
        ( is-positive-rational-ℚ⁺ x))

  right-inverse-law-mul-ℚ⁺ : (x : ℚ⁺) → x *ℚ⁺ (inv-ℚ⁺ x) ＝ one-ℚ⁺
  right-inverse-law-mul-ℚ⁺ x =
    eq-ℚ⁺
      ( right-inverse-law-mul-is-positive-ℚ
        ( rational-ℚ⁺ x)
        ( is-positive-rational-ℚ⁺ x))
```

### The multiplicative group of positive rational numbers

```agda
group-mul-ℚ⁺ : Group lzero
pr1 group-mul-ℚ⁺ = semigroup-mul-ℚ⁺
pr1 (pr2 group-mul-ℚ⁺) = is-unital-Monoid monoid-mul-ℚ⁺
pr1 (pr2 (pr2 group-mul-ℚ⁺)) = inv-ℚ⁺
pr1 (pr2 (pr2 (pr2 group-mul-ℚ⁺))) = left-inverse-law-mul-ℚ⁺
pr2 (pr2 (pr2 (pr2 group-mul-ℚ⁺))) = right-inverse-law-mul-ℚ⁺
```

## Properties

### The multiplicative group of positive rational numbers is commutative

```agda
abelian-group-mul-ℚ⁺ : Ab lzero
pr1 abelian-group-mul-ℚ⁺ = group-mul-ℚ⁺
pr2 abelian-group-mul-ℚ⁺ = commutative-mul-ℚ⁺
```

### Inversion reverses inequality on the positive rational numbers

```agda
opaque
  unfolding inv-ℚ⁺
  unfolding leq-ℚ-Prop

  inv-leq-ℚ⁺ : (x y : ℚ⁺) → leq-ℚ⁺ x y → leq-ℚ⁺ (inv-ℚ⁺ y) (inv-ℚ⁺ x)
  inv-leq-ℚ⁺ x y =
    binary-tr
      ( leq-ℤ)
      ( commutative-mul-ℤ _ _)
      ( commutative-mul-ℤ _ _)
```

### Inversion is an involution

```agda
abstract
  inv-inv-ℚ⁺ : (q : ℚ⁺) → inv-ℚ⁺ (inv-ℚ⁺ q) ＝ q
  inv-inv-ℚ⁺ = inv-inv-Group group-mul-ℚ⁺

  rational-inv-inv-ℚ⁺ : (q : ℚ⁺) → rational-inv-ℚ⁺ (inv-ℚ⁺ q) ＝ rational-ℚ⁺ q
  rational-inv-inv-ℚ⁺ q = ap rational-ℚ⁺ (inv-inv-ℚ⁺ q)
```

### Inversion reverses strict inequality on the positive rational numbers

```agda
opaque
  unfolding inv-ℚ⁺
  unfolding le-ℚ-Prop

  inv-le-ℚ⁺ : (x y : ℚ⁺) → le-ℚ⁺ x y → le-ℚ⁺ (inv-ℚ⁺ y) (inv-ℚ⁺ x)
  inv-le-ℚ⁺ x y =
    binary-tr
      ( le-ℤ)
      ( commutative-mul-ℤ _ _)
      ( commutative-mul-ℤ _ _)

  inv-le-ℚ⁺' : (x y : ℚ⁺) → le-ℚ⁺ (inv-ℚ⁺ x) (inv-ℚ⁺ y) → le-ℚ⁺ y x
  inv-le-ℚ⁺' x y =
    binary-tr
      ( le-ℤ)
      ( commutative-mul-ℤ _ _)
      ( commutative-mul-ℤ _ _)
```

### Inversion of positive rational numbers distributes over multiplication

```agda
abstract
  distributive-inv-mul-ℚ⁺ :
    (x y : ℚ⁺) → inv-ℚ⁺ (x *ℚ⁺ y) ＝ inv-ℚ⁺ x *ℚ⁺ inv-ℚ⁺ y
  distributive-inv-mul-ℚ⁺ x y =
    distributive-inv-mul-Group'
      ( group-mul-ℚ⁺)
      ( x)
      ( y)
      ( commutative-mul-ℚ⁺ x y)
```

### Inversion on the positive rational numbers interchanges numerator and denominator

```agda
module _
  (x : ℚ⁺)
  where

  opaque
    unfolding inv-ℚ⁺

    eq-numerator-inv-denominator-ℚ⁺ :
      numerator-ℚ⁺ (inv-ℚ⁺ x) ＝ denominator-ℚ⁺ x
    eq-numerator-inv-denominator-ℚ⁺ =
      ind-Σ eq-numerator-inv-denominator-is-positive-ℚ x

    eq-denominator-inv-numerator-ℚ⁺ :
      denominator-ℚ⁺ (inv-ℚ⁺ x) ＝ numerator-ℚ⁺ x
    eq-denominator-inv-numerator-ℚ⁺ =
      ind-Σ eq-denominator-inv-numerator-is-positive-ℚ x
```

### Group laws on the positive rational numbers

```agda
abstract
  is-section-left-div-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) → rational-ℚ⁺ p *ℚ (rational-inv-ℚ⁺ p *ℚ q) ＝ q
  is-section-left-div-ℚ⁺ p⁺@(p , _) q =
    equational-reasoning
      p *ℚ (rational-inv-ℚ⁺ p⁺ *ℚ q)
      ＝ (p *ℚ rational-inv-ℚ⁺ p⁺) *ℚ q
        by inv (associative-mul-ℚ p _ q)
      ＝ one-ℚ *ℚ q
        by ap-mul-ℚ (ap rational-ℚ⁺ (right-inverse-law-mul-ℚ⁺ p⁺)) refl
      ＝ q
        by left-unit-law-mul-ℚ q

  is-section-right-div-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) → (q *ℚ rational-inv-ℚ⁺ p) *ℚ rational-ℚ⁺ p ＝ q
  is-section-right-div-ℚ⁺ p⁺@(p , _) q =
    equational-reasoning
      (q *ℚ rational-inv-ℚ⁺ p⁺) *ℚ p
      ＝ q *ℚ rational-ℚ⁺ (inv-ℚ⁺ p⁺ *ℚ⁺ p⁺)
        by associative-mul-ℚ _ _ _
      ＝ q *ℚ one-ℚ
        by ap-mul-ℚ refl (ap rational-ℚ⁺ (left-inverse-law-mul-ℚ⁺ p⁺))
      ＝ q
        by right-unit-law-mul-ℚ q

  is-retraction-left-div-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) → rational-ℚ⁺ (inv-ℚ⁺ p) *ℚ (rational-ℚ⁺ p *ℚ q) ＝ q
  is-retraction-left-div-ℚ⁺ p⁺@(p , _) q =
    equational-reasoning
      rational-ℚ⁺ (inv-ℚ⁺ p⁺) *ℚ (p *ℚ q)
      ＝ rational-ℚ⁺ (inv-ℚ⁺ p⁺ *ℚ⁺ p⁺) *ℚ q
        by inv (associative-mul-ℚ _ _ _)
      ＝ rational-ℚ⁺ one-ℚ⁺ *ℚ q
        by ap (λ r → rational-ℚ⁺ r *ℚ q) (left-inverse-law-mul-ℚ⁺ p⁺)
      ＝ q
        by left-unit-law-mul-ℚ q

  is-retraction-right-div-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) → (q *ℚ rational-ℚ⁺ p) *ℚ rational-ℚ⁺ (inv-ℚ⁺ p) ＝ q
  is-retraction-right-div-ℚ⁺ p⁺@(p , _) q =
    equational-reasoning
      (q *ℚ p) *ℚ rational-ℚ⁺ (inv-ℚ⁺ p⁺)
      ＝ q *ℚ rational-ℚ⁺ (p⁺ *ℚ⁺ inv-ℚ⁺ p⁺)
        by associative-mul-ℚ _ _ _
      ＝ q *ℚ rational-ℚ⁺ one-ℚ⁺
        by ap (λ r → q *ℚ rational-ℚ⁺ r) (right-inverse-law-mul-ℚ⁺ p⁺)
      ＝ q
        by right-unit-law-mul-ℚ q
```

### Multiplication by a positive rational number reflects strict inequality

```agda
abstract
  reflects-le-left-mul-ℚ⁺ :
    (p : ℚ⁺) (q r : ℚ) →
    le-ℚ (rational-ℚ⁺ p *ℚ q) (rational-ℚ⁺ p *ℚ r) →
    le-ℚ q r
  reflects-le-left-mul-ℚ⁺ p⁺@(p , _) q r pq<pr =
    binary-tr
      ( le-ℚ)
      ( is-retraction-left-div-ℚ⁺ p⁺ q)
      ( is-retraction-left-div-ℚ⁺ p⁺ r)
      ( preserves-strict-order-left-mul-ℚ⁺ (inv-ℚ⁺ p⁺) _ _ pq<pr)
```

### The inverse of 1 is 1

```agda
abstract
  inv-one-ℚ⁺ : inv-ℚ⁺ one-ℚ⁺ ＝ one-ℚ⁺
  inv-one-ℚ⁺ = inv-unit-Group group-mul-ℚ⁺
```

### Multiplication by a positive rational number is cofinal and coinitial

```agda
abstract
  is-cofinal-left-mul-rational-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) →
    exists ℚ (λ r → leq-ℚ-Prop q (rational-ℚ⁺ p *ℚ r))
  is-cofinal-left-mul-rational-ℚ⁺ p q =
    intro-exists
      ( rational-inv-ℚ⁺ p *ℚ q)
      ( leq-eq-ℚ (inv (is-section-left-div-ℚ⁺ p q)))

  is-coinitial-left-mul-rational-ℚ⁺ :
    (p : ℚ⁺) (q : ℚ) →
    exists ℚ (λ r → leq-ℚ-Prop (rational-ℚ⁺ p *ℚ r) q)
  is-coinitial-left-mul-rational-ℚ⁺ p q =
    intro-exists
      ( rational-inv-ℚ⁺ p *ℚ q)
      ( leq-eq-ℚ (is-section-left-div-ℚ⁺ p q))
```
