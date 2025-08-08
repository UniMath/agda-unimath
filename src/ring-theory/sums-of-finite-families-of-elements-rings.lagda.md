# Sums of finite families of elements in rings

```agda
module ring-theory.sums-of-finite-families-of-elements-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.powers-of-elements-commutative-monoids

open import ring-theory.rings
open import ring-theory.sums-of-finite-families-of-elements-semirings
open import ring-theory.sums-of-finite-sequences-of-elements-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a ring" WD="sum" WDID=Q218005 Agda=sum-finite-Ring}}
extends the binary addition operation on a [ring](ring-theory.rings.md) `R` to
any family of elements of `R` indexed by a
[finite type](univalent-combinatorics.finite-types.md)

## Definition

```agda
sum-count-Ring :
  {l1 l2 : Level} (R : Ring l1) (A : UU l2) → count A → (A → type-Ring R) →
  type-Ring R
sum-count-Ring R = sum-count-Semiring (semiring-Ring R)

sum-finite-Ring :
  {l1 l2 : Level} (R : Ring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Ring R) → type-Ring R
sum-finite-Ring R = sum-finite-Semiring (semiring-Ring R)
```

## Properties

### Sums over the unit type

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-unit-finite-Ring :
    (f : unit → type-Ring R) → sum-finite-Ring R unit-Finite-Type f ＝ f star
  sum-unit-finite-Ring = sum-unit-finite-Semiring (semiring-Ring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-sum-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Ring R} → (f ~ g) →
    sum-finite-Ring R A f ＝ sum-finite-Ring R A g
  htpy-sum-finite-Ring = htpy-sum-finite-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-sum-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) (x : type-Ring R) →
    (f : type-Finite-Type A → type-Ring R) →
    mul-Ring R x (sum-finite-Ring R A f) ＝
    sum-finite-Ring R A (mul-Ring R x ∘ f)
  left-distributive-mul-sum-finite-Ring =
    left-distributive-mul-sum-finite-Semiring (semiring-Ring R)

  right-distributive-mul-sum-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    (f : type-Finite-Type A → type-Ring R) (x : type-Ring R) →
    mul-Ring R (sum-finite-Ring R A f) x ＝
    sum-finite-Ring R A (mul-Ring' R x ∘ f)
  right-distributive-mul-sum-finite-Ring =
    right-distributive-mul-sum-finite-Semiring (semiring-Ring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-zero-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Ring R A (λ _ → zero-Ring R) ＝ zero-Ring R
  sum-zero-finite-Ring = sum-zero-finite-Semiring (semiring-Ring R)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1) (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  sum-equiv-finite-Ring :
    (f : type-Finite-Type A → type-Ring R) →
    sum-finite-Ring R A f ＝
    sum-finite-Ring R B (f ∘ map-inv-equiv H)
  sum-equiv-finite-Ring = sum-equiv-finite-Semiring (semiring-Ring R) A B H
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  distributive-sum-coproduct-finite-Ring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Ring R) →
    sum-finite-Ring R (coproduct-Finite-Type A B) f ＝
    add-Ring
      ( R)
      ( sum-finite-Ring R A (f ∘ inl))
      ( sum-finite-Ring R B (f ∘ inr))
  distributive-sum-coproduct-finite-Ring =
    distributive-sum-coproduct-finite-Semiring (semiring-Ring R) A B
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (R : Ring l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  sum-Σ-finite-Ring :
    (f : (a : type-Finite-Type A) → type-Finite-Type (B a) → type-Ring R) →
    sum-finite-Ring R (Σ-Finite-Type A B) (ind-Σ f) ＝
    sum-finite-Ring R A (λ a → sum-finite-Ring R (B a) (f a))
  sum-Σ-finite-Ring = sum-Σ-finite-Semiring (semiring-Ring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  eq-zero-sum-finite-is-empty-Ring :
    (f : type-Finite-Type A → type-Ring R) →
    is-zero-Ring R (sum-finite-Ring R A f)
  eq-zero-sum-finite-is-empty-Ring =
    eq-zero-sum-finite-is-empty-Semiring (semiring-Ring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
eq-sum-finite-sum-count-Ring :
  {l1 l2 : Level} (R : Ring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A)) (f : type-Finite-Type A → type-Ring R) →
  sum-finite-Ring R A f ＝ sum-count-Ring R (type-Finite-Type A) cA f
eq-sum-finite-sum-count-Ring R =
  eq-sum-finite-sum-count-Semiring (semiring-Ring R)
```

### Sums of constant functions

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : Finite-Type l2)
  where

  sum-const-finite-type-Ring :
    (c : type-Ring R) →
    sum-finite-Ring R A (λ _ → c) ＝
    power-Commutative-Monoid
      ( additive-commutative-monoid-Ring R)
      ( number-of-elements-Finite-Type A)
      ( c)
  sum-const-finite-type-Ring =
    sum-const-finite-type-Semiring (semiring-Ring R) A
```
