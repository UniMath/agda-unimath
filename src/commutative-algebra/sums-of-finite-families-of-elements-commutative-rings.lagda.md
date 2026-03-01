# Sums of finite families in commutative rings

```agda
module commutative-algebra.sums-of-finite-families-of-elements-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-of-finite-families-of-elements-commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-rings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.automorphisms
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-rings

open import ring-theory.sums-of-finite-families-of-elements-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a commutative ring" WD="sum" WDID=Q218005 Agda=sum-finite-Commutative-Ring}}
extends the binary addition operation on a
[commutative ring](commutative-algebra.commutative-rings.md) `A` to any family
of elements of `A` indexed by a
[finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-count-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : UU l2) → count A →
  (A → type-Commutative-Ring R) → type-Commutative-Ring R
sum-count-Commutative-Ring R =
  sum-count-Ring (ring-Commutative-Ring R)

sum-finite-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Commutative-Ring R) → type-Commutative-Ring R
sum-finite-Commutative-Ring R =
  sum-finite-Commutative-Semiring (commutative-semiring-Commutative-Ring R)
```

## Properties

### Sums over the unit types

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  sum-unit-finite-Commutative-Ring :
    (f : unit → type-Commutative-Ring A) →
    sum-finite-Commutative-Ring A unit-Finite-Type f ＝ f star
  sum-unit-finite-Commutative-Ring =
    sum-unit-finite-type-Ring (ring-Commutative-Ring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-sum-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Commutative-Ring R} → (f ~ g) →
    sum-finite-Commutative-Ring R A f ＝ sum-finite-Commutative-Ring R A g
  htpy-sum-finite-Commutative-Ring =
    htpy-sum-finite-Ring (ring-Commutative-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-sum-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) (x : type-Commutative-Ring R) →
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    mul-Commutative-Ring R x (sum-finite-Commutative-Ring R A f) ＝
    sum-finite-Commutative-Ring R A (mul-Commutative-Ring R x ∘ f)
  left-distributive-mul-sum-finite-Commutative-Ring =
    left-distributive-mul-sum-finite-Ring (ring-Commutative-Ring R)

  right-distributive-mul-sum-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (sum-finite-Commutative-Ring R A f) x ＝
    sum-finite-Commutative-Ring R A (mul-Commutative-Ring' R x ∘ f)
  right-distributive-mul-sum-finite-Commutative-Ring =
    right-distributive-mul-sum-finite-Ring (ring-Commutative-Ring R)
```

### Sums over finite types are preserved by equivalences

```agda
sum-equiv-finite-Commutative-Ring :
  {l1 l2 l3 : Level} (R : Commutative-Ring l1) →
  (A : Finite-Type l2) (B : Finite-Type l3) (H : equiv-Finite-Type A B) →
  (f : type-Finite-Type A → type-Commutative-Ring R) →
  sum-finite-Commutative-Ring R A f ＝
  sum-finite-Commutative-Ring R B (f ∘ map-inv-equiv H)
sum-equiv-finite-Commutative-Ring R =
  sum-equiv-finite-Commutative-Semiring
    ( commutative-semiring-Commutative-Ring R)

module _
  {l1 l2 : Level} (R : Commutative-Ring l1)
  (A : Finite-Type l2) (σ : Aut (type-Finite-Type A))
  where

  sum-aut-finite-Commutative-Ring :
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    sum-finite-Commutative-Ring R A f ＝
    sum-finite-Commutative-Ring R A (f ∘ map-equiv σ)
  sum-aut-finite-Commutative-Ring =
    sum-equiv-finite-Commutative-Ring R A A (inv-equiv σ)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  distributive-sum-coproduct-finite-Commutative-Ring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Commutative-Ring R) →
    sum-finite-Commutative-Ring R (coproduct-Finite-Type A B) f ＝
    add-Commutative-Ring
      ( R)
      ( sum-finite-Commutative-Ring R A (f ∘ inl))
      ( sum-finite-Commutative-Ring R B (f ∘ inr))
  distributive-sum-coproduct-finite-Commutative-Ring =
    distributive-sum-coproduct-finite-Ring (ring-Commutative-Ring R) A B
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  sum-Σ-finite-Commutative-Ring :
    (f :
      (a : type-Finite-Type A) →
      type-Finite-Type (B a) →
      type-Commutative-Ring R) →
    sum-finite-Commutative-Ring R (Σ-Finite-Type A B) (ind-Σ f) ＝
    sum-finite-Commutative-Ring
      R A (λ a → sum-finite-Commutative-Ring R (B a) (f a))
  sum-Σ-finite-Commutative-Ring =
    sum-Σ-finite-Ring (ring-Commutative-Ring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  eq-zero-sum-finite-is-empty-Commutative-Ring :
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    is-zero-Commutative-Ring R (sum-finite-Commutative-Ring R A f)
  eq-zero-sum-finite-is-empty-Commutative-Ring =
    is-zero-sum-finite-is-empty-Ring (ring-Commutative-Ring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
eq-sum-finite-sum-count-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Commutative-Ring R) →
  sum-finite-Commutative-Ring R A f ＝
  sum-count-Commutative-Ring R (type-Finite-Type A) cA f
eq-sum-finite-sum-count-Commutative-Ring R =
  eq-sum-finite-sum-count-Ring (ring-Commutative-Ring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  sum-zero-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Commutative-Ring R A (λ _ → zero-Commutative-Ring R) ＝
    zero-Commutative-Ring R
  sum-zero-finite-Commutative-Ring =
    sum-zero-finite-Ring (ring-Commutative-Ring R)
```
