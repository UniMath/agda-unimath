# Sums of elements in rings

```agda
module ring-theory.sums-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-rings

open import ring-theory.rings
open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="in a ring" WD="sum" WDID=Q218005 Agda=sum-Ring}}
extends the binary addition operation on a [ring](ring-theory.rings.md) `R` to
any family of elements of `R` indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md), or by
a [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-Ring :
  {l : Level} (R : Ring l) (n : ℕ) → functional-vec-Ring R n → type-Ring R
sum-Ring R = sum-Semiring (semiring-Ring R)

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

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-one-element-Ring :
    (f : functional-vec-Ring R 1) → sum-Ring R 1 f ＝ head-functional-vec 0 f
  sum-one-element-Ring = sum-one-element-Semiring (semiring-Ring R)

  sum-unit-finite-Ring :
    (f : unit → type-Ring R) → sum-finite-Ring R unit-Finite-Type f ＝ f star
  sum-unit-finite-Ring = sum-unit-finite-Semiring (semiring-Ring R)

  sum-two-elements-Ring :
    (f : functional-vec-Ring R 2) →
    sum-Ring R 2 f ＝ add-Ring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Ring = sum-two-elements-Semiring (semiring-Ring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Ring l)
  where

  htpy-sum-Ring :
    (n : ℕ) {f g : functional-vec-Ring R n} →
    (f ~ g) → sum-Ring R n f ＝ sum-Ring R n g
  htpy-sum-Ring = htpy-sum-Semiring (semiring-Ring R)

  htpy-sum-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Ring R} → (f ~ g) →
    sum-finite-Ring R A f ＝ sum-finite-Ring R A g
  htpy-sum-finite-Ring = htpy-sum-finite-Semiring (semiring-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Ring l)
  where

  cons-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → head-functional-vec n f ＝ x →
    sum-Ring R (succ-ℕ n) f ＝
    add-Ring R (sum-Ring R n (tail-functional-vec n f)) x
  cons-sum-Ring = cons-sum-Semiring (semiring-Ring R)

  snoc-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R (succ-ℕ n)) →
    {x : type-Ring R} → f (zero-Fin n) ＝ x →
    sum-Ring R (succ-ℕ n) f ＝
    add-Ring R
      ( x)
      ( sum-Ring R n (f ∘ inr-Fin n))
  snoc-sum-Ring = snoc-sum-Semiring (semiring-Ring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  left-distributive-mul-sum-Ring :
    (n : ℕ) (x : type-Ring R)
    (f : functional-vec-Ring R n) →
    mul-Ring R x (sum-Ring R n f) ＝
    sum-Ring R n (λ i → mul-Ring R x (f i))
  left-distributive-mul-sum-Ring =
    left-distributive-mul-sum-Semiring (semiring-Ring R)

  right-distributive-mul-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R n)
    (x : type-Ring R) →
    mul-Ring R (sum-Ring R n f) x ＝
    sum-Ring R n (λ i → mul-Ring R (f i) x)
  right-distributive-mul-sum-Ring =
    right-distributive-mul-sum-Semiring (semiring-Ring R)

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

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  interchange-add-sum-Ring :
    (n : ℕ) (f g : functional-vec-Ring R n) →
    add-Ring R
      ( sum-Ring R n f)
      ( sum-Ring R n g) ＝
    sum-Ring R n
      ( add-functional-vec-Ring R n f g)
  interchange-add-sum-Ring = interchange-add-sum-Semiring (semiring-Ring R)
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  extend-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R n) →
    sum-Ring R
      ( succ-ℕ n)
      ( cons-functional-vec-Ring R n (zero-Ring R) f) ＝
    sum-Ring R n f
  extend-sum-Ring = extend-sum-Semiring (semiring-Ring R)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Ring l)
  where

  shift-sum-Ring :
    (n : ℕ) (f : functional-vec-Ring R n) →
    sum-Ring R
      ( succ-ℕ n)
      ( snoc-functional-vec-Ring R n f
        ( zero-Ring R)) ＝
    sum-Ring R n f
  shift-sum-Ring = shift-sum-Semiring (semiring-Ring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Ring l)
  where

  sum-zero-Ring :
    (n : ℕ) → sum-Ring R n (zero-functional-vec-Ring R n) ＝ zero-Ring R
  sum-zero-Ring = sum-zero-Semiring (semiring-Ring R)

  sum-zero-finite-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Ring R A (λ _ → zero-Ring R) ＝ zero-Ring R
  sum-zero-finite-Ring = sum-zero-finite-Semiring (semiring-Ring R)
```

### Splitting sums

```agda
split-sum-Ring :
  {l : Level} (R : Ring l)
  (n m : ℕ) (f : functional-vec-Ring R (n +ℕ m)) →
  sum-Ring R (n +ℕ m) f ＝
  add-Ring R
    ( sum-Ring R n (f ∘ inl-coproduct-Fin n m))
    ( sum-Ring R m (f ∘ inr-coproduct-Fin n m))
split-sum-Ring R = split-sum-Semiring (semiring-Ring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Ring l)
  where

  preserves-sum-permutation-Ring :
    (n : ℕ) → (σ : Permutation n) →
    (f : functional-vec-Ring R n) →
    sum-Ring R n f ＝ sum-Ring R n (f ∘ map-equiv σ)
  preserves-sum-permutation-Ring =
    preserves-sum-permutation-Semiring (semiring-Ring R)
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

  sum-coproduct-finite-Ring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Ring R) →
    sum-finite-Ring R (coproduct-Finite-Type A B) f ＝
    add-Ring
      ( R)
      ( sum-finite-Ring R A (f ∘ inl))
      ( sum-finite-Ring R B (f ∘ inr))
  sum-coproduct-finite-Ring =
    sum-coproduct-finite-Semiring (semiring-Ring R) A B
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

  sum-is-empty-finite-Ring :
    (f : type-Finite-Type A → type-Ring R) →
    is-zero-Ring R (sum-finite-Ring R A f)
  sum-is-empty-finite-Ring = sum-is-empty-finite-Semiring (semiring-Ring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
sum-finite-count-Ring :
  {l1 l2 : Level} (R : Ring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A)) (f : type-Finite-Type A → type-Ring R) →
  sum-finite-Ring R A f ＝ sum-count-Ring R (type-Finite-Type A) cA f
sum-finite-count-Ring R = sum-finite-count-Semiring (semiring-Ring R)
```
