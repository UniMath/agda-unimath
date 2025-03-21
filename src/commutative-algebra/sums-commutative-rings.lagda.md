# Sums in commutative rings

```agda
module commutative-algebra.sums-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.sums-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.automorphisms
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-rings

open import ring-theory.sums-rings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **sum operation** extends the binary addition operation on a
[commutative ring](commutative-algebra.commutative-rings.md) `A` to any family
of elements of `A` indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md), or by
a [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l) (n : ℕ) →
  (functional-vec-Commutative-Ring A n) → type-Commutative-Ring A
sum-Commutative-Ring A = sum-Ring (ring-Commutative-Ring A)

sum-count-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : UU l2) → count A →
  (A → type-Commutative-Ring R) → type-Commutative-Ring R
sum-count-Commutative-Ring R = sum-count-Ring (ring-Commutative-Ring R)

sum-finite-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Commutative-Ring R) → type-Commutative-Ring R
sum-finite-Commutative-Ring R =
  sum-finite-Commutative-Semiring (commutative-semiring-Commutative-Ring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  sum-one-element-Commutative-Ring :
    (f : functional-vec-Commutative-Ring A 1) →
    sum-Commutative-Ring A 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Ring =
    sum-one-element-Ring (ring-Commutative-Ring A)

  sum-unit-Commutative-Ring :
    (f : unit → type-Commutative-Ring A) →
    sum-finite-Commutative-Ring A unit-Finite-Type f ＝ f star
  sum-unit-Commutative-Ring = sum-unit-Ring (ring-Commutative-Ring A)

  sum-two-elements-Commutative-Ring :
    (f : functional-vec-Commutative-Ring A 2) →
    sum-Commutative-Ring A 2 f ＝
    add-Commutative-Ring A (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Ring =
    sum-two-elements-Ring (ring-Commutative-Ring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  htpy-sum-Commutative-Ring :
    (n : ℕ) {f g : functional-vec-Commutative-Ring R n} →
    (f ~ g) → sum-Commutative-Ring R n f ＝ sum-Commutative-Ring R n g
  htpy-sum-Commutative-Ring = htpy-sum-Ring (ring-Commutative-Ring R)

  htpy-sum-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Commutative-Ring R} → (f ~ g) →
    sum-finite-Commutative-Ring R A f ＝ sum-finite-Commutative-Ring R A g
  htpy-sum-finite-Commutative-Ring =
    htpy-sum-finite-Ring (ring-Commutative-Ring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  cons-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring A (succ-ℕ n)) →
    {x : type-Commutative-Ring A} → head-functional-vec n f ＝ x →
    sum-Commutative-Ring A (succ-ℕ n) f ＝
    add-Commutative-Ring A
      ( sum-Commutative-Ring A n (tail-functional-vec n f)) x
  cons-sum-Commutative-Ring = cons-sum-Ring (ring-Commutative-Ring A)

  snoc-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring A (succ-ℕ n)) →
    {x : type-Commutative-Ring A} → f (zero-Fin n) ＝ x →
    sum-Commutative-Ring A (succ-ℕ n) f ＝
    add-Commutative-Ring A
      ( x)
      ( sum-Commutative-Ring A n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Ring = snoc-sum-Ring (ring-Commutative-Ring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (x : type-Commutative-Ring R)
    (f : functional-vec-Commutative-Ring R n) →
    mul-Commutative-Ring R x (sum-Commutative-Ring R n f) ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R x (f i))
  left-distributive-mul-sum-Commutative-Ring =
    left-distributive-mul-sum-Ring (ring-Commutative-Ring R)

  right-distributive-mul-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring R n)
    (x : type-Commutative-Ring R) →
    mul-Commutative-Ring R (sum-Commutative-Ring R n f) x ＝
    sum-Commutative-Ring R n (λ i → mul-Commutative-Ring R (f i) x)
  right-distributive-mul-sum-Commutative-Ring =
    right-distributive-mul-sum-Ring (ring-Commutative-Ring R)

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

### Interchange law of sums and addition in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  interchange-add-sum-Commutative-Ring :
    (n : ℕ) (f g : functional-vec-Commutative-Ring A n) →
    add-Commutative-Ring A
      ( sum-Commutative-Ring A n f)
      ( sum-Commutative-Ring A n g) ＝
    sum-Commutative-Ring A n
      ( add-functional-vec-Commutative-Ring A n f g)
  interchange-add-sum-Commutative-Ring =
    interchange-add-sum-Ring (ring-Commutative-Ring A)
```

### Extending a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  extend-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring A n) →
    sum-Commutative-Ring A
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Ring A n (zero-Commutative-Ring A) f) ＝
    sum-Commutative-Ring A n f
  extend-sum-Commutative-Ring = extend-sum-Ring (ring-Commutative-Ring A)
```

### Shifting a sum of elements in a commutative ring

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  shift-sum-Commutative-Ring :
    (n : ℕ) (f : functional-vec-Commutative-Ring A n) →
    sum-Commutative-Ring A
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Ring A n f
        ( zero-Commutative-Ring A)) ＝
    sum-Commutative-Ring A n f
  shift-sum-Commutative-Ring = shift-sum-Ring (ring-Commutative-Ring A)
```

### Splitting sums

```agda
split-sum-Commutative-Ring :
  {l : Level} (A : Commutative-Ring l)
  (n m : ℕ) (f : functional-vec-Commutative-Ring A (n +ℕ m)) →
  sum-Commutative-Ring A (n +ℕ m) f ＝
  add-Commutative-Ring A
    ( sum-Commutative-Ring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Ring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Ring A n zero-ℕ f =
  inv (right-unit-law-add-Commutative-Ring A (sum-Commutative-Ring A n f))
split-sum-Commutative-Ring A n (succ-ℕ m) f =
  ( ap
    ( add-Commutative-Ring' A (f (inr star)))
    ( split-sum-Commutative-Ring A n m (f ∘ inl))) ∙
  ( associative-add-Commutative-Ring A _ _ _)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  sum-zero-Commutative-Ring :
    (n : ℕ) →
    sum-Commutative-Ring R n
      ( zero-functional-vec-Commutative-Ring R n) ＝
    zero-Commutative-Ring R
  sum-zero-Commutative-Ring = sum-zero-Ring (ring-Commutative-Ring R)

  sum-zero-finite-Commutative-Ring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Commutative-Ring R A (λ _ → zero-Commutative-Ring R) ＝
    zero-Commutative-Ring R
  sum-zero-finite-Commutative-Ring =
    sum-zero-finite-Ring (ring-Commutative-Ring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (A : Commutative-Ring l)
  where

  preserves-sum-permutation-Commutative-Ring :
    (n : ℕ) → (σ : Permutation n) →
    (f : functional-vec-Commutative-Ring A n) →
    sum-Commutative-Ring A n f ＝ sum-Commutative-Ring A n (f ∘ map-equiv σ)
  preserves-sum-permutation-Commutative-Ring =
    preserves-sum-permutation-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring A)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Ring l1)
  (A : Finite-Type l2) (B : Finite-Type l3) (H : equiv-Finite-Type A B)
  where

  sum-equiv-finite-Commutative-Ring :
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    sum-finite-Commutative-Ring R A f ＝
    sum-finite-Commutative-Ring R B (f ∘ map-inv-equiv H)
  sum-equiv-finite-Commutative-Ring =
    sum-equiv-finite-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
      ( A)
      ( B)
      ( H)

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

  sum-coproduct-finite-Commutative-Ring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Commutative-Ring R) →
    sum-finite-Commutative-Ring R (coproduct-Finite-Type A B) f ＝
    add-Commutative-Ring
      ( R)
      ( sum-finite-Commutative-Ring R A (f ∘ inl))
      ( sum-finite-Commutative-Ring R B (f ∘ inr))
  sum-coproduct-finite-Commutative-Ring =
    sum-coproduct-finite-Ring (ring-Commutative-Ring R) A B
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

  sum-is-empty-finite-Commutative-Ring :
    (f : type-Finite-Type A → type-Commutative-Ring R) →
    is-zero-Commutative-Ring R (sum-finite-Commutative-Ring R A f)
  sum-is-empty-finite-Commutative-Ring =
    sum-is-empty-finite-Ring (ring-Commutative-Ring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
sum-finite-count-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Commutative-Ring R) →
  sum-finite-Commutative-Ring R A f ＝
  sum-count-Commutative-Ring R (type-Finite-Type A) cA f
sum-finite-count-Commutative-Ring R =
  sum-finite-count-Ring (ring-Commutative-Ring R)
```
