# Sums in commutative semirings

```agda
module commutative-algebra.sums-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

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
-- open import foundation.negated-equality
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-semirings

open import lists.lists

open import ring-theory.sums-semirings

open import univalent-combinatorics.cartesian-product-types
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="in a commutative semiring" WD="sum" WDID=Q218005 Agda=sum-Commutative-Semiring}}
extends the binary addition operation on a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` to any
family of elements of `R` indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md), or by
a [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n : ℕ) →
  (functional-vec-Commutative-Semiring A n) → type-Commutative-Semiring A
sum-Commutative-Semiring A = sum-Semiring (semiring-Commutative-Semiring A)

sum-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2) → count A →
  (A → type-Commutative-Semiring R) → type-Commutative-Semiring R
sum-count-Commutative-Semiring R =
  sum-count-Semiring (semiring-Commutative-Semiring R)

sum-finite-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Commutative-Semiring R) →
  type-Commutative-Semiring R
sum-finite-Commutative-Semiring R =
  sum-finite-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 1) →
    sum-Commutative-Semiring A 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Semiring =
    sum-one-element-Semiring (semiring-Commutative-Semiring A)

  sum-unit-finite-Commutative-Semiring :
    (f : unit → type-Commutative-Semiring A) →
    sum-finite-Commutative-Semiring A unit-Finite-Type f ＝ f star
  sum-unit-finite-Commutative-Semiring =
    sum-unit-finite-Semiring (semiring-Commutative-Semiring A)

  sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 2) →
    sum-Commutative-Semiring A 2 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Semiring =
    sum-two-elements-Semiring (semiring-Commutative-Semiring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-vec-Commutative-Semiring R n} →
    (f ~ g) → sum-Commutative-Semiring R n f ＝ sum-Commutative-Semiring R n g
  htpy-sum-Commutative-Semiring =
    htpy-sum-Semiring (semiring-Commutative-Semiring R)

  htpy-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Commutative-Semiring R} → (f ~ g) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R A g
  htpy-sum-finite-Commutative-Semiring =
    htpy-sum-finite-Semiring (semiring-Commutative-Semiring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  cons-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → head-functional-vec n f ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n (tail-functional-vec n f)) x
  cons-sum-Commutative-Semiring =
    cons-sum-Semiring (semiring-Commutative-Semiring A)

  snoc-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → f (zero-Fin n) ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( x)
      ( sum-Commutative-Semiring A n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Semiring =
    snoc-sum-Semiring (semiring-Commutative-Semiring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring R)
    (f : functional-vec-Commutative-Semiring R n) →
    mul-Commutative-Semiring R x (sum-Commutative-Semiring R n f) ＝
    sum-Commutative-Semiring R n (λ i → mul-Commutative-Semiring R x (f i))
  left-distributive-mul-sum-Commutative-Semiring =
    left-distributive-mul-sum-Semiring (semiring-Commutative-Semiring R)

  right-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring R n)
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (sum-Commutative-Semiring R n f) x ＝
    sum-Commutative-Semiring R n (λ i → mul-Commutative-Semiring R (f i) x)
  right-distributive-mul-sum-Commutative-Semiring =
    right-distributive-mul-sum-Semiring (semiring-Commutative-Semiring R)

  left-distributive-mul-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) (x : type-Commutative-Semiring R) →
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    mul-Commutative-Semiring R x (sum-finite-Commutative-Semiring R A f) ＝
    sum-finite-Commutative-Semiring R A (mul-Commutative-Semiring R x ∘ f)
  left-distributive-mul-sum-finite-Commutative-Semiring =
    left-distributive-mul-sum-finite-Semiring (semiring-Commutative-Semiring R)

  right-distributive-mul-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (sum-finite-Commutative-Semiring R A f) x ＝
    sum-finite-Commutative-Semiring R A (mul-Commutative-Semiring' R x ∘ f)
  right-distributive-mul-sum-finite-Commutative-Semiring =
    right-distributive-mul-sum-finite-Semiring (semiring-Commutative-Semiring R)
```

### Interchange law of sums and addition in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  interchange-add-sum-Commutative-Semiring :
    (n : ℕ) (f g : functional-vec-Commutative-Semiring A n) →
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n f)
      ( sum-Commutative-Semiring A n g) ＝
    sum-Commutative-Semiring A n
      ( add-functional-vec-Commutative-Semiring A n f g)
  interchange-add-sum-Commutative-Semiring =
    interchange-add-sum-Semiring (semiring-Commutative-Semiring A)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  extend-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Semiring A n
        ( zero-Commutative-Semiring A) f) ＝
    sum-Commutative-Semiring A n f
  extend-sum-Commutative-Semiring =
    extend-sum-Semiring (semiring-Commutative-Semiring A)
```

### Shifting a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  shift-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Semiring A n f
        ( zero-Commutative-Semiring A)) ＝
    sum-Commutative-Semiring A n f
  shift-sum-Commutative-Semiring =
    shift-sum-Semiring (semiring-Commutative-Semiring A)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  sum-zero-Commutative-Semiring :
    (n : ℕ) →
    sum-Commutative-Semiring R n
      ( zero-functional-vec-Commutative-Semiring R n) ＝
    zero-Commutative-Semiring R
  sum-zero-Commutative-Semiring =
    sum-zero-Semiring (semiring-Commutative-Semiring R)

  sum-zero-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Commutative-Semiring R A (λ _ → zero-Commutative-Semiring R) ＝
    zero-Commutative-Semiring R
  sum-zero-finite-Commutative-Semiring =
    sum-zero-finite-Semiring (semiring-Commutative-Semiring R)
```

### Splitting sums

```agda
split-sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n m : ℕ) (f : functional-vec-Commutative-Semiring A (n +ℕ m)) →
  sum-Commutative-Semiring A (n +ℕ m) f ＝
  add-Commutative-Semiring A
    ( sum-Commutative-Semiring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Semiring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Semiring A =
  split-sum-Semiring (semiring-Commutative-Semiring A)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  preserves-sum-permutation-Commutative-Semiring :
    (n : ℕ) → (σ : Permutation n) →
    (f : functional-vec-Commutative-Semiring R n) →
    sum-Commutative-Semiring R n f ＝
    sum-Commutative-Semiring R n (f ∘ map-equiv σ)
  preserves-sum-permutation-Commutative-Semiring =
    preserves-sum-permutation-Semiring (semiring-Commutative-Semiring R)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : Finite-Type l3) (H : equiv-Finite-Type A B)
  where

  sum-equiv-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R B (f ∘ map-inv-equiv H)
  sum-equiv-finite-Commutative-Semiring =
    sum-equiv-finite-Semiring (semiring-Commutative-Semiring R) A B H

module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (σ : Aut (type-Finite-Type A))
  where

  sum-aut-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R A (f ∘ map-equiv σ)
  sum-aut-finite-Commutative-Semiring =
    sum-equiv-finite-Commutative-Semiring R A A (inv-equiv σ)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  sum-coproduct-finite-Commutative-Semiring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R (coproduct-Finite-Type A B) f ＝
    add-Commutative-Semiring
      ( R)
      ( sum-finite-Commutative-Semiring R A (f ∘ inl))
      ( sum-finite-Commutative-Semiring R B (f ∘ inr))
  sum-coproduct-finite-Commutative-Semiring =
    sum-coproduct-finite-Semiring (semiring-Commutative-Semiring R) A B
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  sum-Σ-finite-Commutative-Semiring :
    (f :
      (a : type-Finite-Type A) →
      type-Finite-Type (B a) →
      type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R (Σ-Finite-Type A B) (ind-Σ f) ＝
    sum-finite-Commutative-Semiring
      R A (λ a → sum-finite-Commutative-Semiring R (B a) (f a))
  sum-Σ-finite-Commutative-Semiring =
    sum-Σ-finite-Semiring (semiring-Commutative-Semiring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  sum-is-empty-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    is-zero-Commutative-Semiring R (sum-finite-Commutative-Semiring R A f)
  sum-is-empty-finite-Commutative-Semiring =
    sum-is-empty-finite-Semiring (semiring-Commutative-Semiring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
sum-finite-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Commutative-Semiring R) →
  sum-finite-Commutative-Semiring R A f ＝
  sum-count-Commutative-Semiring R (type-Finite-Type A) cA f
sum-finite-count-Commutative-Semiring R =
  sum-finite-count-Semiring (semiring-Commutative-Semiring R)
```

### Commuting sums

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  where

  commute-sum-two-finite-Commutative-Semiring :
    (f g : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A
      (λ a → add-Commutative-Semiring R (f a) (g a)) ＝
    add-Commutative-Semiring R
      (sum-finite-Commutative-Semiring R A f)
      (sum-finite-Commutative-Semiring R A g)
  commute-sum-two-finite-Commutative-Semiring f g = equational-reasoning
    sum-finite-Commutative-Semiring R A
      ( λ a → add-Commutative-Semiring R (f a) (g a))
    ＝
      sum-finite-Commutative-Semiring
        ( R)
        ( A)
        ( λ a → sum-Commutative-Semiring R 2 (h a))
        by
          htpy-sum-finite-Commutative-Semiring
            ( R)
            ( A)
            ( λ a → inv (sum-two-elements-Commutative-Semiring R (h a)))
    ＝
      sum-finite-Commutative-Semiring
        ( R)
        ( A)
        ( λ a →
          sum-finite-Commutative-Semiring R (Fin-Finite-Type 2) (h a))
      by
        htpy-sum-finite-Commutative-Semiring R A
          ( λ a →
            inv
              ( sum-finite-count-Commutative-Semiring
                ( R)
                ( Fin-Finite-Type 2)
                ( count-Fin 2)
                ( h a)))
    ＝
      sum-finite-Commutative-Semiring
        ( R)
        ( Σ-Finite-Type A (λ _ → Fin-Finite-Type 2))
        ( ind-Σ h)
      by inv (sum-Σ-finite-Commutative-Semiring R A (λ _ → Fin-Finite-Type 2) h)
    ＝
      sum-finite-Commutative-Semiring
        ( R)
        ( Σ-Finite-Type (Fin-Finite-Type 2) (λ _ → A))
        ( λ (i , a) → h a i)
      by
        sum-equiv-finite-Commutative-Semiring R _ _
          ( commutative-product)
          ( ind-Σ h)
    ＝
      sum-finite-Commutative-Semiring
        ( R)
        ( Fin-Finite-Type 2)
        ( λ i → sum-finite-Commutative-Semiring R A (λ a → h a i))
      by sum-Σ-finite-Commutative-Semiring R _ _ _
    ＝
      sum-Commutative-Semiring
        ( R)
        ( 2)
        ( λ i → sum-finite-Commutative-Semiring R A (λ a → h a i))
      by
        sum-finite-count-Commutative-Semiring
          ( R)
          ( Fin-Finite-Type 2)
          ( count-Fin 2)
          ( _)
    ＝
      add-Commutative-Semiring
        ( R)
        ( sum-finite-Commutative-Semiring R A f)
        ( sum-finite-Commutative-Semiring R A g)
      by
        sum-two-elements-Commutative-Semiring
          ( R)
          ( λ i → sum-finite-Commutative-Semiring R A (λ a → h a i))
    where
      h : type-Finite-Type A → Fin 2 → type-Commutative-Semiring R
      h a (inl (inr _)) = f a
      h a (inr _) = g a
```
