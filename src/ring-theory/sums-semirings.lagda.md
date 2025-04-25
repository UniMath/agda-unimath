# Sums of elements in semirings

```agda
module ring-theory.sums-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import linear-algebra.finite-sequences
open import linear-algebra.finite-sequences-on-semirings

open import ring-theory.semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sum operation extends the binary addition operation on a semiring `R` to any
[finite sequence](linear-algebra.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) →
  (fin-sequence-Semiring R n) → type-Semiring R
sum-Semiring R zero-ℕ f = zero-Semiring R
sum-Semiring R (succ-ℕ n) f =
  add-Semiring R
    ( sum-Semiring R n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-one-element-Semiring :
    (f : fin-sequence-Semiring R 1) →
    sum-Semiring R 1 f ＝ head-fin-sequence 0 f
  sum-one-element-Semiring f =
    left-unit-law-add-Semiring R (f (inr star))

  sum-two-elements-Semiring :
    (f : fin-sequence-Semiring R 2) →
    sum-Semiring R 2 f ＝ add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Semiring f =
    ( associative-add-Semiring R
      (zero-Semiring R) (f (zero-Fin 1)) (f (one-Fin 1))) ∙
    ( left-unit-law-add-Semiring R
      ( add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))))
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-sum-Semiring :
    (n : ℕ) {f g : fin-sequence-Semiring R n} →
    (f ~ g) → sum-Semiring R n f ＝ sum-Semiring R n g
  htpy-sum-Semiring zero-ℕ H = refl
  htpy-sum-Semiring (succ-ℕ n) H =
    ap-add-Semiring R
      ( htpy-sum-Semiring n (H ·r inl-Fin n))
      ( H (inr star))
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Semiring l)
  where

  cons-sum-Semiring :
    (n : ℕ) (f : fin-sequence-Semiring R (succ-ℕ n)) →
    {x : type-Semiring R} → head-fin-sequence n f ＝ x →
    sum-Semiring R (succ-ℕ n) f ＝
    add-Semiring R (sum-Semiring R n (f ∘ inl-Fin n)) x
  cons-sum-Semiring n f refl = refl

  snoc-sum-Semiring :
    (n : ℕ) (f : fin-sequence-Semiring R (succ-ℕ n)) →
    {x : type-Semiring R} → f (zero-Fin n) ＝ x →
    sum-Semiring R (succ-ℕ n) f ＝
    add-Semiring R
      ( x)
      ( sum-Semiring R n (f ∘ inr-Fin n))
  snoc-sum-Semiring zero-ℕ f refl =
    ( sum-one-element-Semiring R f) ∙
    ( inv (right-unit-law-add-Semiring R (f (zero-Fin 0))))
  snoc-sum-Semiring (succ-ℕ n) f refl =
    ( ap
      ( add-Semiring' R (head-fin-sequence (succ-ℕ n) f))
      ( snoc-sum-Semiring n (f ∘ inl-Fin (succ-ℕ n)) refl)) ∙
    ( associative-add-Semiring R
      ( f (zero-Fin (succ-ℕ n)))
      ( sum-Semiring R n (f ∘ (inr-Fin (succ-ℕ n) ∘ inl-Fin n)))
      ( head-fin-sequence (succ-ℕ n) f))
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  left-distributive-mul-sum-Semiring :
    (n : ℕ) (x : type-Semiring R)
    (f : fin-sequence-Semiring R n) →
    mul-Semiring R x (sum-Semiring R n f) ＝
    sum-Semiring R n (λ i → mul-Semiring R x (f i))
  left-distributive-mul-sum-Semiring zero-ℕ x f =
    right-zero-law-mul-Semiring R x
  left-distributive-mul-sum-Semiring (succ-ℕ n) x f =
    ( left-distributive-mul-add-Semiring R x
      ( sum-Semiring R n (f ∘ inl-Fin n))
      ( f (inr star))) ∙
    ( ap
      ( add-Semiring' R (mul-Semiring R x (f (inr star))))
      ( left-distributive-mul-sum-Semiring n x (f ∘ inl-Fin n)))

  right-distributive-mul-sum-Semiring :
    (n : ℕ) (f : fin-sequence-Semiring R n)
    (x : type-Semiring R) →
    mul-Semiring R (sum-Semiring R n f) x ＝
    sum-Semiring R n (λ i → mul-Semiring R (f i) x)
  right-distributive-mul-sum-Semiring zero-ℕ f x =
    left-zero-law-mul-Semiring R x
  right-distributive-mul-sum-Semiring (succ-ℕ n) f x =
    ( right-distributive-mul-add-Semiring R
      ( sum-Semiring R n (f ∘ inl-Fin n))
      ( f (inr star))
      ( x)) ∙
    ( ap
      ( add-Semiring' R (mul-Semiring R (f (inr star)) x))
      ( right-distributive-mul-sum-Semiring n (f ∘ inl-Fin n) x))
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  interchange-add-sum-Semiring :
    (n : ℕ) (f g : fin-sequence-Semiring R n) →
    add-Semiring R
      ( sum-Semiring R n f)
      ( sum-Semiring R n g) ＝
    sum-Semiring R n
      ( add-fin-sequence-Semiring R n f g)
  interchange-add-sum-Semiring zero-ℕ f g =
    left-unit-law-add-Semiring R (zero-Semiring R)
  interchange-add-sum-Semiring (succ-ℕ n) f g =
    ( interchange-add-add-Semiring R
      ( sum-Semiring R n (f ∘ inl-Fin n))
      ( f (inr star))
      ( sum-Semiring R n (g ∘ inl-Fin n))
      ( g (inr star))) ∙
    ( ap
      ( add-Semiring' R
        ( add-Semiring R (f (inr star)) (g (inr star))))
      ( interchange-add-sum-Semiring n
        ( f ∘ inl-Fin n)
        ( g ∘ inl-Fin n)))
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  extend-sum-Semiring :
    (n : ℕ) (f : fin-sequence-Semiring R n) →
    sum-Semiring R
      ( succ-ℕ n)
      ( cons-fin-sequence-Semiring R n (zero-Semiring R) f) ＝
    sum-Semiring R n f
  extend-sum-Semiring n f =
    right-unit-law-add-Semiring R (sum-Semiring R n f)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  shift-sum-Semiring :
    (n : ℕ) (f : fin-sequence-Semiring R n) →
    sum-Semiring R
      ( succ-ℕ n)
      ( snoc-fin-sequence-Semiring R n f
        ( zero-Semiring R)) ＝
    sum-Semiring R n f
  shift-sum-Semiring zero-ℕ f =
    left-unit-law-add-Semiring R (zero-Semiring R)
  shift-sum-Semiring (succ-ℕ n) f =
    ap
      ( add-Semiring' R
        ( head-fin-sequence-Semiring R n f))
      ( shift-sum-Semiring n
        ( tail-fin-sequence-Semiring R n f))
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-zero-Semiring :
    (n : ℕ) →
    sum-Semiring R n (zero-fin-sequence-Semiring R n) ＝ zero-Semiring R
  sum-zero-Semiring zero-ℕ = refl
  sum-zero-Semiring (succ-ℕ n) =
    right-unit-law-add-Semiring R _ ∙ sum-zero-Semiring n
```

### Splitting sums

```agda
split-sum-Semiring :
  {l : Level} (R : Semiring l)
  (n m : ℕ) (f : fin-sequence-Semiring R (n +ℕ m)) →
  sum-Semiring R (n +ℕ m) f ＝
  add-Semiring R
    ( sum-Semiring R n (f ∘ inl-coproduct-Fin n m))
    ( sum-Semiring R m (f ∘ inr-coproduct-Fin n m))
split-sum-Semiring R n zero-ℕ f =
  inv (right-unit-law-add-Semiring R (sum-Semiring R n f))
split-sum-Semiring R n (succ-ℕ m) f =
  ( ap
    ( add-Semiring' R (f (inr star)))
    ( split-sum-Semiring R n m (f ∘ inl))) ∙
  ( associative-add-Semiring R _ _ _)
```
