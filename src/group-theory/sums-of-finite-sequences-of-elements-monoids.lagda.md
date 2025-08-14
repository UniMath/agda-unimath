# Sums of finite sequences of elements in monoids

```agda
module group-theory.sums-of-finite-sequences-of-elements-monoids where
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

open import group-theory.monoids
open import group-theory.powers-of-elements-monoids

open import linear-algebra.finite-sequences-in-monoids

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a monoid" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Monoid}}
operation extends the binary operation on a [monoid](group-theory.monoids.md)
`M` to any [finite sequence](lists.finite-sequences.md) of elements of `M`.

## Definition

```agda
sum-fin-sequence-type-Monoid :
  {l : Level} (M : Monoid l) (n : ℕ) →
  (fin-sequence-type-Monoid M n) → type-Monoid M
sum-fin-sequence-type-Monoid M zero-ℕ f = unit-Monoid M
sum-fin-sequence-type-Monoid M (succ-ℕ n) f =
  mul-Monoid M
    ( sum-fin-sequence-type-Monoid M n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  compute-sum-one-element-Monoid :
    (f : fin-sequence-type-Monoid M 1) →
    sum-fin-sequence-type-Monoid M 1 f ＝ head-fin-sequence-type-Monoid M 0 f
  compute-sum-one-element-Monoid f =
    left-unit-law-mul-Monoid M (f (inr star))

  compute-sum-two-elements-Monoid :
    (f : fin-sequence-type-Monoid M 2) →
    sum-fin-sequence-type-Monoid M 2 f ＝
    mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  compute-sum-two-elements-Monoid f =
    ( associative-mul-Monoid M
      (unit-Monoid M) (f (zero-Fin 1)) (f (one-Fin 1))) ∙
    ( left-unit-law-mul-Monoid M
      ( mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))))
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (M : Monoid l)
  where

  htpy-sum-fin-sequence-type-Monoid :
    (n : ℕ) {f g : fin-sequence-type-Monoid M n} →
    (f ~ g) →
    sum-fin-sequence-type-Monoid M n f ＝ sum-fin-sequence-type-Monoid M n g
  htpy-sum-fin-sequence-type-Monoid zero-ℕ H = refl
  htpy-sum-fin-sequence-type-Monoid (succ-ℕ n) H =
    ap-mul-Monoid M
      ( htpy-sum-fin-sequence-type-Monoid n (H ·r inl-Fin n))
      ( H (inr star))
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Monoid l)
  where

  cons-sum-fin-sequence-type-Monoid :
    (n : ℕ) (f : fin-sequence-type-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → head-fin-sequence-type-Monoid M n f ＝ x →
    sum-fin-sequence-type-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M (sum-fin-sequence-type-Monoid M n (f ∘ inl-Fin n)) x
  cons-sum-fin-sequence-type-Monoid n f refl = refl

  snoc-sum-fin-sequence-type-Monoid :
    (n : ℕ) (f : fin-sequence-type-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → f (zero-Fin n) ＝ x →
    sum-fin-sequence-type-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M
      ( x)
      ( sum-fin-sequence-type-Monoid M n (f ∘ inr-Fin n))
  snoc-sum-fin-sequence-type-Monoid zero-ℕ f refl =
    ( compute-sum-one-element-Monoid M f) ∙
    ( inv (right-unit-law-mul-Monoid M (f (zero-Fin 0))))
  snoc-sum-fin-sequence-type-Monoid (succ-ℕ n) f refl =
    ( ap
      ( mul-Monoid' M (head-fin-sequence-type-Monoid M (succ-ℕ n) f))
      ( snoc-sum-fin-sequence-type-Monoid n (f ∘ inl-Fin (succ-ℕ n)) refl)) ∙
    ( associative-mul-Monoid M
      ( f (zero-Fin (succ-ℕ n)))
      ( sum-fin-sequence-type-Monoid M n (f ∘ (inr-Fin (succ-ℕ n) ∘ inl-Fin n)))
      ( head-fin-sequence-type-Monoid M (succ-ℕ n) f))
```

### Extending a sum of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  extend-sum-fin-sequence-type-Monoid :
    (n : ℕ) (f : fin-sequence-type-Monoid M n) →
    sum-fin-sequence-type-Monoid M
      ( succ-ℕ n)
      ( cons-fin-sequence-type-Monoid M n (unit-Monoid M) f) ＝
    sum-fin-sequence-type-Monoid M n f
  extend-sum-fin-sequence-type-Monoid n f =
    right-unit-law-mul-Monoid M (sum-fin-sequence-type-Monoid M n f)
```

### Shifting a sum of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  shift-sum-fin-sequence-type-Monoid :
    (n : ℕ) (f : fin-sequence-type-Monoid M n) →
    sum-fin-sequence-type-Monoid M
      ( succ-ℕ n)
      ( snoc-fin-sequence-type-Monoid M n f
        ( unit-Monoid M)) ＝
    sum-fin-sequence-type-Monoid M n f
  shift-sum-fin-sequence-type-Monoid zero-ℕ f =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  shift-sum-fin-sequence-type-Monoid (succ-ℕ n) f =
    ap
      ( mul-Monoid' M
        ( head-fin-sequence-type-Monoid M n f))
      ( shift-sum-fin-sequence-type-Monoid n
        ( tail-fin-sequence-type-Monoid M n f))
```

### A sum of zeros is zero

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    sum-zero-fin-sequence-type-Monoid :
      (n : ℕ) →
      sum-fin-sequence-type-Monoid M n (zero-fin-sequence-type-Monoid M n) ＝
      unit-Monoid M
    sum-zero-fin-sequence-type-Monoid zero-ℕ = refl
    sum-zero-fin-sequence-type-Monoid (succ-ℕ n) =
      right-unit-law-mul-Monoid M _ ∙ sum-zero-fin-sequence-type-Monoid n
```

### Splitting sums of `n + m` elements into a sum of `n` elements and a sum of `m` elements

```agda
split-sum-fin-sequence-type-Monoid :
  {l : Level} (M : Monoid l)
  (n m : ℕ) (f : fin-sequence-type-Monoid M (n +ℕ m)) →
  sum-fin-sequence-type-Monoid M (n +ℕ m) f ＝
  mul-Monoid M
    ( sum-fin-sequence-type-Monoid M n (f ∘ inl-coproduct-Fin n m))
    ( sum-fin-sequence-type-Monoid M m (f ∘ inr-coproduct-Fin n m))
split-sum-fin-sequence-type-Monoid M n zero-ℕ f =
  inv (right-unit-law-mul-Monoid M (sum-fin-sequence-type-Monoid M n f))
split-sum-fin-sequence-type-Monoid M n (succ-ℕ m) f =
  ( ap
    ( mul-Monoid' M (f (inr star)))
    ( split-sum-fin-sequence-type-Monoid M n m (f ∘ inl))) ∙
  ( associative-mul-Monoid M _ _ _)
```

### The sum of a sequence of length `n` of a constant `c` is `n` times `c`

```agda
abstract
  sum-const-sequence-type-Monoid :
    {l : Level} (M : Monoid l) (n : ℕ) (c : type-Monoid M) →
    sum-fin-sequence-type-Monoid M n (λ _ → c) ＝ power-Monoid M n c
  sum-const-sequence-type-Monoid M 0 c = refl
  sum-const-sequence-type-Monoid M 1 c =
    compute-sum-one-element-Monoid M (λ _ → c)
  sum-const-sequence-type-Monoid M (succ-ℕ (succ-ℕ n)) c =
    ap-mul-Monoid M (sum-const-sequence-type-Monoid M (succ-ℕ n) c) refl
```
