# Products of tuples of elements in monoids

```agda
module group-theory.products-of-tuples-of-elements-monoids where
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

open import linear-algebra.vectors-on-monoids

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The product operation extends the binary multiplication operation on a
[monoid](group-theory.monoids.md) `M` to any family of elements of `M` indexed
by a [standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definition

```agda
mul-fin-Monoid :
  {l : Level} (M : Monoid l) (n : ℕ) →
  (functional-vec-Monoid M n) → type-Monoid M
mul-fin-Monoid M zero-ℕ f = unit-Monoid M
mul-fin-Monoid M (succ-ℕ n) f =
  mul-Monoid M
    ( mul-fin-Monoid M n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Products of one and two elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-one-element-Monoid :
    (f : functional-vec-Monoid M 1) →
    mul-fin-Monoid M 1 f ＝ head-functional-vec-Monoid M 0 f
  mul-one-element-Monoid f =
    left-unit-law-mul-Monoid M (f (inr star))

  mul-two-elements-Monoid :
    (f : functional-vec-Monoid M 2) →
    mul-fin-Monoid M 2 f ＝ mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  mul-two-elements-Monoid f =
    ( associative-mul-Monoid M
      (unit-Monoid M) (f (zero-Fin 1)) (f (one-Fin 1))) ∙
    ( left-unit-law-mul-Monoid M
      ( mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))))
```

### Products are homotopy invariant

```agda
module _
  {l : Level} (M : Monoid l)
  where

  htpy-mul-fin-Monoid :
    (n : ℕ) {f g : functional-vec-Monoid M n} →
    (f ~ g) → mul-fin-Monoid M n f ＝ mul-fin-Monoid M n g
  htpy-mul-fin-Monoid zero-ℕ H = refl
  htpy-mul-fin-Monoid (succ-ℕ n) H =
    ap-mul-Monoid M
      ( htpy-mul-fin-Monoid n (H ·r inl-Fin n))
      ( H (inr star))
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Monoid l)
  where

  cons-mul-fin-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → head-functional-vec-Monoid M n f ＝ x →
    mul-fin-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M (mul-fin-Monoid M n (f ∘ inl-Fin n)) x
  cons-mul-fin-Monoid n f refl = refl

  snoc-mul-fin-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → f (zero-Fin n) ＝ x →
    mul-fin-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M
      ( x)
      ( mul-fin-Monoid M n (f ∘ inr-Fin n))
  snoc-mul-fin-Monoid zero-ℕ f refl =
    ( mul-one-element-Monoid M f) ∙
    ( inv (right-unit-law-mul-Monoid M (f (zero-Fin 0))))
  snoc-mul-fin-Monoid (succ-ℕ n) f refl =
    ( ap
      ( mul-Monoid' M (head-functional-vec-Monoid M (succ-ℕ n) f))
      ( snoc-mul-fin-Monoid n (f ∘ inl-Fin (succ-ℕ n)) refl)) ∙
    ( associative-mul-Monoid M
      ( f (zero-Fin (succ-ℕ n)))
      ( mul-fin-Monoid M n (f ∘ (inr-Fin (succ-ℕ n) ∘ inl-Fin n)))
      ( head-functional-vec-Monoid M (succ-ℕ n) f))
```

### Extending a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  extend-mul-fin-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M n) →
    mul-fin-Monoid M
      ( succ-ℕ n)
      ( cons-functional-vec-Monoid M n (unit-Monoid M) f) ＝
    mul-fin-Monoid M n f
  extend-mul-fin-Monoid n f =
    right-unit-law-mul-Monoid M (mul-fin-Monoid M n f)
```

### Shifting a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  shift-mul-fin-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M n) →
    mul-fin-Monoid M
      ( succ-ℕ n)
      ( snoc-functional-vec-Monoid M n f
        ( unit-Monoid M)) ＝
    mul-fin-Monoid M n f
  shift-mul-fin-Monoid zero-ℕ f =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  shift-mul-fin-Monoid (succ-ℕ n) f =
    ap
      ( mul-Monoid' M
        ( head-functional-vec-Monoid M n f))
      ( shift-mul-fin-Monoid n
        ( tail-functional-vec-Monoid M n f))
```

### A product of units is the unit

```agda
module _
  {l : Level} (M : Monoid l)
  where

  mul-unit-Monoid :
    (n : ℕ) →
    mul-fin-Monoid M n (unit-functional-vec-Monoid M n) ＝ unit-Monoid M
  mul-unit-Monoid zero-ℕ = refl
  mul-unit-Monoid (succ-ℕ n) =
    right-unit-law-mul-Monoid M _ ∙ mul-unit-Monoid n
```

### Splitting products

```agda
split-mul-fin-Monoid :
  {l : Level} (M : Monoid l)
  (n m : ℕ) (f : functional-vec-Monoid M (n +ℕ m)) →
  mul-fin-Monoid M (n +ℕ m) f ＝
  mul-Monoid M
    ( mul-fin-Monoid M n (f ∘ inl-coproduct-Fin n m))
    ( mul-fin-Monoid M m (f ∘ inr-coproduct-Fin n m))
split-mul-fin-Monoid M n zero-ℕ f =
  inv (right-unit-law-mul-Monoid M (mul-fin-Monoid M n f))
split-mul-fin-Monoid M n (succ-ℕ m) f =
  ( ap
    ( mul-Monoid' M (f (inr star)))
    ( split-mul-fin-Monoid M n m (f ∘ inl))) ∙
  ( associative-mul-Monoid M _ _ _)
```
