# Products of elements in monoids

```agda
module group-theory.products-monoids where
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

The product operation extends the binary multiplication operation on a monoid
`M` to any family of elements of `M` indexed by a standard finite type.

## Definition

```agda
product-Monoid :
  {l : Level} (M : Monoid l) (n : ℕ) →
  (functional-vec-Monoid M n) → type-Monoid M
product-Monoid M zero-ℕ f = unit-Monoid M
product-Monoid M (succ-ℕ n) f =
  mul-Monoid M
    ( product-Monoid M n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Products of one and two elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  product-one-element-Monoid :
    (f : functional-vec-Monoid M 1) →
    product-Monoid M 1 f ＝ head-functional-vec-Monoid M 0 f
  product-one-element-Monoid f =
    left-unit-law-mul-Monoid M (f (inr star))

  product-two-elements-Monoid :
    (f : functional-vec-Monoid M 2) →
    product-Monoid M 2 f ＝ mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  product-two-elements-Monoid f =
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

  htpy-product-Monoid :
    (n : ℕ) {f g : functional-vec-Monoid M n} →
    (f ~ g) → product-Monoid M n f ＝ product-Monoid M n g
  htpy-product-Monoid zero-ℕ H = refl
  htpy-product-Monoid (succ-ℕ n) H =
    ap-mul-Monoid M
      ( htpy-product-Monoid n (H ·r inl-Fin n))
      ( H (inr star))
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Monoid l)
  where

  cons-product-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → head-functional-vec-Monoid M n f ＝ x →
    product-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M (product-Monoid M n (f ∘ inl-Fin n)) x
  cons-product-Monoid n f refl = refl

  snoc-product-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M (succ-ℕ n)) →
    {x : type-Monoid M} → f (zero-Fin n) ＝ x →
    product-Monoid M (succ-ℕ n) f ＝
    mul-Monoid M
      ( x)
      ( product-Monoid M n (f ∘ inr-Fin n))
  snoc-product-Monoid zero-ℕ f refl =
    ( product-one-element-Monoid M f) ∙
    ( inv (right-unit-law-mul-Monoid M (f (zero-Fin 0))))
  snoc-product-Monoid (succ-ℕ n) f refl =
    ( ap
      ( mul-Monoid' M (head-functional-vec-Monoid M (succ-ℕ n) f))
      ( snoc-product-Monoid n (f ∘ inl-Fin (succ-ℕ n)) refl)) ∙
    ( associative-mul-Monoid M
      ( f (zero-Fin (succ-ℕ n)))
      ( product-Monoid M n (f ∘ (inr-Fin (succ-ℕ n) ∘ inl-Fin n)))
      ( head-functional-vec-Monoid M (succ-ℕ n) f))
```

### Extending a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  extend-product-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M n) →
    product-Monoid M
      ( succ-ℕ n)
      ( cons-functional-vec-Monoid M n (unit-Monoid M) f) ＝
    product-Monoid M n f
  extend-product-Monoid n f =
    right-unit-law-mul-Monoid M (product-Monoid M n f)
```

### Shifting a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  shift-product-Monoid :
    (n : ℕ) (f : functional-vec-Monoid M n) →
    product-Monoid M
      ( succ-ℕ n)
      ( snoc-functional-vec-Monoid M n f
        ( unit-Monoid M)) ＝
    product-Monoid M n f
  shift-product-Monoid zero-ℕ f =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  shift-product-Monoid (succ-ℕ n) f =
    ap
      ( mul-Monoid' M
        ( head-functional-vec-Monoid M n f))
      ( shift-product-Monoid n
        ( tail-functional-vec-Monoid M n f))
```

### A product of units is the unit

```agda
module _
  {l : Level} (M : Monoid l)
  where

  product-unit-Monoid :
    (n : ℕ) →
    product-Monoid M n (unit-functional-vec-Monoid M n) ＝ unit-Monoid M
  product-unit-Monoid zero-ℕ = refl
  product-unit-Monoid (succ-ℕ n) =
    right-unit-law-mul-Monoid M _ ∙ product-unit-Monoid n
```

### Splitting products

```agda
split-product-Monoid :
  {l : Level} (M : Monoid l)
  (n m : ℕ) (f : functional-vec-Monoid M (n +ℕ m)) →
  product-Monoid M (n +ℕ m) f ＝
  mul-Monoid M
    ( product-Monoid M n (f ∘ inl-coproduct-Fin n m))
    ( product-Monoid M m (f ∘ inr-coproduct-Fin n m))
split-product-Monoid M n zero-ℕ f =
  inv (right-unit-law-mul-Monoid M (product-Monoid M n f))
split-product-Monoid M n (succ-ℕ m) f =
  ( ap
    ( mul-Monoid' M (f (inr star)))
    ( split-product-Monoid M n m (f ∘ inl))) ∙
  ( associative-mul-Monoid M _ _ _)
```
