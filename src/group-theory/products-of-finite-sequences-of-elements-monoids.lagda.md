# Products of finite sequences of elements in monoids

```agda
module group-theory.products-of-finite-sequences-of-elements-monoids where
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
{{#concept "product operation" Disambiguation="of a finite sequence in a monoid" WD="product" WDID=Q218005 Agda=product-fin-sequence-type-Monoid}}
operation extends the binary operation on a [monoid](group-theory.monoids.md)
`M` to any [finite sequence](lists.finite-sequences.md) of elements of `M`.

## Definition

```agda
product-fin-sequence-type-Monoid :
  {l : Level} (M : Monoid l) (n : ℕ) →
  (fin-sequence-type-Monoid M n) → type-Monoid M
product-fin-sequence-type-Monoid M zero-ℕ f = unit-Monoid M
product-fin-sequence-type-Monoid M (succ-ℕ n) f =
  mul-Monoid M
    ( product-fin-sequence-type-Monoid M n (f ∘ inl-Fin n))
    ( f (inr star))
```

## Properties

### Products of one and two elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    compute-product-one-element-Monoid :
      (f : fin-sequence-type-Monoid M 1) →
      product-fin-sequence-type-Monoid M 1 f ＝
      head-fin-sequence-type-Monoid M 0 f
    compute-product-one-element-Monoid f =
      left-unit-law-mul-Monoid M (f (inr star))

    compute-product-two-elements-Monoid :
      (f : fin-sequence-type-Monoid M 2) →
      product-fin-sequence-type-Monoid M 2 f ＝
      mul-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
    compute-product-two-elements-Monoid f =
      ap-mul-Monoid M (left-unit-law-mul-Monoid M (f (zero-Fin 1))) refl
```

### Products are homotopy invariant

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    htpy-product-fin-sequence-type-Monoid :
      (n : ℕ) {f g : fin-sequence-type-Monoid M n} →
      (f ~ g) →
      product-fin-sequence-type-Monoid M n f ＝
      product-fin-sequence-type-Monoid M n g
    htpy-product-fin-sequence-type-Monoid zero-ℕ H = refl
    htpy-product-fin-sequence-type-Monoid (succ-ℕ n) H =
      ap-mul-Monoid M
        ( htpy-product-fin-sequence-type-Monoid n (H ·r inl-Fin n))
        ( H (inr star))
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    cons-product-fin-sequence-type-Monoid :
      (n : ℕ) (f : fin-sequence-type-Monoid M (succ-ℕ n)) →
      product-fin-sequence-type-Monoid M (succ-ℕ n) f ＝
      mul-Monoid M
        ( product-fin-sequence-type-Monoid M n (f ∘ inl-Fin n))
        ( head-fin-sequence-type-Monoid M n f)
    cons-product-fin-sequence-type-Monoid n f = refl

    snoc-product-fin-sequence-type-Monoid :
      (n : ℕ) (f : fin-sequence-type-Monoid M (succ-ℕ n)) →
      product-fin-sequence-type-Monoid M (succ-ℕ n) f ＝
      mul-Monoid M
        ( f (zero-Fin n))
        ( product-fin-sequence-type-Monoid M n (f ∘ inr-Fin n))
    snoc-product-fin-sequence-type-Monoid zero-ℕ f =
      ( compute-product-one-element-Monoid M f) ∙
      ( inv (right-unit-law-mul-Monoid M (f (zero-Fin 0))))
    snoc-product-fin-sequence-type-Monoid (succ-ℕ n) f =
      ( ap
        ( mul-Monoid' M (head-fin-sequence-type-Monoid M (succ-ℕ n) f))
        ( snoc-product-fin-sequence-type-Monoid
          ( n)
          ( f ∘ inl-Fin (succ-ℕ n)))) ∙
      ( associative-mul-Monoid M _ _ _)
```

### Extending a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    extend-product-fin-sequence-type-Monoid :
      (n : ℕ) (f : fin-sequence-type-Monoid M n) →
      product-fin-sequence-type-Monoid M
        ( succ-ℕ n)
        ( cons-fin-sequence-type-Monoid M n (unit-Monoid M) f) ＝
      product-fin-sequence-type-Monoid M n f
    extend-product-fin-sequence-type-Monoid n f =
      right-unit-law-mul-Monoid M (product-fin-sequence-type-Monoid M n f)
```

### Shifting a product of elements in a monoid

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    shift-product-fin-sequence-type-Monoid :
      (n : ℕ) (f : fin-sequence-type-Monoid M n) →
      product-fin-sequence-type-Monoid M
        ( succ-ℕ n)
        ( snoc-fin-sequence-type-Monoid M n f
          ( unit-Monoid M)) ＝
      product-fin-sequence-type-Monoid M n f
    shift-product-fin-sequence-type-Monoid zero-ℕ f =
      left-unit-law-mul-Monoid M (unit-Monoid M)
    shift-product-fin-sequence-type-Monoid (succ-ℕ n) f =
      ap
        ( mul-Monoid' M (head-fin-sequence-type-Monoid M n f))
        ( shift-product-fin-sequence-type-Monoid
          ( n)
          ( tail-fin-sequence-type-Monoid M n f))
```

### A product of units is the unit

```agda
module _
  {l : Level} (M : Monoid l)
  where

  abstract
    product-unit-fin-sequence-type-Monoid :
      (n : ℕ) →
      product-fin-sequence-type-Monoid
        ( M)
        ( n)
        ( zero-fin-sequence-type-Monoid M n) ＝
      unit-Monoid M
    product-unit-fin-sequence-type-Monoid zero-ℕ = refl
    product-unit-fin-sequence-type-Monoid (succ-ℕ n) =
      right-unit-law-mul-Monoid M _ ∙ product-unit-fin-sequence-type-Monoid n
```

### Splitting products of `n + m` elements into a product of `n` elements and a product of `m` elements

```agda
abstract
  split-product-fin-sequence-type-Monoid :
    {l : Level} (M : Monoid l)
    (n m : ℕ) (f : fin-sequence-type-Monoid M (n +ℕ m)) →
    product-fin-sequence-type-Monoid M (n +ℕ m) f ＝
    mul-Monoid M
      ( product-fin-sequence-type-Monoid M n (f ∘ inl-coproduct-Fin n m))
      ( product-fin-sequence-type-Monoid M m (f ∘ inr-coproduct-Fin n m))
  split-product-fin-sequence-type-Monoid M n zero-ℕ f =
    inv (right-unit-law-mul-Monoid M (product-fin-sequence-type-Monoid M n f))
  split-product-fin-sequence-type-Monoid M n (succ-ℕ m) f =
    ( ap
      ( mul-Monoid' M (f (inr star)))
      ( split-product-fin-sequence-type-Monoid M n m (f ∘ inl))) ∙
    ( associative-mul-Monoid M _ _ _)
```

### Constant products are powers

```agda
abstract
  product-constant-fin-sequence-type-Monoid :
    {l : Level} (M : Monoid l) (n : ℕ) (x : type-Monoid M) →
    product-fin-sequence-type-Monoid M n (λ _ → x) ＝ power-Monoid M n x
  product-constant-fin-sequence-type-Monoid M 0 x = refl
  product-constant-fin-sequence-type-Monoid M 1 x =
    compute-product-one-element-Monoid M (λ _ → x)
  product-constant-fin-sequence-type-Monoid M (succ-ℕ n@(succ-ℕ _)) x =
    ap-mul-Monoid M
      ( product-constant-fin-sequence-type-Monoid M n x)
      ( refl)
```
