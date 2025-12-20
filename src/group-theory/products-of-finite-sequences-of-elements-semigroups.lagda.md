# Products of finite sequences of elements in semigroups

```agda
module group-theory.products-of-finite-sequences-of-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semigroups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite sequence in a semigroup" WD="product" WDID=Q218005 Agda=product-fin-sequence-type-Semigroup}}
extends the binary operation on a [semigroup](group-theory.semigroups.md) `G` to
any nonempty [finite sequence](lists.finite-sequences.md) of elements of `G`.

## Definition

```agda
product-fin-sequence-type-Semigroup :
  {l : Level} (G : Semigroup l) (n : ℕ) →
  fin-sequence-type-Semigroup G (succ-ℕ n) → type-Semigroup G
product-fin-sequence-type-Semigroup G zero-ℕ f = f (inr star)
product-fin-sequence-type-Semigroup G (succ-ℕ n) f =
  mul-Semigroup G
    ( product-fin-sequence-type-Semigroup G n (f ∘ inl-Fin (succ-ℕ n)))
    ( f (inr star))
```

## Properties

### Products are homotopy invariant

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  htpy-product-fin-sequence-type-Semigroup :
    (n : ℕ) → {f g : fin-sequence-type-Semigroup G (succ-ℕ n)} →
    f ~ g →
    product-fin-sequence-type-Semigroup G n f ＝
    product-fin-sequence-type-Semigroup G n g
  htpy-product-fin-sequence-type-Semigroup n f~g =
    ap (product-fin-sequence-type-Semigroup G n) (eq-htpy f~g)
```

### Splitting products of `succ-ℕ n + succ-ℕ m` elements into a product of `succ-ℕ n` elements and a product of `succ-ℕ m` elements

```agda
abstract
  split-product-fin-sequence-type-Semigroup :
    {l : Level} (G : Semigroup l)
    (n m : ℕ) (f : fin-sequence-type-Semigroup G (succ-ℕ n +ℕ succ-ℕ m)) →
    product-fin-sequence-type-Semigroup G (succ-ℕ n +ℕ m) f ＝
    mul-Semigroup G
      ( product-fin-sequence-type-Semigroup G n
        ( f ∘ inl-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
      ( product-fin-sequence-type-Semigroup G m
        ( f ∘ inr-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
  split-product-fin-sequence-type-Semigroup G n zero-ℕ f = refl
  split-product-fin-sequence-type-Semigroup G n (succ-ℕ m) f =
    ap-mul-Semigroup G
      ( split-product-fin-sequence-type-Semigroup G n m (f ∘ inl))
      ( refl) ∙
    associative-mul-Semigroup G _ _ _
```
