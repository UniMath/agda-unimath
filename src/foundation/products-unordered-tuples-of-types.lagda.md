# Products of unordered tuples of types

```agda
module foundation.products-unordered-tuples-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-function-types
open import foundation.universal-property-maybe
open import foundation.universe-levels
open import foundation.unordered-tuples
open import foundation.unordered-tuples-of-types

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences

open import univalent-combinatorics.complements-isolated-elements
```

</details>

## Idea

Given an unordered pair of types, we can take their product. This is a
commutative version of the cartesian product operation on types.

## Definition

```agda
product-unordered-tuple-types :
  {l : Level} (n : ℕ) → unordered-tuple n (UU l) → (UU l)
product-unordered-tuple-types n p =
  (x : type-unordered-tuple n p) → element-unordered-tuple n p x

pr-product-unordered-tuple-types :
  {l : Level} (n : ℕ) (A : unordered-tuple-types l n)
  (i : type-unordered-tuple n A) →
  product-unordered-tuple-types n A → element-unordered-tuple n A i
pr-product-unordered-tuple-types n A i f = f i

equiv-pr-product-unordered-tuple-types :
  {l : Level} (n : ℕ) (A : unordered-tuple-types l (succ-ℕ n))
  (i : type-unordered-tuple (succ-ℕ n) A) →
  ( ( product-unordered-tuple-types n
      ( unordered-tuple-complement-point-type-unordered-tuple n A i)) ×
    ( element-unordered-tuple (succ-ℕ n) A i)) ≃
  product-unordered-tuple-types (succ-ℕ n) A
equiv-pr-product-unordered-tuple-types n A i =
  ( equiv-Π
    ( element-unordered-tuple (succ-ℕ n) A)
    ( equiv-maybe-structure-element-Type-With-Cardinality-ℕ n
      ( type-unordered-tuple-Type-With-Cardinality-ℕ (succ-ℕ n) A) i)
    ( λ x → id-equiv)) ∘e
  ( inv-equiv
    ( equiv-dependent-universal-property-Maybe
      ( λ j →
        element-unordered-tuple (succ-ℕ n) A
          ( map-equiv
            ( equiv-maybe-structure-element-Type-With-Cardinality-ℕ n
              ( type-unordered-tuple-Type-With-Cardinality-ℕ (succ-ℕ n) A)
              ( i))
            ( j)))))

map-equiv-pr-product-unordered-tuple-types :
  {l : Level} (n : ℕ) (A : unordered-tuple-types l (succ-ℕ n))
  (i : type-unordered-tuple (succ-ℕ n) A) →
  product-unordered-tuple-types n
    ( unordered-tuple-complement-point-type-unordered-tuple n A i) →
  element-unordered-tuple (succ-ℕ n) A i →
  product-unordered-tuple-types (succ-ℕ n) A
map-equiv-pr-product-unordered-tuple-types n A i f a =
  map-equiv (equiv-pr-product-unordered-tuple-types n A i) (pair f a)
```

### Equivalences of products of unordered pairs of types

```agda
module _
  {l1 l2 : Level} {n : ℕ} (A : unordered-tuple-types l1 n)
  (B : unordered-tuple-types l2 n)
  where

  equiv-product-unordered-tuple-types :
    equiv-unordered-tuple-types n A B →
    product-unordered-tuple-types n A ≃ product-unordered-tuple-types n B
  equiv-product-unordered-tuple-types e =
    equiv-Π
      ( element-unordered-tuple n B)
      ( equiv-type-equiv-unordered-tuple-types n A B e)
      ( equiv-element-equiv-unordered-tuple-types n A B e)
```
