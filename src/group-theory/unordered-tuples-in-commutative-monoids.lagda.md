# Unordered tuples of elements in commutative monoids

```agda
module group-theory.unordered-tuples-in-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.unordered-tuples

open import group-theory.commutative-monoids
```

</details>

## Definition

```agda
unordered-tuple-Commutative-Monoid :
  {l : Level} (n : ℕ) (M : Commutative-Monoid l) → UU (lsuc lzero ⊔ l)
unordered-tuple-Commutative-Monoid n M =
  unordered-tuple n (type-Commutative-Monoid M)

module _
  {l : Level} {n : ℕ} (M : Commutative-Monoid l)
  (x : unordered-tuple-Commutative-Monoid n M)
  where

  type-unordered-tuple-Commutative-Monoid : UU lzero
  type-unordered-tuple-Commutative-Monoid = type-unordered-tuple n x

  element-unordered-tuple-Commutative-Monoid :
    type-unordered-tuple-Commutative-Monoid → type-Commutative-Monoid M
  element-unordered-tuple-Commutative-Monoid =
    element-unordered-tuple n x
```
