# Unordered tuples of elements in commutative monoids

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module group-theory.unordered-tuples-of-elements-commutative-monoids
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
open import foundation.unordered-tuples funext univalence truncations

open import group-theory.commutative-monoids funext univalence truncations
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
