# Binary operations on unordered pairs of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.binary-operations-unordered-pairs-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.products-unordered-pairs-of-types funext univalence truncations
open import foundation.universe-levels
open import foundation.unordered-pairs funext univalence truncations
```

</details>

## Idea

A binary operation on an unordered pair of types A indexed by a 2-element type I
is a map `((i : I) → A i) → B`.

## Definition

```agda
binary-operation-unordered-pair-types :
  {l1 l2 : Level} (A : unordered-pair (UU l1)) (B : UU l2) → UU (l1 ⊔ l2)
binary-operation-unordered-pair-types A B = product-unordered-pair-types A → B
```
