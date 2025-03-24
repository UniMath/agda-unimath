# Products of tuples of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.products-of-tuples-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.tuples-of-types funext univalence truncations
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

The product of an `n`-tuple of types is their dependent product.

## Definition

### Products of `n`-tuples of types

```agda
product-tuple-types :
  {l : Level} (n : ℕ) → tuple-types l n → UU l
product-tuple-types n A = (i : Fin n) → A i
```

### The projection maps

```agda
pr-product-tuple-types :
  {l : Level} {n : ℕ} (A : tuple-types l n) (i : Fin n) →
  product-tuple-types n A → A i
pr-product-tuple-types A i f = f i
```
