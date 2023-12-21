# Products of tuples of types

```agda
module foundation.products-of-tuples-of-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.tuples-of-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
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
