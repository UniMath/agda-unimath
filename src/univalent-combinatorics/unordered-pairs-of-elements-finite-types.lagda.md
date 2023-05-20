# Unordered pairs of elements in finite types

```agda
module univalent-combinatorics.unordered-pairs-of-elements-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.unordered-pairs public

open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
open import univalent-combinatorics.pi-finite-types
```

</details>

## Idea

The type of [unordered pairs](foundation.unordered-pairs.md) of elements in a [finite type](univalent-combinatorics.finite-types.md) is a [π-finite type](univalent-combinatorics.pi-finite-types.md).

Note: The type of unordered pairs in a π-finite type is also π-finite. However, we haven't shown yet that π-finite types are closed under dependent products.

## Properties

### The type of unordered pairs of elements in a finite type is π-finite.

```agda
module _
  {l1 : Level} (X : 𝔽 l1)
  where

  is-π-finite-unordered-pair-𝔽 :
    (k : ℕ) → is-π-finite k (unordered-pair (type-𝔽 X))
  is-π-finite-unordered-pair-𝔽 k =
    is-π-finite-Σ k
      ( is-π-finite-UU-Fin (succ-ℕ k) 2)
      ( λ I →
        is-π-finite-is-finite k
          ( is-finite-function-type
            ( is-finite-has-cardinality 2 (has-cardinality-type-UU-Fin 2 I))
            ( is-finite-type-𝔽 X)))
```
