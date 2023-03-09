# Infinite sets

```agda
module set-theory.infinite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.existential-quantification
open import foundation.mere-embeddings
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A set `A` is said to be infinite if it contains arbitrarily large finite subsets.

## Definition

```agda
is-infinite-Set-Prop : {l : Level} → Set l → Prop l
is-infinite-Set-Prop X = Π-Prop ℕ (λ n → mere-emb-Prop (Fin n) (type-Set X))

is-infinite-Set : {l : Level} → Set l → UU l
is-infinite-Set X = type-Prop (is-infinite-Set-Prop X)
```
