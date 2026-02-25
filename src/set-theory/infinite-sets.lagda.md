# Infinite sets

```agda
module set-theory.infinite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.mere-embeddings
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A [set](foundation-core.sets.md) `A` is said to be
{{#concept "infinite" Disambiguation="set" WD="infinite set" WDID=Q205140}} if
it contains arbitrarily [large](set-theory.cardinals.md)
[finite](univalent-combinatorics.finite-types.md)
[subsets](foundation-core.subtypes.md).

## Definition

### The predicate on a set of being infinite

```agda
is-infinite-Set-Prop : {l : Level} → Set l → Prop l
is-infinite-Set-Prop X = Π-Prop ℕ (λ n → mere-emb-Prop (Fin n) (type-Set X))

is-infinite-Set : {l : Level} → Set l → UU l
is-infinite-Set X = type-Prop (is-infinite-Set-Prop X)
```

### The universe of infinite sets

```agda
Infinite-Set : (l : Level) → UU (lsuc l)
Infinite-Set l = Σ (Set l) (is-infinite-Set)

module _
  {l : Level} (X : Infinite-Set l)
  where

  set-Infinite-Set : Set l
  set-Infinite-Set = pr1 X

  type-Infinite-Set : UU l
  type-Infinite-Set = type-Set set-Infinite-Set

  is-infinite-Infinite-Set : is-infinite-Set set-Infinite-Set
  is-infinite-Infinite-Set = pr2 X
```

## External links

- [infinite set](https://ncatlab.org/nlab/show/infinite+set) at $n$Lab
- [Infinite set](https://en.wikipedia.org/wiki/Infinite_set) at Wikipedia
