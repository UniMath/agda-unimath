# Multiset-indexed dependent products of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module trees.multiset-indexed-dependent-products-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import trees.multisets funext univalence truncations
open import trees.w-types funext univalence truncations
```

</details>

## Idea

Consider a [multiset](trees.multisets.md) `M`. Then `M` can be seen as a tower
of type families, via the inclusion from the type of all multisets, which are
the well-founded trees, into the type of all trees.

This leads to the idea that we should be able to take the iterated dependent
product of this tower of type families.

## Definitions

### The iterated dependent product of types indexed by a multiset

```agda
iterated-Π-𝕍 : {l : Level} → ℕ → 𝕍 l → UU l
iterated-Π-𝕍 zero-ℕ (tree-𝕎 X Y) = X
iterated-Π-𝕍 (succ-ℕ n) (tree-𝕎 X Y) = (x : X) → iterated-Π-𝕍 n (Y x)
```
