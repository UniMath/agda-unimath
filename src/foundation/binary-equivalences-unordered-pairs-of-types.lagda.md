# Binary equivalences on unordered pairs of types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.binary-equivalences-unordered-pairs-of-types
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-operations-unordered-pairs-of-types funext univalence truncations
open import foundation.products-unordered-pairs-of-types funext univalence truncations
open import foundation.universe-levels
open import foundation.unordered-pairs funext univalence truncations

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

A binary operation `f : ((i : I) → A i) → B` is a binary equivalence if for each
`i : I` and each `x : A i` the map `f ∘ pair x : A (swap i) → B` is an
equivalence.

## Definition

```agda
is-binary-equiv-unordered-pair-types :
  {l1 l2 : Level} (A : unordered-pair (UU l1)) {B : UU l2}
  (f : binary-operation-unordered-pair-types A B) → UU (l1 ⊔ l2)
is-binary-equiv-unordered-pair-types A f =
  (i : type-unordered-pair A) (x : element-unordered-pair A i) →
  is-equiv (f ∘ pair-product-unordered-pair-types A i x)
```
