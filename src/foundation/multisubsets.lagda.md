# Multisubsets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.multisubsets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.images funext univalence truncations
open import foundation.negated-equality funext univalence truncations
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.sets

open import univalent-combinatorics.finite-types funext univalence truncations
```

</details>

## Idea

A multisubset of a given set `U` is a type `B` equipped with a function
`f : B → U`

## Definition

```agda
module _
  {l1 : Level} (l2 : Level)
  where

  multisubset : Set l1 → UU (l1 ⊔ lsuc l2)
  multisubset U = Σ (UU l2) (λ B → B → type-Set U)

  is-locally-finite-multisubset :
    (U : Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-locally-finite-multisubset U (pair B f) =
    (x : type-Set U) → is-finite (fiber f x)

  is-finite-multisubset :
    (U : Set l1) → multisubset U → UU (l1 ⊔ l2)
  is-finite-multisubset U (pair B f) = is-finite (im f)

module _
  {l1 : Level}
  where

  locally-finite-multisubset : Set l1 → UU l1
  locally-finite-multisubset U = type-Set U → ℕ

  support-locally-finite-multisubset :
    (U : Set l1) → locally-finite-multisubset U → UU l1
  support-locally-finite-multisubset U μ =
    Σ (type-Set U) (λ x → μ x ≠ 0)

  is-finite-locally-finite-multisubset :
    (U : Set l1) → locally-finite-multisubset U → UU l1
  is-finite-locally-finite-multisubset U μ =
    is-finite (support-locally-finite-multisubset U μ)
```
