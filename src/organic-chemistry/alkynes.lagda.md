# Alkynes

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module organic-chemistry.alkynes
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings funext
open import foundation.universe-levels

open import organic-chemistry.hydrocarbons funext univalence truncations
open import organic-chemistry.saturated-carbons funext univalence truncations

open import univalent-combinatorics.finite-types funext univalence truncations
```

</details>

## Idea

An **n-alkyne** is a hydrocarbon equipped with a choice of $n$ carbons, each of
which has a triple bond.

## Definition

```agda
n-alkyne : {l1 l2 : Level} → hydrocarbon l1 l2 → ℕ → UU (lsuc l1 ⊔ l2)
n-alkyne {l1} {l2} H n =
  Σ ( Type-With-Cardinality-ℕ l1 n)
    ( λ carbons →
      Σ ( type-Type-With-Cardinality-ℕ n carbons ↪ vertex-hydrocarbon H)
        ( λ embed-carbons →
          (c : type-Type-With-Cardinality-ℕ n carbons) →
          has-triple-bond-hydrocarbon H (pr1 embed-carbons c)))
```
