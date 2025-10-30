# Alkynes

```agda
module organic-chemistry.alkynes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.universe-levels

open import organic-chemistry.hydrocarbons
open import organic-chemistry.saturated-carbons

open import univalent-combinatorics.finite-types
```

</details>

## Idea

An $n$-{{#concept "alkyne" WD="alkyne" WDID=Q159226 Agda=alkyne}} is a
[hydrocarbon](organic-chemistry.hydrocarbons.md) equipped with a choice of $n$
carbons, each of which has a triple bond.

## Definition

```agda
alkyne : {l1 l2 : Level} → hydrocarbon l1 l2 → ℕ → UU (lsuc l1 ⊔ l2)
alkyne {l1} {l2} H n =
  Σ ( Type-With-Cardinality-ℕ l1 n)
    ( λ carbons →
      Σ ( type-Type-With-Cardinality-ℕ n carbons ↪ vertex-hydrocarbon H)
        ( λ embed-carbons →
          (c : type-Type-With-Cardinality-ℕ n carbons) →
          has-triple-bond-hydrocarbon H (pr1 embed-carbons c)))
```
