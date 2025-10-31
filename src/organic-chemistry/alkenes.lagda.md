# Alkenes

```agda
module organic-chemistry.alkenes where
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

An $n$-{{#concept "alkene" WD="alkene" WDID=Q81406 Agda=alkene}} is a
[hydrocarbon](organic-chemistry.hydrocarbons.md)
[equipped](foundation.structure.md) with a choice of $n$ carbons, each of which
has a double bond. For an $n$-alkene, the
[embedding](foundation-core.embeddings.md) from the given type (the first
component of the $n$-alkene structure) specifies which carbons have double
bonds. For example, 1-butene and but-2-ene have the same geometry, and the
embedding is what differentiates them (while the third tautometer, isobutylene,
is branched, thus has a different geometry).

## Definition

```agda
alkene : {l1 l2 : Level} → hydrocarbon l1 l2 → ℕ → UU (lsuc lzero ⊔ l1 ⊔ l2)
alkene H n =
  Σ ( Type-With-Cardinality-ℕ lzero n)
    ( λ carbons →
      Σ ( type-Type-With-Cardinality-ℕ n carbons ↪ vertex-hydrocarbon H)
        ( λ embed-carbons →
          ( c : type-Type-With-Cardinality-ℕ n carbons) →
          has-double-bond-hydrocarbon H (map-emb embed-carbons c)))
```
