# `G`-spaces

```agda
module structured-types.g-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.0-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import foundation-core.endomorphisms
open import group-theory.concrete-group-actions
open import group-theory.concrete-groups
open import foundation-core.propositions

open import structured-types.magmas
open import structured-types.noncoherent-h-spaces
open import structured-types.pointed-sections
open import structured-types.pointed-types
```

</details>

## Idea

Given a [concrete group](group-theory.concrete-groups.md) `G`, a `G`-**space**
is a type [equipped](foundation.structure.md) with a
[$0$-truncated map](foundation.0-maps.md) to `BG`.

## Definition

```agda
G-Space : {l1 : Level} (G : Concrete-Group l1) (l2 : Level) → UU (l1 ⊔ lsuc l2)
G-Space G l2 = Σ (UU l2) (λ X → 0-map X (classifying-type-Concrete-Group G))
```
