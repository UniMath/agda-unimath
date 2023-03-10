# Equivalences of species

```agda
module univalent-combinatorics.equivalences-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.species
```

</details>

## Idea

An equivalence of species from `F` to `G` is a pointwise equivalence.

## Definition

```agda
equiv-species :
  {l1 l2 l3 : Level} → species l1 l2 → species l1 l3 →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
equiv-species {l1} F G = (X : 𝔽 l1) → F X ≃ G X
```

## Properties

### The identity type of two species is equivalent to the type of equivalences between them

```agda
extensionality-species :
  {l1 l2 : Level} (F : species l1 l2) (G : species l1 l2) →
  (Id F G) ≃ (equiv-species F G)
extensionality-species = extensionality-fam
```
