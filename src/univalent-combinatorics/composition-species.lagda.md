# Composition of species

```agda
module univalent-combinatorics.composition-species where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.equivalences-species
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.partitions
open import univalent-combinatorics.sigma-decompositions
open import univalent-combinatorics.species
```

</details>

## Idea

A species `S : 𝔽 → UU l` can be thought of as the analytic endofunctor

```md
  X ↦ Σ (A : 𝔽) (S A) × (A → X)
```

Using the formula for composition of analytic endofunctors, we obtain a way to compose species.

## Definition

### Analytic composition of species

```agda
analytic-comp-species :
  {l1 l2 l3 : Level} → species l1 l2 → species l1 l3 →
  species l1 (lsuc l1 ⊔ l2 ⊔ l3)
analytic-comp-species {l1} {l2} {l3} S T X =
  Σ ( Σ-Decomposition-𝔽 l1 l1 X)
    ( λ D →
      ( T (finite-indexing-type-Σ-Decomposition-𝔽 X D) ×
      ( (y : indexing-type-Σ-Decomposition-𝔽 X D) →
      S (finite-cotype-Σ-Decomposition-𝔽 X D y ))))
```

### The analytic unit for composition of species

 ```agda
analytic-unit-species : {l1 : Level} → species l1 l1
analytic-unit-species X = is-contr (type-𝔽 X)

```

## Properties

### Unit laws for analytic composition of species

```agda
{-
left-unit-law-comp-species :
  {l1 l2 : Level} (F : species l1 l2) →
  equiv-species (analytic-comp-species analytic-unit-species F) F
left-unit-law-comp-species F X =
  {!!}
-}
```
