# Finite Σ-decompositions of finite types

```agda
module univalent-combinatorics.sigma-decompositions where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.inhabited-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

## Idea

## Definition

```agda
Σ-Decomposition-𝔽 :
  {l : Level} → (l1 l2 : Level) → 𝔽 l → UU (l ⊔ lsuc l1 ⊔ lsuc l2)
Σ-Decomposition-𝔽 l1 l2 A =
  Σ ( 𝔽 l1)
    ( λ X →
      Σ ( type-𝔽 X → Inhabited-Type-𝔽 l2)
        ( λ Y → equiv-𝔽 A (Σ-𝔽 X (λ x → finite-type-Inhabited-Type-𝔽 (Y x)))))

module _
  {l l1 l2 : Level} (A : 𝔽 l) (D : Σ-Decomposition-𝔽 l1 l2 A)
  where

  finite-indexing-type-Σ-Decomposition-𝔽 : 𝔽 l1
  finite-indexing-type-Σ-Decomposition-𝔽 = pr1 D

  indexing-type-Σ-Decomposition-𝔽 : UU l1
  indexing-type-Σ-Decomposition-𝔽 =
    type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽

  inhabited-cotype-Σ-Decomposition-𝔽 :
    Fam-Inhabited-Types-𝔽 l2 finite-indexing-type-Σ-Decomposition-𝔽
  inhabited-cotype-Σ-Decomposition-𝔽 = pr1 (pr2 D)

  finite-cotype-Σ-Decomposition-𝔽 : type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽 → 𝔽 l2
  finite-cotype-Σ-Decomposition-𝔽 =
    finite-type-Fam-Inhabited-Types-𝔽
      finite-indexing-type-Σ-Decomposition-𝔽
      inhabited-cotype-Σ-Decomposition-𝔽

  cotype-Σ-Decomposition-𝔽 : type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽 → UU l2
  cotype-Σ-Decomposition-𝔽 x = type-𝔽 (finite-cotype-Σ-Decomposition-𝔽 x)

  is-inhabited-cotype-Σ-Decomposition-𝔽 :
   (x : type-𝔽 finite-indexing-type-Σ-Decomposition-𝔽) →
    is-inhabited (cotype-Σ-Decomposition-𝔽 x)
  is-inhabited-cotype-Σ-Decomposition-𝔽 x =
    is-inhabited-type-Inhabited-Type-𝔽 (inhabited-cotype-Σ-Decomposition-𝔽 x)

  matching-correspondence-Σ-Decomposition-𝔽 :
    type-𝔽 A ≃ Σ indexing-type-Σ-Decomposition-𝔽 cotype-Σ-Decomposition-𝔽
  matching-correspondence-Σ-Decomposition-𝔽 = pr2 (pr2 D)

  map-matching-correspondence-Σ-Decomposition-𝔽 :
    type-𝔽 A → Σ indexing-type-Σ-Decomposition-𝔽 cotype-Σ-Decomposition-𝔽
  map-matching-correspondence-Σ-Decomposition-𝔽 =
    map-equiv matching-correspondence-Σ-Decomposition-𝔽
```
