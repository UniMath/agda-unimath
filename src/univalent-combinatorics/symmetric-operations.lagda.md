# Symmetric operations on finite sets

```agda
module univalent-combinatorics.symmetric-operations where
```

<details><summary>Imports</summary>

```agda
open import foundation.symmetric-operations public

open import foundation.universe-levels

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.function-types
```

## Idea

The type of [symmetric operations](foundation.symmetric-operations.md) from one [finite type](univalent-combinatorics.finite-types.md) into another is finite.

## Properties

### The type of symmetric operations from one finite type into another is finite

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-finite-symmetric-operation :
    is-finite A → is-finite B → is-finite (symmetric-operation A B)
  is-finite-symmetric-operation H K =
    is-finite-equiv'
      ( compute-symmetric-operation-Set A (B , is-set-is-finite K))
      ( is-finite-Σ
        ( is-finite-function-type H (is-finite-function-type H K))
        ( λ f →
          is-finite-Π H
            ( λ x →
              is-finite-Π H
                ( λ y → is-finite-eq (has-decidable-equality-is-finite K)))))

symmetric-operation-𝔽 :
  {l1 l2 : Level} → 𝔽 l1 → 𝔽 l2 → 𝔽 (lsuc lzero ⊔ l1 ⊔ l2)
pr1 (symmetric-operation-𝔽 A B) =
  symmetric-operation (type-𝔽 A) (type-𝔽 B)
pr2 (symmetric-operation-𝔽 A B) =
  is-finite-symmetric-operation (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)
```
