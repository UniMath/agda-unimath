# Alternating concrete groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module finite-group-theory.alternating-concrete-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.cartier-delooping-sign-homomorphism funext univalence truncations
open import finite-group-theory.finite-type-groups funext univalence truncations

open import foundation.universe-levels

open import group-theory.concrete-groups funext univalence truncations
open import group-theory.kernels-homomorphisms-concrete-groups funext univalence truncations
```

</details>

## Idea

The alternating concrete groups are the kernels of the concrete sign
homomorphism

## Definition

```agda
module _
  (n : ℕ)
  where

  alternating-Concrete-Group : Concrete-Group (lsuc (lsuc lzero))
  alternating-Concrete-Group =
    concrete-group-kernel-hom-Concrete-Group
      ( Type-With-Cardinality-ℕ-Concrete-Group lzero n)
      ( Type-With-Cardinality-ℕ-Concrete-Group (lsuc lzero) 2)
      ( cartier-delooping-sign n)
```
