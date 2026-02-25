# Alternating concrete groups

```agda
module finite-group-theory.alternating-concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.cartier-delooping-sign-homomorphism
open import finite-group-theory.finite-type-groups

open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.kernels-homomorphisms-concrete-groups
```

</details>

## Idea

The [concrete](group-theory.concrete-groups.md)
{{#concept "alternating groups" Disambiguation="concrete" WD="alternating group" WDID=Q438814 Agda=alternating-Concrete-Group}}
are the [kernels](group-theory.kernels-homomorphisms-concrete-groups.md) of the
[concrete sign homomorphism](finite-group-theory.cartier-delooping-sign-homomorphism.md).

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
