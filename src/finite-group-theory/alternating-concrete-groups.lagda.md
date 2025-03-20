# Alternating concrete groups

```agda
open import foundation.function-extensionality-axiom

module
  finite-group-theory.alternating-concrete-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.cartier-delooping-sign-homomorphism funext
open import finite-group-theory.finite-type-groups funext

open import foundation.universe-levels

open import group-theory.concrete-groups funext
open import group-theory.kernels-homomorphisms-concrete-groups funext
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
