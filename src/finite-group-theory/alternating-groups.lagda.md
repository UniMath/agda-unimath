# Alternating groups

```agda
module finite-group-theory.alternating-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.sign-homomorphism

open import group-theory.groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.symmetric-groups

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "alternating group" Disambiguation="on a finite set" Agda=alternating-Group}}
on a [finite set](univalent-combinatorics.finite-types.md) `X` is the
[group](group-theory.groups.md) of even permutations of `X`, i.e., it is the
[kernel](group-theory.kernels-homomorphisms-groups.md) of the
[sign homomorphism](finite-group-theory.sign-homomorphism.md) `Aut(X) → Aut(2)`.

## Definition

```agda
module _
  {l} (n : ℕ) (X : Type-With-Cardinality-ℕ l n)
  where

  alternating-Group : Group l
  alternating-Group = group-kernel-hom-Group
    ( symmetric-Group (set-Type-With-Cardinality-ℕ n X))
    ( symmetric-Group (Fin-Set 2))
    ( sign-homomorphism n X)
```
