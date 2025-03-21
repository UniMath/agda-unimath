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

The alternating group on a finite set `X` is the group of even permutations of
`X`, i.e. it is the kernel of the sign homomorphism `Aut(X) → Aut(2)`.

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
