# Alternating groups

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module finite-group-theory.alternating-groups
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.sign-homomorphism funext univalence truncations

open import group-theory.groups funext univalence truncations
open import group-theory.kernels-homomorphisms-groups funext univalence truncations
open import group-theory.symmetric-groups funext univalence truncations

open import univalent-combinatorics.finite-types funext univalence truncations
open import univalent-combinatorics.standard-finite-types funext univalence truncations
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
