# The algebraic theory of abelian groups

```agda
module universal-algebra.algebraic-theory-of-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.groups

open import lists.tuples

open import univalent-combinatorics.standard-finite-types

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.algebraic-theories
open import universal-algebra.algebraic-theory-of-groups
open import universal-algebra.algebras
open import universal-algebra.extensions-signatures
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.models-of-signatures
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

## Definition

```agda
operation-Ab : UU lzero
operation-Ab = operation-Group

pattern zero-operation-Ab = unit-operation-Group
pattern add-operation-Ab = ?

signature-Ab : signature lzero
signature-Ab = signature-Group
```
