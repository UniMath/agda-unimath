# Algebraic theory of groups

```agda
module universal-algebra.algebraic-theory-of-groups where
```

<details><summary>Imports</summary>

```agda
open import lists.tuples
open import universal-algebra.algebraic-theory-of-monoids
open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import foundation.dependent-pair-types
open import universal-algebra.homomorphisms-of-algebras
open import foundation.universe-levels
open import universal-algebra.signatures
open import universal-algebra.terms-over-signatures
```

</details>

## Idea

There is an
{{#concept "algebraic theory of groups" Agda=algebraic-theory-Group}}. The type
of all such [algebras](universal-algebra.algebras.md) is
[equivalent](foundation-core.equivalences.md) to the type of
[groups](group-theory.groups.md).

## Definitions

### The algebra of groups

```agda
data operation-Group : UU lzero where
  operation-group-operation-Monoid : operation-Monoid → operation-Group
  inv-operation-Group : operation-Group

pattern mul-operation-Group =
  operation-group-operation-Monoid mul-operation-Monoid
pattern unit-operation-Group =
  operation-group-operation-Monoid unit-operation-Monoid

signature-Group : signature lzero
pr1 signature-Group = operation-Group
pr2 signature-Group (operation-group-operation-Monoid op) =
  arity-operation-signature signature-Monoid op
pr2 signature-Group inv-operation-Group = 1

data law-Group : UU lzero where

```
