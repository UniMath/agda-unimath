# Trivial groups

```agda
module group-theory.trivial-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.subgroups
open import group-theory.trivial-subgroups
```

</details>

## Idea

A [group](group-theory.groups.md) is said to be **trivial** if its underlying
type is [contractible](foundation-core.contractible-types.md). In other words, a
group is trivial if it consists only of the unit element.

## Definitions

### The predicate of being a trivial group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-trivial-prop-Group : Prop l1
  is-trivial-prop-Group = is-contr-Prop (type-Group G)

  is-trivial-Group : UU l1
  is-trivial-Group = type-Prop is-trivial-prop-Group
```

### The type of trivial groups

```agda
Trivial-Group : (l : Level) → UU (lsuc l)
Trivial-Group l = Σ (Group l) is-trivial-Group
```

### The trivial group

```agda
trivial-Group : Group lzero
pr1 (pr1 trivial-Group) = unit-Set
pr1 (pr2 (pr1 trivial-Group)) x y = star
pr2 (pr2 (pr1 trivial-Group)) x y z = refl
pr1 (pr2 trivial-Group) = (star , (refl-htpy , refl-htpy))
pr2 (pr2 trivial-Group) = ((λ x → star) , refl-htpy , refl-htpy)
```

## Properties

### The type of subgroups of a trivial group is contractible

This remains to be done.

### The trivial group is abelian

```agda
is-abelian-trivial-Group : is-abelian-Group trivial-Group
is-abelian-trivial-Group x y = refl

trivial-Ab : Ab lzero
trivial-Ab = (trivial-Group , is-abelian-trivial-Group)
```
