# Trivial subgroups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.trivial-subgroups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import group-theory.groups funext
open import group-theory.subgroups funext
```

</details>

## Idea

A [subgroup](group-theory.subgroups.md) `H` of `G` is said to be **trivial** if
it only contains the unit element of `G`.

## Definitions

### The trivial subgroup

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  trivial-Subgroup : Subgroup l1 G
  pr1 trivial-Subgroup x = is-unit-prop-Group' G x
  pr1 (pr2 trivial-Subgroup) = refl
  pr1 (pr2 (pr2 trivial-Subgroup)) refl refl =
    inv (left-unit-law-mul-Group G (unit-Group G))
  pr2 (pr2 (pr2 trivial-Subgroup)) refl =
    inv (inv-unit-Group G)
```

### The predicate of being a trivial subgroup

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-trivial-Subgroup : UU (l1 ⊔ l2)
  is-trivial-Subgroup = leq-Subgroup G H (trivial-Subgroup G)
```
