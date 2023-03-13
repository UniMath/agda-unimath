# Trivial subgroups

```agda
module group-theory.trivial-subgroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
```

</details>

## Idea

A subgroup `H` of `G` is said to be trivial if it only contains the unit element
of `G`.

## Definitions

### Trivial subgroups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Subgroup l2 G)
  where

  is-trivial-Subgroup : UU (l1 ⊔ l2)
  is-trivial-Subgroup =
    (x : type-Group G) → is-in-Subgroup G H x → x ＝ unit-Group G
```

### The trivial subgroup

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  trivial-Subgroup : Subgroup l1 G
  pr1 trivial-Subgroup x = is-unit-group-Prop G x
  pr1 (pr2 trivial-Subgroup) = refl
  pr1 (pr2 (pr2 trivial-Subgroup)) .(unit-Group G) .(unit-Group G) refl refl =
    left-unit-law-mul-Group G (unit-Group G)
  pr2 (pr2 (pr2 trivial-Subgroup)) .(unit-Group G) refl =
    inv-unit-Group G
```
