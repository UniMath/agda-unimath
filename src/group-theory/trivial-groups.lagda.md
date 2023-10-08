# Trivial groups

```agda
module group-theory.trivial-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

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

  is-prop-is-trivial-Group : is-prop is-trivial-Group
  is-prop-is-trivial-Group = is-prop-type-Prop is-trivial-prop-Group
```

## Properties

### The type of subgroups of a trivial group is contractible

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-contr-subgroup-is-trivial-Group :
    is-trivial-Group G → is-contr (Subgroup l1 G)
  pr1 (is-contr-subgroup-is-trivial-Group H) =
    trivial-Subgroup G
  pr2 (is-contr-subgroup-is-trivial-Group H) K =
    eq-has-same-elements-Subgroup G
      ( trivial-Subgroup G)
      ( K)
      ( λ x →
        ( λ where refl → contains-unit-Subgroup G K) ,
        ( λ _ →
          is-closed-under-eq-Subgroup G
            ( trivial-Subgroup G)
            ( contains-unit-Subgroup G (trivial-Subgroup G))
            ( eq-is-contr H)))
```
