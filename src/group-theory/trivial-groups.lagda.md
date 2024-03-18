# Trivial groups

```agda
module group-theory.trivial-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.unit-type
open import foundation.universe-levels

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

  is-prop-is-trivial-Group : is-prop is-trivial-Group
  is-prop-is-trivial-Group = is-prop-type-Prop is-trivial-prop-Group

trivial-groups : {l : Level} → UU (lsuc l)
trivial-groups = Σ (Group _) is-trivial-Group
```

## Properties

### The type of subgroups of a trivial group is contractible

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  abstract
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

### "The" trivial group is abelian

```agda
0-group : Group lzero
pr1 (pr1 0-group) = unit-Set
pr1 (pr2 (pr1 0-group)) = λ x y → star
pr2 (pr2 (pr1 0-group)) = λ x y z → refl
pr1 (pr2 0-group) = star , ((λ x → refl) , (λ x → refl))
pr2 (pr2 0-group) = (λ x → star) , (λ x → refl) , (λ x → refl)

is-abelian-0-group : is-abelian-Group 0-group
is-abelian-0-group = λ x y → refl

ab-0-group : Ab lzero
ab-0-group = 0-group , is-abelian-0-group
```

### The type of trivial groups is contractible

This remains to be done. It requires first classifying identity types of groups
using the structure identity principle, shouldn't be too hard (perhaps it's
already a lemma in the category-theory modules?) but needs to be done.
