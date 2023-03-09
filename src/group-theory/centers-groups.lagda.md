# The center of a group

```agda
module group-theory.centers-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.subgroups
```

</details>

## Idea

The **center** of a group `G` is the normal subgroup consisting of all elements `g : G` that commute with every element of `G`.

## Definition

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  subtype-center-Group : subset-Group l1 G
  subtype-center-Group g =
    Π-Prop
      ( type-Group G)
      ( λ h → Id-Prop (set-Group G) (mul-Group G g h) (mul-Group G h g))

  contains-unit-center-Group : contains-unit-subset-Group G subtype-center-Group
  contains-unit-center-Group h =
    ( left-unit-law-mul-Group G h) ∙
    ( inv (right-unit-law-mul-Group G h))

  is-closed-under-mul-center-Group :
    is-closed-under-mul-subset-Group G subtype-center-Group
  is-closed-under-mul-center-Group g1 g2 H1 H2 h =
    ( associative-mul-Group G g1 g2 h) ∙
    ( ( ap (mul-Group G g1) (H2 h)) ∙
      ( ( inv (associative-mul-Group G g1 h g2)) ∙
        ( ( ap (mul-Group' G g2) (H1 h)) ∙
          ( associative-mul-Group G h g1 g2))))

  is-closed-under-inv-center-Group :
    is-closed-under-inv-subset-Group G subtype-center-Group
  is-closed-under-inv-center-Group g H h =
    ( inv (inv-inv-Group G (mul-Group G (inv-Group G g) h))) ∙
    ( ( ap (inv-Group G) (distributive-inv-mul-Group G (inv-Group G g) h)) ∙
      ( ( ap
          ( inv-Group G)
          ( ap (mul-Group G (inv-Group G h)) (inv-inv-Group G g))) ∙
        ( ( inv (ap (inv-Group G) (H (inv-Group G h)))) ∙
          ( ( distributive-inv-mul-Group G g (inv-Group G h)) ∙
            ( ap (mul-Group' G (inv-Group G g)) (inv-inv-Group G h))))))

  subgroup-center-Group : Subgroup l1 G
  pr1 subgroup-center-Group = subtype-center-Group
  pr1 (pr2 subgroup-center-Group) = contains-unit-center-Group
  pr1 (pr2 (pr2 subgroup-center-Group)) = is-closed-under-mul-center-Group
  pr2 (pr2 (pr2 subgroup-center-Group)) = is-closed-under-inv-center-Group
```
