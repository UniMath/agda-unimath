# Torsion-free groups

```agda
module group-theory.torsion-free-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.singleton-subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.torsion-elements-groups
```

</details>

## Idea

A **torsion-free group** is a [group](group-theory.groups.md) `G` in which any
element of finite [order](group-theory.orders-of-elements-groups.md) is the
identity element. In other words, torsion-free groups are groups in which the
condition

```text
  ∀ (k : nonzero-ℤ), xᵏ ＝ 1 → x ＝ 1
```

holds for all elements `x : G`. This condition can be formulated in several
equivalent ways:

1. `∀ (k : nonzero-ℤ), xᵏ ＝ 1 → x ＝ 1`.
2. The [subset](group-theory.subsets-groups.md) of `G` of
   [torsion elements](group-theory.torsion-elements-groups.md) is a
   [singleton subtype](foundation.singleton-subtypes.md).

There is another closely related condition, which asserts that the
[image](foundation.images.md) of the map `order : G → subgroup ℤ` is a
[2-element type](univalent-combinatorics.2-element-types.md). Groups satisfying
this condition are _nontrivial_ torsion-free groups.

## Definitions

### The predicate of being a torsion-free group

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-torsion-free-prop-Group : Prop l1
  is-torsion-free-prop-Group =
    Π-Prop
      ( type-Group G)
      ( λ x →
        Π-Prop
          ( nonzero-ℤ)
          ( λ k →
            function-Prop
              ( integer-power-Group G (int-nonzero-ℤ k) x ＝ unit-Group G)
              ( Id-Prop (set-Group G) x (unit-Group G))))

  is-torsion-free-Group : UU l1
  is-torsion-free-Group = type-Prop is-torsion-free-prop-Group

  is-prop-is-torsion-free-Group : is-prop is-torsion-free-Group
  is-prop-is-torsion-free-Group = is-prop-type-Prop is-torsion-free-prop-Group
```

### The group has a unique torsion element

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  has-unique-torsion-element-prop-Group : Prop l1
  has-unique-torsion-element-prop-Group =
    is-singleton-subtype-Prop (is-torsion-element-prop-Group G)

  has-unique-torsion-element-Group : UU l1
  has-unique-torsion-element-Group =
    is-singleton-subtype (is-torsion-element-prop-Group G)

  is-prop-has-unique-torsion-element-Group :
    is-prop has-unique-torsion-element-Group
  is-prop-has-unique-torsion-element-Group =
    is-prop-is-singleton-subtype (is-torsion-element-prop-Group G)
```

## Properties

### The two definitions of torsion-free groups are equivalent

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-torsion-free-has-unique-torsion-element-Group :
    has-unique-torsion-element-Group G → is-torsion-free-Group G
  is-torsion-free-has-unique-torsion-element-Group H x k p =
    ap pr1 (eq-is-contr H {x , intro-∃ k p} {unit-torsion-element-Group G})

  has-unique-torsion-element-is-torsion-free-Group :
    is-torsion-free-Group G → has-unique-torsion-element-Group G
  has-unique-torsion-element-is-torsion-free-Group H =
    fundamental-theorem-id'
      ( λ where x refl → is-torsion-element-unit-Group G)
      ( λ x →
        is-equiv-is-prop
          ( is-set-type-Group G _ _)
          ( is-prop-is-torsion-element-Group G x)
          ( elim-exists-Prop
              ( λ k → Id-Prop (set-Group G) _ _)
              ( Id-Prop (set-Group G) _ _)
              ( λ k p → inv (H x k p))))
```
