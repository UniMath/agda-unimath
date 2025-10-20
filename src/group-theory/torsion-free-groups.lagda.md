# Torsion-free groups

```agda
module group-theory.torsion-free-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.nonzero-integers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.singleton-subtypes
open import foundation.standard-pullbacks
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.integer-powers-of-elements-groups
open import group-theory.orders-of-elements-groups
open import group-theory.subgroups
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
[equivalent](foundation.logical-equivalences.md) ways:

1. `∀ (k : nonzero-ℤ), xᵏ ＝ 1 → x ＝ 1`.
2. The [subset](group-theory.subsets-groups.md) of `G` of
   [torsion elements](group-theory.torsion-elements-groups.md) is a
   [singleton subtype](foundation.singleton-subtypes.md).
3. The map `p` in the [pullback square](foundation-core.pullbacks.md)
   ```text
             q
       · ---------> Prop
       | ⌟            |
      p|              | P ↦ {k : ℤ ∣ (k ＝ 0) ∨ P}
       ∨              ∨
       G -------> Subgroup ℤ
          order
   ```
   is an [equivalence](foundation.equivalences.md).

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

### The predicate that a group has a unique torsion element

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

### The predicate that the first projection of the pullback of `Prop lzero → Subgroup ℤ` along `order : G → Subgroup ℤ` is an equivalence

```agda
module _
  {l1 : Level} (G : Group l1)
  where

  is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group :
    Prop (lsuc l1)
  is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group =
    is-equiv-Prop
      ( vertical-map-standard-pullback
        { f = subgroup-order-element-Group G}
        { g = subgroup-Prop ℤ-Group})

  is-equiv-first-projection-pullback-subgroup-prop-Group : UU (lsuc l1)
  is-equiv-first-projection-pullback-subgroup-prop-Group =
    type-Prop is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group

  is-prop-is-equiv-first-projection-pullback-subgroup-prop-Group :
    is-prop is-equiv-first-projection-pullback-subgroup-prop-Group
  is-prop-is-equiv-first-projection-pullback-subgroup-prop-Group =
    is-prop-type-Prop
      ( is-equiv-vertical-map-standard-pullback-subgroup-prop-prop-Group)
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
    ap pr1 (eq-is-contr H {x , intro-exists k p} {unit-torsion-element-Group G})

  abstract
    has-unique-torsion-element-is-torsion-free-Group :
      is-torsion-free-Group G → has-unique-torsion-element-Group G
    has-unique-torsion-element-is-torsion-free-Group H =
      fundamental-theorem-id'
        ( ind-Id
          ( unit-Group G)
          ( λ y _ → is-torsion-element-Group G y)
          ( is-torsion-element-unit-Group G))
        ( λ x →
          is-equiv-has-converse-is-prop
            ( is-set-type-Group G (unit-Group G) x)
            ( is-prop-is-torsion-element-Group G x)
            ( elim-exists
              ( Id-Prop (set-Group G) (unit-Group G) x)
              ( λ k p → inv (H x k p))))
```
