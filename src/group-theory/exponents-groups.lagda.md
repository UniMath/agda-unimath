# Exponents of groups

```agda
module group-theory.exponents-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers

open import foundation.universe-levels

open import group-theory.free-groups-with-one-generator
open import group-theory.groups
open import group-theory.intersections-subgroups-groups
open import group-theory.kernels-homomorphisms-groups
open import group-theory.subgroups
```

</details>

The **exponent** `exp G` of a [group](group-theory.groups.md) `G` is the
intersection of the kernels of the
[group homomorphisms](group-theory.homomorphisms-groups.md)

```text
  hom-element-Group G g : ℤ → G
```

indexed by all elements `g : G`. In other words, the exponent of `G` is the
[subgroup](group-theory.subgroups.md) `K` of `ℤ` consisting of all
[integers](elementary-number-theory.integers.md) `k` such that the
[integer power](group-theory.integer-powers-of-elements-groups.md) `gᵏ ＝ 1` for
every group element `g`.

Note that our conventions are slightly different from the conventions in
classical mathematics, where the exponent is taken to be the positive integer
`k` that
[generates the subgroup](group-theory.subgroups-generated-by-elements-groups.md)
of `ℤ` that we call the exponent of `G`. In constructive mathematics, however,
such an integer is not always well-defined.

## Definitions

### The exponent of a group

```agda
module _
  {l : Level} (G : Group l)
  where

  exponent-Group : Subgroup l ℤ-Group
  exponent-Group =
    intersection-family-of-subgroups-Group ℤ-Group
      ( λ (g : type-Group G) →
        subgroup-kernel-hom-Group ℤ-Group G (hom-element-Group G g))
```
