# Exponents of abelian groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.exponents-abelian-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.group-of-integers funext

open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.exponents-groups funext
open import group-theory.subgroups-abelian-groups funext
```

</details>

The **exponent** `exp A` of an [abelian group](group-theory.abelian-groups.md)
`A` is the intersection of the kernels of the
[group homomorphisms](group-theory.homomorphisms-groups.md)

```text
  hom-element-Group (group-Ab A) a : ℤ → A
```

indexed by all elements `a : A`. In other words, the exponent of `A` is the
[subgroup](group-theory.subgroups.md) `K` of `ℤ` consisting of all
[integers](elementary-number-theory.integers.md) `k` such that the
[integer multiple](group-theory.integer-multiples-of-elements-abelian-groups.md)
`kx ＝ 1` for every group element `x`.

Note that our conventions are slightly different from the conventions in
classical mathematics, where the exponent is taken to be the positive integer
`k` that
[generates the subgroup](group-theory.subgroups-generated-by-elements-groups.md)
of `ℤ` that we call the exponent of `A`. In constructive mathematics, however,
such an integer is not always well-defined.

## Definitions

### The exponent of an abelian group

```agda
module _
  {l : Level} (A : Ab l)
  where

  exponent-Ab : Subgroup-Ab l ℤ-Ab
  exponent-Ab = exponent-Group (group-Ab A)
```
