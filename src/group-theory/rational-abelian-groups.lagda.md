# Rational abelian groups

```agda
module group-theory.rational-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.divisible-groups
open import group-theory.groups
open import group-theory.torsion-free-groups
open import group-theory.trivial-groups
open import group-theory.trivial-subgroups
```

</details>

## Idea

A group `G` is called **rational** when it is
[divisible](group-theory.divisible-groups.md) and
[torsion-free](group-theory.torsion-free-groups.md). Although this definition is
reasonable for nonabelian groups, it is of particular interest for abelian
groups: these turn out to be precisely the
[modules](linear-algebra.left-modules-rings.md) over the
[rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

## Definition

```agda
is-rational-Group : {l : Level} (G : Group l) → UU l
is-rational-Group G = is-divisible-Group G × is-torsion-free-Group G

is-rational-Ab : {l : Level} (A : Ab l) → UU l
is-rational-Ab A = is-rational-Group (group-Ab A)
```
