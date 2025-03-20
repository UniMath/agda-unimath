# The standard cyclic groups

```agda
open import foundation.function-extensionality-axiom

module
  elementary-number-theory.standard-cyclic-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.modular-arithmetic funext
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups funext
open import group-theory.groups funext
open import group-theory.semigroups funext
```

</details>

## Idea

The **standard cyclic groups** are the [groups](group-theory.groups.md) of
[integers](elementary-number-theory.integers.md)
[modulo `k`](elementary-number-theory.modular-arithmetic.md). The standard
cyclic groups are [abelian groups](group-theory.abelian-groups.md).

The fact that the standard cyclic groups are
[cyclic groups](group-theory.cyclic-groups.md) is shown in
[`elementary-number-theory.standard-cyclic-rings`](elementary-number-theory.standard-cyclic-rings.md).

## Definitions

### The semigroup `ℤ/k`

```agda
ℤ-Mod-Semigroup : (k : ℕ) → Semigroup lzero
pr1 (ℤ-Mod-Semigroup k) = ℤ-Mod-Set k
pr1 (pr2 (ℤ-Mod-Semigroup k)) = add-ℤ-Mod k
pr2 (pr2 (ℤ-Mod-Semigroup k)) = associative-add-ℤ-Mod k
```

### The group `ℤ/k`

```agda
ℤ-Mod-Group : (k : ℕ) → Group lzero
pr1 (ℤ-Mod-Group k) = ℤ-Mod-Semigroup k
pr1 (pr1 (pr2 (ℤ-Mod-Group k))) = zero-ℤ-Mod k
pr1 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = left-unit-law-add-ℤ-Mod k
pr2 (pr2 (pr1 (pr2 (ℤ-Mod-Group k)))) = right-unit-law-add-ℤ-Mod k
pr1 (pr2 (pr2 (ℤ-Mod-Group k))) = neg-ℤ-Mod k
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = left-inverse-law-add-ℤ-Mod k
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Group k)))) = right-inverse-law-add-ℤ-Mod k
```

### The abelian group `ℤ/k`

```agda
ℤ-Mod-Ab : (k : ℕ) → Ab lzero
pr1 (ℤ-Mod-Ab k) = ℤ-Mod-Group k
pr2 (ℤ-Mod-Ab k) = commutative-add-ℤ-Mod k
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
