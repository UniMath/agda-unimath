# The commutative rings of modular arithmetic

```agda
module elementary-number-theory.commutative-rings-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.groups-of-modular-arithmetic
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

The integers modulo `n` form a
[commutative ring](commutative-algebra.commutative-rings.md).

## Definition

```agda
ℤ-Mod-Ring : (n : ℕ) → Ring lzero
pr1 (ℤ-Mod-Ring n) = ℤ-Mod-Ab n
pr1 (pr1 (pr2 (ℤ-Mod-Ring n))) = mul-ℤ-Mod n
pr2 (pr1 (pr2 (ℤ-Mod-Ring n))) = associative-mul-ℤ-Mod n
pr1 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n)))) = one-ℤ-Mod n
pr1 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = left-unit-law-mul-ℤ-Mod n
pr2 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = right-unit-law-mul-ℤ-Mod n
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = left-distributive-mul-add-ℤ-Mod n
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = right-distributive-mul-add-ℤ-Mod n

ℤ-Mod-Commutative-Ring : (n : ℕ) → Commutative-Ring lzero
pr1 (ℤ-Mod-Commutative-Ring n) = ℤ-Mod-Ring n
pr2 (ℤ-Mod-Commutative-Ring n) = commutative-mul-ℤ-Mod n
```
