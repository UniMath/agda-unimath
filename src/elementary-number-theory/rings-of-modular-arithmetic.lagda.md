# Rings of modular arithmetic

```agda
module elementary-number-theory.rings-of-modular-arithmetic where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.groups-of-modular-arithmetic
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.ring-of-integers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import ring-theory.cyclic-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
open import foundation.existential-quantification
open import group-theory.generating-elements-groups
open import foundation.surjective-maps
```

</details>

## Idea

The **standard cyclic rings** `ℤ/n` are the [rings](ring-theory.rings.md) of
[modular arithmetic](elementary-number-theory.modular-arithmetic.md).

The fact that the rings `ℤ/n` are [cyclic](ring-theory.cyclic-rings.md) remains
to be shown.

## Definitions

```agda
ℤ-Mod-Ring : ℕ → Ring lzero
pr1 (ℤ-Mod-Ring n) = ℤ-Mod-Ab n
pr1 (pr1 (pr2 (ℤ-Mod-Ring n))) = mul-ℤ-Mod n
pr2 (pr1 (pr2 (ℤ-Mod-Ring n))) = associative-mul-ℤ-Mod n
pr1 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n)))) = one-ℤ-Mod n
pr1 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = left-unit-law-mul-ℤ-Mod n
pr2 (pr2 (pr1 (pr2 (pr2 (ℤ-Mod-Ring n))))) = right-unit-law-mul-ℤ-Mod n
pr1 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = left-distributive-mul-add-ℤ-Mod n
pr2 (pr2 (pr2 (pr2 (ℤ-Mod-Ring n)))) = right-distributive-mul-add-ℤ-Mod n

ℤ-Mod-Commutative-Ring : ℕ → Commutative-Ring lzero
pr1 (ℤ-Mod-Commutative-Ring n) = ℤ-Mod-Ring n
pr2 (ℤ-Mod-Commutative-Ring n) = commutative-mul-ℤ-Mod n
```

## Properties

### Rings of modular arithmetic are cyclic

**Proof:**

```agda
compute-integer-multiple-one-ℤ-Mod :
  ( n : ℕ) →
  ( λ k → integer-multiple-Ring (ℤ-Mod-Ring n) k (one-ℤ-Mod n)) ~
  ( mod-ℤ n)
compute-integer-multiple-one-ℤ-Mod = {!   !}

is-surjective-hom-element-one-ℤ-Mod-Ring :
  (n : ℕ) → is-surjective-hom-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-surjective-hom-element-one-ℤ-Mod-Ring n = is-surjective-htpy (compute-integer-multiple-one-ℤ-Mod n) (is-surjective-mod-ℤ n)

is-generating-element-one-ℤ-Mod-Ring :
  (n : ℕ) → is-generating-element-Group (ℤ-Mod-Group n) (one-ℤ-Mod n)
is-generating-element-one-ℤ-Mod-Ring n =
  is-generating-element-is-surjective-hom-element-Group
    ( ℤ-Mod-Group n)
    ( one-ℤ-Mod n)
    ( is-surjective-hom-element-one-ℤ-Mod-Ring n)

is-cyclic-ℤ-Mod-Ring :
  (n : ℕ) → is-cyclic-Ring (ℤ-Mod-Ring n)
is-cyclic-ℤ-Mod-Ring n =
  intro-∃
    ( one-ℤ-Mod n)
    ( is-generating-element-one-ℤ-Mod-Ring n)
```
