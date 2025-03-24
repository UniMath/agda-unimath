# The group of integers

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module elementary-number-theory.group-of-integers
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers funext univalence truncations
open import elementary-number-theory.equality-integers funext univalence truncations
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import group-theory.abelian-groups funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.semigroups funext univalence

open import structured-types.types-equipped-with-endomorphisms funext univalence
```

</details>

## Idea

The type of integers, equipped with a zero-element, addition, and negatives,
forms a group.

## Definition

```agda
ℤ-Type-With-Endomorphism : Type-With-Endomorphism lzero
pr1 ℤ-Type-With-Endomorphism = ℤ
pr2 ℤ-Type-With-Endomorphism = succ-ℤ

ℤ-Semigroup : Semigroup lzero
pr1 ℤ-Semigroup = ℤ-Set
pr1 (pr2 ℤ-Semigroup) = add-ℤ
pr2 (pr2 ℤ-Semigroup) = associative-add-ℤ

ℤ-Group : Group lzero
pr1 ℤ-Group = ℤ-Semigroup
pr1 (pr1 (pr2 ℤ-Group)) = zero-ℤ
pr1 (pr2 (pr1 (pr2 ℤ-Group))) = left-unit-law-add-ℤ
pr2 (pr2 (pr1 (pr2 ℤ-Group))) = right-unit-law-add-ℤ
pr1 (pr2 (pr2 ℤ-Group)) = neg-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Group))) = left-inverse-law-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Group))) = right-inverse-law-add-ℤ

ℤ-Ab : Ab lzero
pr1 ℤ-Ab = ℤ-Group
pr2 ℤ-Ab = commutative-add-ℤ
```
