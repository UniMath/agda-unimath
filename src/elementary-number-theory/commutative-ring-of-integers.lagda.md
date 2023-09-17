# The commutative ring of integers

```agda
module elementary-number-theory.commutative-ring-of-integers where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.free-groups-with-one-generator
open import group-theory.homomorphisms-groups

open import ring-theory.free-rings-with-one-generator
open import ring-theory.homomorphisms-rings
open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Definition

```agda
ℤ-Ab : Ab lzero
pr1 ℤ-Ab = ℤ-Group
pr2 ℤ-Ab = commutative-add-ℤ

ℤ-Ring : Ring lzero
pr1 ℤ-Ring = ℤ-Ab
pr1 (pr1 (pr2 ℤ-Ring)) = mul-ℤ
pr2 (pr1 (pr2 ℤ-Ring)) = associative-mul-ℤ
pr1 (pr1 (pr2 (pr2 ℤ-Ring))) = one-ℤ
pr1 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = left-unit-law-mul-ℤ
pr2 (pr2 (pr1 (pr2 (pr2 ℤ-Ring)))) = right-unit-law-mul-ℤ
pr1 (pr2 (pr2 (pr2 ℤ-Ring))) = left-distributive-mul-add-ℤ
pr2 (pr2 (pr2 (pr2 ℤ-Ring))) = right-distributive-mul-add-ℤ

ℤ-Commutative-Ring : Commutative-Ring lzero
pr1 ℤ-Commutative-Ring = ℤ-Ring
pr2 ℤ-Commutative-Ring = commutative-mul-ℤ
```

## Properties

### The ring of integers equipped with the integer `1` is the free ring with one generator

#### The homomorphism from `ℤ` to a ring equipped with an element

```agda
module _
  {l1 : Level} (R : Ring l1) (x : type-Ring R)
  where

  hom-group-hom-element-Ring : type-hom-Group ℤ-Group (group-Ring R)
  hom-group-hom-element-Ring =
    hom-element-Group (group-Ring R) x

  map-hom-element-Ring : ℤ → type-Ring R
  map-hom-element-Ring =
    map-hom-Group ℤ-Group (group-Ring R) hom-group-hom-element-Ring

  preserves-add-hom-element-Ring :
    (k l : ℤ) →
    map-hom-element-Ring (add-ℤ k l) ＝
    add-Ring R (map-hom-element-Ring k) (map-hom-element-Ring l)
  preserves-add-hom-element-Ring =
    preserves-mul-hom-Group ℤ-Group (group-Ring R) hom-group-hom-element-Ring

  hom-element-Ring : type-hom-Ring ℤ-Ring R
  hom-element-Ring = {!!}
```

#### The ring of integers equipped with the integer `1` is the free ring with one generator

```agda
is-free-ring-with-one-generator-ℤ-Ring :
  is-free-ring-with-one-generator ℤ-Ring one-ℤ
is-free-ring-with-one-generator-ℤ-Ring S = {!!}
```
