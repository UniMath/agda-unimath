# The abstract quaternion group of order 8

```agda
module finite-group-theory.abstract-quaternion-group where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.semigroups

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The abstract quaternion group of order 8 is the group of the quaternions `1`, `-1`, `i`, `-i`, `j`, `-j`, `k`, and `-k`.

## Definition

```agda
data Q8 : UU lzero where
  e-Q8  : Q8
  -e-Q8 : Q8
  i-Q8  : Q8
  -i-Q8 : Q8
  j-Q8  : Q8
  -j-Q8 : Q8
  k-Q8  : Q8
  -k-Q8 : Q8

mul-Q8 : Q8 → Q8 → Q8
mul-Q8 e-Q8 e-Q8 = e-Q8
mul-Q8 e-Q8 -e-Q8 = -e-Q8
mul-Q8 e-Q8 i-Q8 = i-Q8
mul-Q8 e-Q8 -i-Q8 = -i-Q8
mul-Q8 e-Q8 j-Q8 = j-Q8
mul-Q8 e-Q8 -j-Q8 = -j-Q8
mul-Q8 e-Q8 k-Q8 = k-Q8
mul-Q8 e-Q8 -k-Q8 = -k-Q8
mul-Q8 -e-Q8 e-Q8 = -e-Q8
mul-Q8 -e-Q8 -e-Q8 = e-Q8
mul-Q8 -e-Q8 i-Q8 = -i-Q8
mul-Q8 -e-Q8 -i-Q8 = i-Q8
mul-Q8 -e-Q8 j-Q8 = -j-Q8
mul-Q8 -e-Q8 -j-Q8 = j-Q8
mul-Q8 -e-Q8 k-Q8 = -k-Q8
mul-Q8 -e-Q8 -k-Q8 = k-Q8
mul-Q8 i-Q8 e-Q8 = i-Q8
mul-Q8 i-Q8 -e-Q8 = -i-Q8
mul-Q8 i-Q8 i-Q8 = -e-Q8
mul-Q8 i-Q8 -i-Q8 = e-Q8
mul-Q8 i-Q8 j-Q8 = k-Q8
mul-Q8 i-Q8 -j-Q8 = -k-Q8
mul-Q8 i-Q8 k-Q8 = -j-Q8
mul-Q8 i-Q8 -k-Q8 = j-Q8
mul-Q8 -i-Q8 e-Q8 = -i-Q8
mul-Q8 -i-Q8 -e-Q8 = i-Q8
mul-Q8 -i-Q8 i-Q8 = e-Q8
mul-Q8 -i-Q8 -i-Q8 = -e-Q8
mul-Q8 -i-Q8 j-Q8 = -k-Q8
mul-Q8 -i-Q8 -j-Q8 = k-Q8
mul-Q8 -i-Q8 k-Q8 = j-Q8
mul-Q8 -i-Q8 -k-Q8 = -j-Q8
mul-Q8 j-Q8 e-Q8 = j-Q8
mul-Q8 j-Q8 -e-Q8 = -j-Q8
mul-Q8 j-Q8 i-Q8 = -k-Q8
mul-Q8 j-Q8 -i-Q8 = k-Q8
mul-Q8 j-Q8 j-Q8 = -e-Q8
mul-Q8 j-Q8 -j-Q8 = e-Q8
mul-Q8 j-Q8 k-Q8 = i-Q8
mul-Q8 j-Q8 -k-Q8 = -i-Q8
mul-Q8 -j-Q8 e-Q8 = -j-Q8
mul-Q8 -j-Q8 -e-Q8 = j-Q8
mul-Q8 -j-Q8 i-Q8 = k-Q8
mul-Q8 -j-Q8 -i-Q8 = -k-Q8
mul-Q8 -j-Q8 j-Q8 = e-Q8
mul-Q8 -j-Q8 -j-Q8 = -e-Q8
mul-Q8 -j-Q8 k-Q8 = -i-Q8
mul-Q8 -j-Q8 -k-Q8 = i-Q8
mul-Q8 k-Q8 e-Q8 = k-Q8
mul-Q8 k-Q8 -e-Q8 = -k-Q8
mul-Q8 k-Q8 i-Q8 = j-Q8
mul-Q8 k-Q8 -i-Q8 = -j-Q8
mul-Q8 k-Q8 j-Q8 = -i-Q8
mul-Q8 k-Q8 -j-Q8 = i-Q8
mul-Q8 k-Q8 k-Q8 = -e-Q8
mul-Q8 k-Q8 -k-Q8 = e-Q8
mul-Q8 -k-Q8 e-Q8 = -k-Q8
mul-Q8 -k-Q8 -e-Q8 = k-Q8
mul-Q8 -k-Q8 i-Q8 = -j-Q8
mul-Q8 -k-Q8 -i-Q8 = j-Q8
mul-Q8 -k-Q8 j-Q8 = i-Q8
mul-Q8 -k-Q8 -j-Q8 = -i-Q8
mul-Q8 -k-Q8 k-Q8 = e-Q8
mul-Q8 -k-Q8 -k-Q8 = -e-Q8

inv-Q8 : Q8 → Q8
inv-Q8 e-Q8 = e-Q8
inv-Q8 -e-Q8 = -e-Q8
inv-Q8 i-Q8 = -i-Q8
inv-Q8 -i-Q8 = i-Q8
inv-Q8 j-Q8 = -j-Q8
inv-Q8 -j-Q8 = j-Q8
inv-Q8 k-Q8 = -k-Q8
inv-Q8 -k-Q8 = k-Q8

left-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 e-Q8 x) x
left-unit-law-mul-Q8 e-Q8 = refl
left-unit-law-mul-Q8 -e-Q8 = refl
left-unit-law-mul-Q8 i-Q8 = refl
left-unit-law-mul-Q8 -i-Q8 = refl
left-unit-law-mul-Q8 j-Q8 = refl
left-unit-law-mul-Q8 -j-Q8 = refl
left-unit-law-mul-Q8 k-Q8 = refl
left-unit-law-mul-Q8 -k-Q8 = refl

right-unit-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x e-Q8) x
right-unit-law-mul-Q8 e-Q8 = refl
right-unit-law-mul-Q8 -e-Q8 = refl
right-unit-law-mul-Q8 i-Q8 = refl
right-unit-law-mul-Q8 -i-Q8 = refl
right-unit-law-mul-Q8 j-Q8 = refl
right-unit-law-mul-Q8 -j-Q8 = refl
right-unit-law-mul-Q8 k-Q8 = refl
right-unit-law-mul-Q8 -k-Q8 = refl

associative-mul-Q8 :
  (x y z : Q8) → Id (mul-Q8 (mul-Q8 x y) z) (mul-Q8 x (mul-Q8 y z))
associative-mul-Q8 e-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 e-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -e-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 i-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -i-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 j-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -j-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 k-Q8 -k-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 e-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -e-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 i-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -i-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 j-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -j-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 k-Q8 -k-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 e-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -e-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 i-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -i-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 j-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -j-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 k-Q8 = refl
associative-mul-Q8 -k-Q8 -k-Q8 -k-Q8 = refl

left-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 (inv-Q8 x) x) e-Q8
left-inverse-law-mul-Q8 e-Q8 = refl
left-inverse-law-mul-Q8 -e-Q8 = refl
left-inverse-law-mul-Q8 i-Q8 = refl
left-inverse-law-mul-Q8 -i-Q8 = refl
left-inverse-law-mul-Q8 j-Q8 = refl
left-inverse-law-mul-Q8 -j-Q8 = refl
left-inverse-law-mul-Q8 k-Q8 = refl
left-inverse-law-mul-Q8 -k-Q8 = refl

right-inverse-law-mul-Q8 : (x : Q8) → Id (mul-Q8 x (inv-Q8 x)) e-Q8
right-inverse-law-mul-Q8 e-Q8 = refl
right-inverse-law-mul-Q8 -e-Q8 = refl
right-inverse-law-mul-Q8 i-Q8 = refl
right-inverse-law-mul-Q8 -i-Q8 = refl
right-inverse-law-mul-Q8 j-Q8 = refl
right-inverse-law-mul-Q8 -j-Q8 = refl
right-inverse-law-mul-Q8 k-Q8 = refl
right-inverse-law-mul-Q8 -k-Q8 = refl

Eq-Q8 : Q8 → Q8 → UU lzero
Eq-Q8 e-Q8 e-Q8 = unit
Eq-Q8 e-Q8 -e-Q8 = empty
Eq-Q8 e-Q8 i-Q8 = empty
Eq-Q8 e-Q8 -i-Q8 = empty
Eq-Q8 e-Q8 j-Q8 = empty
Eq-Q8 e-Q8 -j-Q8 = empty
Eq-Q8 e-Q8 k-Q8 = empty
Eq-Q8 e-Q8 -k-Q8 = empty
Eq-Q8 -e-Q8 e-Q8 = empty
Eq-Q8 -e-Q8 -e-Q8 = unit
Eq-Q8 -e-Q8 i-Q8 = empty
Eq-Q8 -e-Q8 -i-Q8 = empty
Eq-Q8 -e-Q8 j-Q8 = empty
Eq-Q8 -e-Q8 -j-Q8 = empty
Eq-Q8 -e-Q8 k-Q8 = empty
Eq-Q8 -e-Q8 -k-Q8 = empty
Eq-Q8 i-Q8 e-Q8 = empty
Eq-Q8 i-Q8 -e-Q8 = empty
Eq-Q8 i-Q8 i-Q8 = unit
Eq-Q8 i-Q8 -i-Q8 = empty
Eq-Q8 i-Q8 j-Q8 = empty
Eq-Q8 i-Q8 -j-Q8 = empty
Eq-Q8 i-Q8 k-Q8 = empty
Eq-Q8 i-Q8 -k-Q8 = empty
Eq-Q8 -i-Q8 e-Q8 = empty
Eq-Q8 -i-Q8 -e-Q8 = empty
Eq-Q8 -i-Q8 i-Q8 = empty
Eq-Q8 -i-Q8 -i-Q8 = unit
Eq-Q8 -i-Q8 j-Q8 = empty
Eq-Q8 -i-Q8 -j-Q8 = empty
Eq-Q8 -i-Q8 k-Q8 = empty
Eq-Q8 -i-Q8 -k-Q8 = empty
Eq-Q8 j-Q8 e-Q8 = empty
Eq-Q8 j-Q8 -e-Q8 = empty
Eq-Q8 j-Q8 i-Q8 = empty
Eq-Q8 j-Q8 -i-Q8 = empty
Eq-Q8 j-Q8 j-Q8 = unit
Eq-Q8 j-Q8 -j-Q8 = empty
Eq-Q8 j-Q8 k-Q8 = empty
Eq-Q8 j-Q8 -k-Q8 = empty
Eq-Q8 -j-Q8 e-Q8 = empty
Eq-Q8 -j-Q8 -e-Q8 = empty
Eq-Q8 -j-Q8 i-Q8 = empty
Eq-Q8 -j-Q8 -i-Q8 = empty
Eq-Q8 -j-Q8 j-Q8 = empty
Eq-Q8 -j-Q8 -j-Q8 = unit
Eq-Q8 -j-Q8 k-Q8 = empty
Eq-Q8 -j-Q8 -k-Q8 = empty
Eq-Q8 k-Q8 e-Q8 = empty
Eq-Q8 k-Q8 -e-Q8 = empty
Eq-Q8 k-Q8 i-Q8 = empty
Eq-Q8 k-Q8 -i-Q8 = empty
Eq-Q8 k-Q8 j-Q8 = empty
Eq-Q8 k-Q8 -j-Q8 = empty
Eq-Q8 k-Q8 k-Q8 = unit
Eq-Q8 k-Q8 -k-Q8 = empty
Eq-Q8 -k-Q8 e-Q8 = empty
Eq-Q8 -k-Q8 -e-Q8 = empty
Eq-Q8 -k-Q8 i-Q8 = empty
Eq-Q8 -k-Q8 -i-Q8 = empty
Eq-Q8 -k-Q8 j-Q8 = empty
Eq-Q8 -k-Q8 -j-Q8 = empty
Eq-Q8 -k-Q8 k-Q8 = empty
Eq-Q8 -k-Q8 -k-Q8 = unit

refl-Eq-Q8 : (x : Q8) → Eq-Q8 x x
refl-Eq-Q8 e-Q8 = star
refl-Eq-Q8 -e-Q8 = star
refl-Eq-Q8 i-Q8 = star
refl-Eq-Q8 -i-Q8 = star
refl-Eq-Q8 j-Q8 = star
refl-Eq-Q8 -j-Q8 = star
refl-Eq-Q8 k-Q8 = star
refl-Eq-Q8 -k-Q8 = star

Eq-eq-Q8 : {x y : Q8} → Id x y → Eq-Q8 x y
Eq-eq-Q8 {x} refl = refl-Eq-Q8 x

eq-Eq-Q8 : (x y : Q8) → Eq-Q8 x y → Id x y
eq-Eq-Q8 e-Q8 e-Q8 e = refl
eq-Eq-Q8 -e-Q8 -e-Q8 e = refl
eq-Eq-Q8 i-Q8 i-Q8 e = refl
eq-Eq-Q8 -i-Q8 -i-Q8 e = refl
eq-Eq-Q8 j-Q8 j-Q8 e = refl
eq-Eq-Q8 -j-Q8 -j-Q8 e = refl
eq-Eq-Q8 k-Q8 k-Q8 e = refl
eq-Eq-Q8 -k-Q8 -k-Q8 e = refl

is-decidable-Eq-Q8 : (x y : Q8) → is-decidable (Eq-Q8 x y)
is-decidable-Eq-Q8 e-Q8 e-Q8 = is-decidable-unit
is-decidable-Eq-Q8 e-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 e-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -e-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -e-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -e-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 i-Q8 = is-decidable-unit
is-decidable-Eq-Q8 i-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 i-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -i-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -i-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -i-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 j-Q8 = is-decidable-unit
is-decidable-Eq-Q8 j-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 j-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -j-Q8 = is-decidable-unit
is-decidable-Eq-Q8 -j-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -j-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 k-Q8 k-Q8 = is-decidable-unit
is-decidable-Eq-Q8 k-Q8 -k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -e-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -i-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -j-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 k-Q8 = is-decidable-empty
is-decidable-Eq-Q8 -k-Q8 -k-Q8 = is-decidable-unit

has-decidable-equality-Q8 : has-decidable-equality Q8
has-decidable-equality-Q8 x y =
  is-decidable-iff
    ( eq-Eq-Q8 x y)
    ( Eq-eq-Q8)
    ( is-decidable-Eq-Q8 x y)

is-set-Q8 : is-set Q8
is-set-Q8 = is-set-has-decidable-equality has-decidable-equality-Q8

Q8-Set : Set lzero
Q8-Set = pair Q8 is-set-Q8

Q8-Semigroup : Semigroup lzero
Q8-Semigroup = pair Q8-Set (pair mul-Q8 associative-mul-Q8)

Q8-Group : Group lzero
Q8-Group =
  pair
    Q8-Semigroup
    ( pair
      ( pair e-Q8
        ( pair left-unit-law-mul-Q8 right-unit-law-mul-Q8))
      ( pair inv-Q8 (pair left-inverse-law-mul-Q8 right-inverse-law-mul-Q8)))

is-noncommutative-mul-Q8 :
  ¬ ((x y : Q8) → Id (mul-Q8 x y) (mul-Q8 y x))
is-noncommutative-mul-Q8 f = Eq-eq-Q8 (f i-Q8 j-Q8)

map-equiv-count-Q8 : Fin 8 → Q8
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inl (inl (inr star)))))))) = e-Q8
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inl (inr star))))))) = -e-Q8
map-equiv-count-Q8 (inl (inl (inl (inl (inl (inr star)))))) = i-Q8
map-equiv-count-Q8 (inl (inl (inl (inl (inr star))))) = -i-Q8
map-equiv-count-Q8 (inl (inl (inl (inr star)))) = j-Q8
map-equiv-count-Q8 (inl (inl (inr star))) = -j-Q8
map-equiv-count-Q8 (inl (inr star)) = k-Q8
map-equiv-count-Q8 (inr star) = -k-Q8

map-inv-equiv-count-Q8 : Q8 → Fin 8
map-inv-equiv-count-Q8 e-Q8 = inl (inl (inl (inl (inl (inl (inl (inr star)))))))
map-inv-equiv-count-Q8 -e-Q8 = inl (inl (inl (inl (inl (inl (inr star))))))
map-inv-equiv-count-Q8 i-Q8 = inl (inl (inl (inl (inl (inr star)))))
map-inv-equiv-count-Q8 -i-Q8 = inl (inl (inl (inl (inr star))))
map-inv-equiv-count-Q8 j-Q8 = inl (inl (inl (inr star)))
map-inv-equiv-count-Q8 -j-Q8 = inl (inl (inr star))
map-inv-equiv-count-Q8 k-Q8 = inl (inr star)
map-inv-equiv-count-Q8 -k-Q8 = inr star

issec-map-inv-equiv-count-Q8 :
  ( map-equiv-count-Q8 ∘ map-inv-equiv-count-Q8) ~ id
issec-map-inv-equiv-count-Q8 e-Q8 = refl
issec-map-inv-equiv-count-Q8 -e-Q8 = refl
issec-map-inv-equiv-count-Q8 i-Q8 = refl
issec-map-inv-equiv-count-Q8 -i-Q8 = refl
issec-map-inv-equiv-count-Q8 j-Q8 = refl
issec-map-inv-equiv-count-Q8 -j-Q8 = refl
issec-map-inv-equiv-count-Q8 k-Q8 = refl
issec-map-inv-equiv-count-Q8 -k-Q8 = refl

isretr-map-inv-equiv-count-Q8 :
  ( map-inv-equiv-count-Q8 ∘ map-equiv-count-Q8) ~ id
isretr-map-inv-equiv-count-Q8
  (inl (inl (inl (inl (inl (inl (inl (inr star)))))))) = refl
isretr-map-inv-equiv-count-Q8
  (inl (inl (inl (inl (inl (inl (inr star))))))) = refl
isretr-map-inv-equiv-count-Q8 (inl (inl (inl (inl (inl (inr star)))))) = refl
isretr-map-inv-equiv-count-Q8 (inl (inl (inl (inl (inr star))))) = refl
isretr-map-inv-equiv-count-Q8 (inl (inl (inl (inr star)))) = refl
isretr-map-inv-equiv-count-Q8 (inl (inl (inr star))) = refl
isretr-map-inv-equiv-count-Q8 (inl (inr star)) = refl
isretr-map-inv-equiv-count-Q8 (inr star) = refl

is-equiv-map-equiv-count-Q8 : is-equiv map-equiv-count-Q8
is-equiv-map-equiv-count-Q8 =
  is-equiv-has-inverse
    map-inv-equiv-count-Q8
    issec-map-inv-equiv-count-Q8
    isretr-map-inv-equiv-count-Q8

equiv-count-Q8 : Fin 8 ≃ Q8
equiv-count-Q8 = pair map-equiv-count-Q8 is-equiv-map-equiv-count-Q8

count-Q8 : count Q8
count-Q8 = pair 8 equiv-count-Q8

is-finite-Q8 : is-finite Q8
is-finite-Q8 = unit-trunc-Prop count-Q8

Q8-𝔽 : 𝔽 lzero
Q8-𝔽 = pair Q8 is-finite-Q8

has-cardinality-eight-Q8 : has-cardinality 8 Q8
has-cardinality-eight-Q8 = unit-trunc-Prop equiv-count-Q8

Q8-UU-Fin-8 : UU-Fin lzero 8
Q8-UU-Fin-8 = pair Q8 has-cardinality-eight-Q8

has-finite-cardinality-Q8 : has-finite-cardinality Q8
has-finite-cardinality-Q8 = pair 8 has-cardinality-eight-Q8
```
