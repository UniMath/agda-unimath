# Opposite rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.opposite-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.universe-levels

open import ring-theory.rings funext univalence truncations
```

</details>

## Idea

The opposite of a ring R is a ring with the same underlying abelian group, but
with multiplication given by `x·y := yx`.

## Definition

```agda
module _
  {l : Level} (R : Ring l)
  where

  op-Ring : Ring l
  pr1 op-Ring = ab-Ring R
  pr1 (pr1 (pr2 op-Ring)) = mul-Ring' R
  pr2 (pr1 (pr2 op-Ring)) x y z = inv (associative-mul-Ring R z y x)
  pr1 (pr1 (pr2 (pr2 op-Ring))) = one-Ring R
  pr1 (pr2 (pr1 (pr2 (pr2 op-Ring)))) = right-unit-law-mul-Ring R
  pr2 (pr2 (pr1 (pr2 (pr2 op-Ring)))) = left-unit-law-mul-Ring R
  pr1 (pr2 (pr2 (pr2 op-Ring))) x y z = right-distributive-mul-add-Ring R y z x
  pr2 (pr2 (pr2 (pr2 op-Ring))) x y z = left-distributive-mul-add-Ring R z x y
```
