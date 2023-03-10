# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-extensionality
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

A subset of a ring is a subtype of the underlying type of a ring

## Definition

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = subtype l (type-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  type-subset-Ring : UU (l1 ⊔ l2)
  type-subset-Ring = type-subtype S

  inclusion-subset-Ring : type-subset-Ring → type-Ring R
  inclusion-subset-Ring = pr1
```
