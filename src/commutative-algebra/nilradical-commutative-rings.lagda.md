# Nilradical of a commutative ring

```agda
module commutative-algebra.nilradical-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings

open import foundation.universe-levels

open import ring-theory.nilpotent-elements-rings
```

</details>

## Idea

The nilradical of a commutative ring is the ideal consisting of all nilpotent elements.

## Definitions

```agda
subset-nilradical-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → subset-Commutative-Ring l R
subset-nilradical-Commutative-Ring R = is-nilpotent-element-ring-Prop (ring-Commutative-Ring R)
```

## Properties

### The nilradical is the intersection of all prime ideals
