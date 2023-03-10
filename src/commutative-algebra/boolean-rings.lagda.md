# Boolean rings

```agda
module commutative-algebra.boolean-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.idempotent-elements-rings
```

</details>

## Idea

A boolean ring is a commutative ring in wich every element is idempotent.

## Definition

```agda
is-boolean-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → UU l
is-boolean-Commutative-Ring R =
  (x : type-Commutative-Ring R) →
  is-idempotent-element-Ring (ring-Commutative-Ring R) x

Boolean-Ring : (l : Level) → UU (lsuc l)
Boolean-Ring l = Σ (Commutative-Ring l) is-boolean-Commutative-Ring

module _
  {l : Level} (R : Boolean-Ring l)
  where

  commutative-ring-Boolean-Ring : Commutative-Ring l
  commutative-ring-Boolean-Ring = pr1 R
```
