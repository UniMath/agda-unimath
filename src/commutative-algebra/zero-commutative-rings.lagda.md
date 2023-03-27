# Zero commutative rings

```agda
module commutative-algebra.zero-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import ring-theory.rings
open import ring-theory.zero-rings
```

</details>

## Idea

A zero commutative ring is a commutative ring that has `0 = 1`.
This implies that it only has one element.

## Definition

```agda
is-zero-commutative-ring-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-zero-commutative-ring-Commutative-Ring R =
  Id (zero-Commutative-Ring R) (one-Commutative-Ring R)

is-nonzero-commutative-ring-Commutative-Ring :
  {l : Level} → Commutative-Ring l → UU l
is-nonzero-commutative-ring-Commutative-Ring R =
  ¬ (is-zero-commutative-ring-Commutative-Ring R)
```

## Properties

### The carrier type of a zero commutative ring is contractible

```agda
is-contr-is-zero-commutative-ring-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) →
  is-zero-commutative-ring-Commutative-Ring R →
  is-contr (type-Commutative-Ring R)
is-contr-is-zero-commutative-ring-Commutative-Ring R p =
  is-contr-is-zero-ring-Ring (ring-Commutative-Ring R) p 
```
