# Zero rings

```agda
module ring-theory.zero-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equational-reasoning
open import foundation.identity-types
open import foundation.negation
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

A zero ring is a ring that has `0 = 1`. This implies that it only has one
element.

## Definition

```agda
is-zero-ring-Ring : {l : Level} → Ring l → UU l
is-zero-ring-Ring R = Id (zero-Ring R) (one-Ring R)

is-nonzero-ring-Ring : {l : Level} → Ring l → UU l
is-nonzero-ring-Ring R = ¬ (is-zero-ring-Ring R)
```

## Properties

### The carrier type of a zero ring is contractible

```agda
is-contr-is-zero-ring-Ring :
  {l : Level} (R : Ring l) →
  is-zero-ring-Ring R →
  is-contr (type-Ring R)
pr1 (is-contr-is-zero-ring-Ring R p) = zero-Ring R
pr2 (is-contr-is-zero-ring-Ring R p) x =
  equational-reasoning
    zero-Ring R
      ＝ mul-Ring R (zero-Ring R) x
        by inv (left-zero-law-mul-Ring R x)
      ＝ mul-Ring R (one-Ring R) x
        by ap-binary (mul-Ring R) p refl
      ＝ x
        by left-unit-law-mul-Ring R x
```
