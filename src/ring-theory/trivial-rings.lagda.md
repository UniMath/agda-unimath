# Trivial rings

```agda
module ring-theory.trivial-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

{{#concept "Trivial rings" WD="trivial ring" WDID=Q1652969 Agda=is-trivial-Ring}}
are [rings](ring-theory.rings.md) in which `0 = 1`.

## Definition

```agda
is-trivial-ring-Prop : {l : Level} → Ring l → Prop l
is-trivial-ring-Prop R =
  Id-Prop (set-Ring R) (zero-Ring R) (one-Ring R)

is-trivial-Ring : {l : Level} → Ring l → UU l
is-trivial-Ring R = type-Prop (is-trivial-ring-Prop R)

is-prop-is-trivial-Ring :
  {l : Level} (R : Ring l) → is-prop (is-trivial-Ring R)
is-prop-is-trivial-Ring R = is-prop-type-Prop (is-trivial-ring-Prop R)
```

## Properties

### The carrier type of a trivial ring is contractible

```agda
is-contr-is-trivial-Ring :
  {l : Level} (R : Ring l) →
  is-trivial-Ring R →
  is-contr (type-Ring R)
pr1 (is-contr-is-trivial-Ring R p) = zero-Ring R
pr2 (is-contr-is-trivial-Ring R p) x =
  equational-reasoning
    zero-Ring R
      ＝ mul-Ring R (zero-Ring R) x
        by inv (left-zero-law-mul-Ring R x)
      ＝ mul-Ring R (one-Ring R) x
        by ap-binary (mul-Ring R) p refl
      ＝ x
        by left-unit-law-mul-Ring R x
```
