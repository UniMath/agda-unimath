# Full ideals of commutative rings

```agda
module commutative-algebra.full-ideals-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.ideals-commutative-rings
open import commutative-algebra.poset-of-ideals-commutative-rings
open import commutative-algebra.poset-of-radical-ideals-commutative-rings
open import commutative-algebra.radical-ideals-commutative-rings
open import commutative-algebra.subsets-commutative-rings

open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.top-elements-large-posets

open import ring-theory.full-ideals-rings
```

</details>

## Idea

A **full ideal** in a
[commutative ring](commutative-algebra.commutative-rings.md) `A` is an
[ideal](commutative-algebra.ideals-commutative-rings.md) that contains every
element of `A`.

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 A)
  where

  is-full-ideal-Commutative-Ring-Prop : Prop (l1 ⊔ l2)
  is-full-ideal-Commutative-Ring-Prop =
    is-full-ideal-Ring-Prop (ring-Commutative-Ring A) I

  is-full-ideal-Commutative-Ring : UU (l1 ⊔ l2)
  is-full-ideal-Commutative-Ring =
    is-full-ideal-Ring (ring-Commutative-Ring A) I

  is-prop-is-full-ideal-Commutative-Ring :
    is-prop is-full-ideal-Commutative-Ring
  is-prop-is-full-ideal-Commutative-Ring =
    is-prop-is-full-ideal-Ring (ring-Commutative-Ring A) I
```

### The (standard) full ideal

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  subset-full-ideal-Commutative-Ring : subset-Commutative-Ring lzero A
  subset-full-ideal-Commutative-Ring =
    subset-full-ideal-Ring (ring-Commutative-Ring A)

  is-in-full-ideal-Commutative-Ring : type-Commutative-Ring A → UU lzero
  is-in-full-ideal-Commutative-Ring =
    is-in-full-ideal-Ring (ring-Commutative-Ring A)

  contains-zero-full-ideal-Commutative-Ring :
    contains-zero-subset-Commutative-Ring A subset-full-ideal-Commutative-Ring
  contains-zero-full-ideal-Commutative-Ring =
    contains-zero-full-ideal-Ring (ring-Commutative-Ring A)

  is-closed-under-addition-full-ideal-Commutative-Ring :
    is-closed-under-addition-subset-Commutative-Ring A
      subset-full-ideal-Commutative-Ring
  is-closed-under-addition-full-ideal-Commutative-Ring =
    is-closed-under-addition-full-ideal-Ring (ring-Commutative-Ring A)

  is-closed-under-negatives-full-ideal-Commutative-Ring :
    is-closed-under-negatives-subset-Commutative-Ring A
      subset-full-ideal-Commutative-Ring
  is-closed-under-negatives-full-ideal-Commutative-Ring =
    is-closed-under-negatives-full-ideal-Ring (ring-Commutative-Ring A)

  is-additive-subgroup-full-ideal-Commutative-Ring :
    is-additive-subgroup-subset-Commutative-Ring A
      subset-full-ideal-Commutative-Ring
  is-additive-subgroup-full-ideal-Commutative-Ring =
    is-additive-subgroup-full-ideal-Ring (ring-Commutative-Ring A)

  is-closed-under-left-multiplication-full-ideal-Commutative-Ring :
    is-closed-under-left-multiplication-subset-Commutative-Ring A
      subset-full-ideal-Commutative-Ring
  is-closed-under-left-multiplication-full-ideal-Commutative-Ring =
    is-closed-under-left-multiplication-full-ideal-Ring
      ( ring-Commutative-Ring A)

  is-closed-under-right-multiplication-full-ideal-Commutative-Ring :
    is-closed-under-right-multiplication-subset-Commutative-Ring A
      subset-full-ideal-Commutative-Ring
  is-closed-under-right-multiplication-full-ideal-Commutative-Ring =
    is-closed-under-right-multiplication-full-ideal-Ring
      ( ring-Commutative-Ring A)

  is-left-ideal-full-ideal-Commutative-Ring :
    is-left-ideal-subset-Commutative-Ring A subset-full-ideal-Commutative-Ring
  is-left-ideal-full-ideal-Commutative-Ring =
    is-left-ideal-full-ideal-Ring (ring-Commutative-Ring A)

  full-left-ideal-Commutative-Ring : left-ideal-Commutative-Ring lzero A
  full-left-ideal-Commutative-Ring =
    full-left-ideal-Ring (ring-Commutative-Ring A)

  is-right-ideal-full-ideal-Commutative-Ring :
    is-right-ideal-subset-Commutative-Ring A subset-full-ideal-Commutative-Ring
  is-right-ideal-full-ideal-Commutative-Ring =
    is-right-ideal-full-ideal-Ring (ring-Commutative-Ring A)

  full-right-ideal-Commutative-Ring : right-ideal-Commutative-Ring lzero A
  full-right-ideal-Commutative-Ring =
    full-right-ideal-Ring (ring-Commutative-Ring A)

  is-ideal-full-ideal-Commutative-Ring :
    is-ideal-subset-Commutative-Ring A subset-full-ideal-Commutative-Ring
  is-ideal-full-ideal-Commutative-Ring =
    is-ideal-full-ideal-Ring (ring-Commutative-Ring A)

  full-ideal-Commutative-Ring : ideal-Commutative-Ring lzero A
  full-ideal-Commutative-Ring = full-ideal-Ring (ring-Commutative-Ring A)

  is-full-full-ideal-Commutative-Ring :
    is-full-ideal-Commutative-Ring A full-ideal-Commutative-Ring
  is-full-full-ideal-Commutative-Ring =
    is-full-full-ideal-Ring (ring-Commutative-Ring A)
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 A)
  where

  is-full-contains-one-ideal-Commutative-Ring :
    is-in-ideal-Commutative-Ring A I (one-Commutative-Ring A) →
    is-full-ideal-Commutative-Ring A I
  is-full-contains-one-ideal-Commutative-Ring =
    is-full-contains-one-ideal-Ring (ring-Commutative-Ring A) I

  contains-one-is-full-ideal-Commutative-Ring :
    is-full-ideal-Commutative-Ring A I →
    is-in-ideal-Commutative-Ring A I (one-Commutative-Ring A)
  contains-one-is-full-ideal-Commutative-Ring =
    contains-one-is-full-ideal-Ring (ring-Commutative-Ring A) I
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (I : ideal-Commutative-Ring l2 A)
  where

  is-full-is-top-element-ideal-Commutative-Ring :
    is-top-element-Large-Poset (ideal-Commutative-Ring-Large-Poset A) I →
    is-full-ideal-Commutative-Ring A I
  is-full-is-top-element-ideal-Commutative-Ring =
    is-full-is-top-element-ideal-Ring (ring-Commutative-Ring A) I

  is-top-element-is-full-ideal-Commutative-Ring :
    is-full-ideal-Commutative-Ring A I →
    is-top-element-Large-Poset (ideal-Commutative-Ring-Large-Poset A) I
  is-top-element-is-full-ideal-Commutative-Ring =
    is-top-element-is-full-ideal-Ring (ring-Commutative-Ring A) I

module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  is-top-element-full-ideal-Commutative-Ring :
    is-top-element-Large-Poset
      ( ideal-Commutative-Ring-Large-Poset A)
      ( full-ideal-Commutative-Ring A)
  is-top-element-full-ideal-Commutative-Ring =
    is-top-element-full-ideal-Ring (ring-Commutative-Ring A)

  has-top-element-ideal-Commutative-Ring :
    has-top-element-Large-Poset (ideal-Commutative-Ring-Large-Poset A)
  has-top-element-ideal-Commutative-Ring =
    has-top-element-ideal-Ring (ring-Commutative-Ring A)
```

### The full ideal of a commutative ring is radical

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  is-radical-full-ideal-Commutative-Ring :
    is-radical-ideal-Commutative-Ring A (full-ideal-Commutative-Ring A)
  is-radical-full-ideal-Commutative-Ring x n H = raise-star

  full-radical-ideal-Commutative-Ring : radical-ideal-Commutative-Ring lzero A
  pr1 full-radical-ideal-Commutative-Ring =
    full-ideal-Commutative-Ring A
  pr2 full-radical-ideal-Commutative-Ring =
    is-radical-full-ideal-Commutative-Ring

  is-top-element-full-radical-ideal-Commutative-Ring :
    is-top-element-Large-Poset
      ( radical-ideal-Commutative-Ring-Large-Poset A)
      ( full-radical-ideal-Commutative-Ring)
  is-top-element-full-radical-ideal-Commutative-Ring I =
    is-top-element-full-ideal-Commutative-Ring A
      ( ideal-radical-ideal-Commutative-Ring A I)

  has-top-element-radical-ideal-Commutative-Ring :
    has-top-element-Large-Poset
      ( radical-ideal-Commutative-Ring-Large-Poset A)
  top-has-top-element-Large-Poset
    has-top-element-radical-ideal-Commutative-Ring =
    full-radical-ideal-Commutative-Ring
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-radical-ideal-Commutative-Ring =
    is-top-element-full-radical-ideal-Commutative-Ring
```
