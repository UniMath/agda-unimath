# Subsets of commutative rings

```agda
module commutative-algebra.subsets-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.subsets-rings
```

</details>

## Idea

A {{#concept "subset" Disambiguation="commutative ring" Agda=subset-Commutative-Ring}} of a [commutative ring](commutative-algebra.commutative-rings.md) is a [subtype](foundation-core.subtypes.md) of its underlying type.

## Definitions

### Subsets of rings

```agda
subset-Commutative-Ring :
  (l : Level) {l1 : Level} (A : Commutative-Ring l1) → UU (lsuc l ⊔ l1)
subset-Commutative-Ring l A = subtype l (type-Commutative-Ring A)

is-set-subset-Commutative-Ring :
  (l : Level) {l1 : Level} (A : Commutative-Ring l1) →
  is-set (subset-Commutative-Ring l A)
is-set-subset-Commutative-Ring l A =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-in-subset-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-subset-Commutative-Ring = is-in-subtype S

  is-prop-is-in-subset-Commutative-Ring :
    (x : type-Commutative-Ring A) → is-prop (is-in-subset-Commutative-Ring x)
  is-prop-is-in-subset-Commutative-Ring = is-prop-is-in-subtype S

  type-subset-Commutative-Ring : UU (l1 ⊔ l2)
  type-subset-Commutative-Ring = type-subtype S

  inclusion-subset-Commutative-Ring :
    type-subset-Commutative-Ring → type-Commutative-Ring A
  inclusion-subset-Commutative-Ring = inclusion-subtype S

  ap-inclusion-subset-Commutative-Ring :
    (x y : type-subset-Commutative-Ring) → x ＝ y →
    inclusion-subset-Commutative-Ring x ＝ inclusion-subset-Commutative-Ring y
  ap-inclusion-subset-Commutative-Ring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Commutative-Ring :
    (x : type-subset-Commutative-Ring) →
    is-in-subset-Commutative-Ring (inclusion-subset-Commutative-Ring x)
  is-in-subset-inclusion-subset-Commutative-Ring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Commutative-Ring :
    {x y : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring x → (x ＝ y) → is-in-subset-Commutative-Ring y
  is-closed-under-eq-subset-Commutative-Ring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Commutative-Ring' :
    {x y : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring y → (x ＝ y) → is-in-subset-Commutative-Ring x
  is-closed-under-eq-subset-Commutative-Ring' =
    is-closed-under-eq-subtype' S
```

### The condition that a subset contains zero

This condition asserts that `0 ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  contains-zero-prop-subset-Commutative-Ring :
    Prop l2
  contains-zero-prop-subset-Commutative-Ring =
    contains-zero-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  contains-zero-subset-Commutative-Ring :
    UU l2
  contains-zero-subset-Commutative-Ring =
    contains-zero-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-contains-zero-subset-Commutative-Ring :
    is-prop contains-zero-subset-Commutative-Ring
  is-prop-contains-zero-subset-Commutative-Ring =
    is-prop-contains-zero-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset contains one

This condition asserts that `1 ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  contains-one-prop-subset-Commutative-Ring :
    Prop l2
  contains-one-prop-subset-Commutative-Ring =
    contains-one-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  contains-one-subset-Commutative-Ring :
    UU l2
  contains-one-subset-Commutative-Ring =
    contains-one-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-contains-one-subset-Commutative-Ring :
    is-prop contains-one-subset-Commutative-Ring
  is-prop-contains-one-subset-Commutative-Ring =
    is-prop-contains-one-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under addition

This condition asserts that for any `x y ∈ S` we have `x + y ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-addition-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-addition-prop-subset-Commutative-Ring =
    is-closed-under-addition-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-closed-under-addition-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Commutative-Ring =
    is-closed-under-addition-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-addition-subset-Commutative-Ring :
    is-prop is-closed-under-addition-subset-Commutative-Ring
  is-prop-is-closed-under-addition-subset-Commutative-Ring =
    is-prop-is-closed-under-addition-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under negatives

This condition asserts that for any `x ∈ S` we have `-x ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-negatives-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-negatives-prop-subset-Commutative-Ring =
    is-closed-under-negatives-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
      
  is-closed-under-negatives-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Commutative-Ring =
    is-closed-under-negatives-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-negatives-subset-Commutative-Ring :
    is-prop is-closed-under-negatives-subset-Commutative-Ring
  is-prop-is-closed-under-negatives-subset-Commutative-Ring =
    is-prop-is-closed-under-negatives-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under multiplication

This condition asserts that for any `x y ∈ S` we have `xy ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-multiplication-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Commutative-Ring =
    is-closed-under-multiplication-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
      
  is-closed-under-multiplication-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Commutative-Ring =
    is-closed-under-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-multiplication-subset-Commutative-Ring :
    is-prop is-closed-under-multiplication-subset-Commutative-Ring
  is-prop-is-closed-under-multiplication-subset-Commutative-Ring =
    is-prop-is-closed-under-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

This condition asserts that for any `r x : R`, if `x ∈ S` then `rx ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-left-multiplication-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-left-multiplication-prop-subset-Commutative-Ring =
    is-closed-under-left-multiplication-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
      
  is-closed-under-left-multiplication-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Commutative-Ring =
    is-closed-under-left-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-left-multiplication-subset-Commutative-Ring :
    is-prop is-closed-under-left-multiplication-subset-Commutative-Ring
  is-prop-is-closed-under-left-multiplication-subset-Commutative-Ring =
    is-prop-is-closed-under-left-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

This condition asserts that for any `x r : R`, if `x ∈ S` then `xr ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-right-multiplication-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-right-multiplication-prop-subset-Commutative-Ring =
    is-closed-under-right-multiplication-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-closed-under-right-multiplication-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Commutative-Ring =
    is-closed-under-right-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-right-multiplication-subset-Commutative-Ring :
    is-prop is-closed-under-right-multiplication-subset-Commutative-Ring
  is-prop-is-closed-under-right-multiplication-subset-Commutative-Ring =
    is-prop-is-closed-under-right-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under two-sided multiplication by arbitrary elements

This condition asserts that for any `r x u : R`, if `x ∈ S` then `(rx)u ∈ S`.

The operation `r x u ↦ (rx)u` is the standard form of two-sided multiplication in `R`, which gives the semiring `R` the structure of an (additive) [monoid with `R`-action](ring-theory.monoids-with-semiring-action.md).

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-closed-under-two-sided-multiplication-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-prop-subset-Commutative-Ring =
    is-closed-under-two-sided-multiplication-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-closed-under-two-sided-multiplication-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-subset-Commutative-Ring =
    is-closed-under-two-sided-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-closed-under-two-sided-multiplication-subset-Commutative-Ring :
    is-prop is-closed-under-two-sided-multiplication-subset-Commutative-Ring
  is-prop-is-closed-under-two-sided-multiplication-subset-Commutative-Ring =
    is-prop-is-closed-under-two-sided-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is an additive submonoid

This condition asserts that the subset contains `0` and is closed under addition.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1)
  (S : subset-Commutative-Ring l2 A)
  where

  is-additive-submonoid-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-additive-submonoid-prop-subset-Commutative-Ring =
    is-additive-submonoid-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-additive-submonoid-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-additive-submonoid-subset-Commutative-Ring =
    is-additive-submonoid-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-additive-submonoid-subset-Commutative-Ring :
    is-prop is-additive-submonoid-subset-Commutative-Ring
  is-prop-is-additive-submonoid-subset-Commutative-Ring =
    is-prop-is-additive-submonoid-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is an additive subgroup

This condition asserts that the subset contains `0`, is closed under addition, and is closed under negatives.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-additive-subgroup-prop-subset-Commutative-Ring :
    Prop (l1 ⊔ l2)
  is-additive-subgroup-prop-subset-Commutative-Ring =
    is-additive-subgroup-prop-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-additive-subgroup-subset-Commutative-Ring :
    UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Commutative-Ring =
    is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)

  is-prop-is-additive-subgroup-subset-Commutative-Ring :
    is-prop is-additive-subgroup-subset-Commutative-Ring
  is-prop-is-additive-subgroup-subset-Commutative-Ring =
    is-prop-is-additive-subgroup-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset of a ring is an multiplicative submonoid

This condition asserts that the subset contains `1` and is closed under multiplication.

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1) (S : subset-Commutative-Ring l2 R)
  where

  is-multiplicative-submonoid-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-multiplicative-submonoid-subset-Commutative-Ring =
    is-multiplicative-submonoid-subset-Ring
      ( ring-Commutative-Ring R)
      ( S)

  is-prop-is-multiplicative-submonoid-subset-Commutative-Ring :
    is-prop is-multiplicative-submonoid-subset-Commutative-Ring
  is-prop-is-multiplicative-submonoid-subset-Commutative-Ring =
    is-prop-is-multiplicative-submonoid-subset-Ring
      ( ring-Commutative-Ring R)
      ( S)

  is-multiplicative-submonoid-prop-subset-Commutative-Ring : Prop (l1 ⊔ l2)
  is-multiplicative-submonoid-prop-subset-Commutative-Ring =
    is-multiplicative-submonoid-prop-subset-Ring
      ( ring-Commutative-Ring R)
      ( S)
```
