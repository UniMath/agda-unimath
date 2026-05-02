# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.rings
open import ring-theory.subsets-semirings
```

</details>

## Idea

A {{#concept "subset" Disambiguation="of a ring" Agda=subset-Ring}} of a
[ring](ring-theory.rings.md) `R` is a [subtype](foundation.subtypes.md) of the
underlying type of `R`.

## Definition

### Subsets of rings

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
subset-Ring l R =
  subset-Semiring l (semiring-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-subset-Semiring l (semiring-Ring R)

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-in-subset-Ring :
    type-Ring R → UU l2
  is-in-subset-Ring =
    is-in-subset-Semiring (semiring-Ring R) S

  is-prop-is-in-subset-Ring :
    (x : type-Ring R) → is-prop (is-in-subset-Ring x)
  is-prop-is-in-subset-Ring =
    is-prop-is-in-subset-Semiring (semiring-Ring R) S

  type-subset-Ring :
    UU (l1 ⊔ l2)
  type-subset-Ring =
    type-subset-Semiring (semiring-Ring R) S

  inclusion-subset-Ring :
    type-subset-Ring → type-Ring R
  inclusion-subset-Ring =
    inclusion-subset-Semiring (semiring-Ring R) S

  ap-inclusion-subset-Ring :
    (x y : type-subset-Ring) →
    x ＝ y → (inclusion-subset-Ring x ＝ inclusion-subset-Ring y)
  ap-inclusion-subset-Ring =
    ap-inclusion-subset-Semiring (semiring-Ring R) S

  is-in-subset-inclusion-subset-Ring :
    (x : type-subset-Ring) → is-in-subset-Ring (inclusion-subset-Ring x)
  is-in-subset-inclusion-subset-Ring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Ring :
    {x y : type-Ring R} → is-in-subset-Ring x → (x ＝ y) → is-in-subset-Ring y
  is-closed-under-eq-subset-Ring =
    is-closed-under-eq-subset-Semiring (semiring-Ring R) S

  is-closed-under-eq-subset-Ring' :
    {x y : type-Ring R} → is-in-subset-Ring y → (x ＝ y) → is-in-subset-Ring x
  is-closed-under-eq-subset-Ring' =
    is-closed-under-eq-subset-Semiring' (semiring-Ring R) S
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-zero-prop-subset-Ring : Prop l2
  contains-zero-prop-subset-Ring =
    contains-zero-prop-subset-Semiring (semiring-Ring R) S

  contains-zero-subset-Ring : UU l2
  contains-zero-subset-Ring =
    contains-zero-subset-Semiring (semiring-Ring R) S

  is-prop-contains-zero-subset-Ring :
    is-prop contains-zero-subset-Ring
  is-prop-contains-zero-subset-Ring =
    is-prop-contains-zero-subset-Semiring (semiring-Ring R) S
```

### The condition that a subset contains one

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-one-prop-subset-Ring : Prop l2
  contains-one-prop-subset-Ring =
    contains-one-prop-subset-Semiring (semiring-Ring R) S

  contains-one-subset-Ring : UU l2
  contains-one-subset-Ring =
    contains-one-subset-Semiring (semiring-Ring R) S

  is-prop-contains-one-subset-Ring :
    is-prop contains-one-subset-Ring
  is-prop-contains-one-subset-Ring =
    is-prop-contains-one-subset-Semiring (semiring-Ring R) S
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-addition-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ring =
    is-closed-under-addition-subset-Semiring (semiring-Ring R) S

  abstract
    is-prop-is-closed-under-addition-subset-Ring :
      is-prop is-closed-under-addition-subset-Ring
    is-prop-is-closed-under-addition-subset-Ring =
      is-prop-is-closed-under-addition-subset-Semiring (semiring-Ring R) S

  is-closed-under-addition-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-addition-prop-subset-Ring =
    is-closed-under-addition-prop-subset-Semiring (semiring-Ring R) S
```

### The condition that a subset is closed under negatives

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-negatives-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-negatives-prop-subset-Ring =
    implicit-Π-Prop
      ( type-Ring R)
      ( λ x → hom-Prop (S x) (S (neg-Ring R x)))

  is-closed-under-negatives-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ring =
    {x : type-Ring R} →
    is-in-subset-Ring R S x → is-in-subset-Ring R S (neg-Ring R x)

  abstract
    is-prop-is-closed-under-negatives-subset-Ring :
      is-prop is-closed-under-negatives-subset-Ring
    is-prop-is-closed-under-negatives-subset-Ring =
      is-prop-type-Prop is-closed-under-negatives-prop-subset-Ring
```

### The condition that a subset is closed under multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-multiplication-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Ring =
    is-closed-under-multiplication-prop-subset-Semiring (semiring-Ring R) S

  is-closed-under-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Ring =
    is-closed-under-multiplication-subset-Semiring (semiring-Ring R) S

  is-prop-is-closed-under-multiplication-subset-Ring :
    is-prop is-closed-under-multiplication-subset-Ring
  is-prop-is-closed-under-multiplication-subset-Ring =
    is-prop-is-closed-under-multiplication-subset-Semiring (semiring-Ring R) S
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-left-multiplication-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-left-multiplication-prop-subset-Ring =
    is-closed-under-left-multiplication-prop-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-left-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring =
    is-closed-under-left-multiplication-subset-Semiring (semiring-Ring R) S

  is-prop-is-closed-under-left-multiplication-subset-Ring :
    is-prop is-closed-under-left-multiplication-subset-Ring
  is-prop-is-closed-under-left-multiplication-subset-Ring =
    is-prop-is-closed-under-left-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-right-multiplication-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-right-multiplication-prop-subset-Ring =
    is-closed-under-right-multiplication-prop-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-right-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring =
    is-closed-under-right-multiplication-subset-Semiring (semiring-Ring R) S

  is-prop-is-closed-under-right-multiplication-subset-Ring :
    is-prop is-closed-under-right-multiplication-subset-Ring
  is-prop-is-closed-under-right-multiplication-subset-Ring =
    is-prop-is-closed-under-right-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)
```

### The condition that a subset is closed under two-sided multiplication by arbitrary elements

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-two-sided-multiplication-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-prop-subset-Ring =
    is-closed-under-two-sided-multiplication-prop-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-two-sided-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-subset-Ring =
    is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-prop-is-closed-under-two-sided-multiplication-subset-Ring :
    is-prop is-closed-under-two-sided-multiplication-subset-Ring
  is-prop-is-closed-under-two-sided-multiplication-subset-Ring =
    is-prop-is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)
```

### The condition that a subset is an additive submonoid

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-additive-submonoid-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-additive-submonoid-prop-subset-Ring =
    is-additive-submonoid-prop-subset-Semiring (semiring-Ring R) S

  is-additive-submonoid-subset-Ring : UU (l1 ⊔ l2)
  is-additive-submonoid-subset-Ring =
    is-additive-submonoid-subset-Semiring (semiring-Ring R) S

  is-prop-is-additive-submonoid-subset-Ring :
    is-prop is-additive-submonoid-subset-Ring
  is-prop-is-additive-submonoid-subset-Ring =
    is-prop-is-additive-submonoid-subset-Semiring (semiring-Ring R) S
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-additive-subgroup-subset-Ring : UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring =
    is-subgroup-Ab (ab-Ring R) S

  is-prop-is-additive-subgroup-subset-Ring :
    is-prop is-additive-subgroup-subset-Ring
  is-prop-is-additive-subgroup-subset-Ring =
    is-prop-is-subgroup-Ab (ab-Ring R) S

  is-additive-subgroup-prop-subset-Ring : Prop (l1 ⊔ l2)
  pr1 is-additive-subgroup-prop-subset-Ring =
    is-additive-subgroup-subset-Ring
  pr2 is-additive-subgroup-prop-subset-Ring =
    is-prop-is-additive-subgroup-subset-Ring
```

## Properties

### Any subset that is closed under two-sided multiplication is closed under left and right multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-left-multiplication-is-closed-under-two-sided-multiplication-subset-Ring :
    is-closed-under-two-sided-multiplication-subset-Ring R S →
    is-closed-under-left-multiplication-subset-Ring R S
  is-closed-under-left-multiplication-is-closed-under-two-sided-multiplication-subset-Ring =
    is-closed-under-left-multiplication-is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-right-multiplication-is-closed-under-two-sided-multiplication-subset-Ring :
    is-closed-under-two-sided-multiplication-subset-Ring R S →
    is-closed-under-right-multiplication-subset-Ring R S
  is-closed-under-right-multiplication-is-closed-under-two-sided-multiplication-subset-Ring =
    is-closed-under-right-multiplication-is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)
```

### Any subset that is closed under left, right, or two-sided multiplication is closed under multiplication

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-multiplication-is-closed-under-left-multiplication-subset-Ring :
    is-closed-under-left-multiplication-subset-Ring R S →
    is-closed-under-multiplication-subset-Ring R S
  is-closed-under-multiplication-is-closed-under-left-multiplication-subset-Ring =
    is-closed-under-multiplication-is-closed-under-left-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-multiplication-is-closed-under-right-multiplication-subset-Ring :
    is-closed-under-right-multiplication-subset-Ring R S →
    is-closed-under-multiplication-subset-Ring R S
  is-closed-under-multiplication-is-closed-under-right-multiplication-subset-Ring =
    is-closed-under-multiplication-is-closed-under-right-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)

  is-closed-under-multiplication-is-closed-under-two-sided-multiplication-subset-Ring :
    is-closed-under-two-sided-multiplication-subset-Ring R S →
    is-closed-under-multiplication-subset-Ring R S
  is-closed-under-multiplication-is-closed-under-two-sided-multiplication-subset-Ring =
    is-closed-under-multiplication-is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Ring R)
      ( S)
```

### Any subset that is closed under left or right multiplication is closed under negatives

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-closed-under-negatives-is-closed-under-left-multiplication-subset-Ring :
    is-closed-under-left-multiplication-subset-Ring R S →
    is-closed-under-negatives-subset-Ring R S
  is-closed-under-negatives-is-closed-under-left-multiplication-subset-Ring
    H {x} K =
    is-closed-under-eq-subset-Ring R S
      ( H K)
      ( mul-neg-one-Ring R x)

  is-closed-under-negatives-is-closed-under-right-multiplication-subset-Ring :
    is-closed-under-right-multiplication-subset-Ring R S →
    is-closed-under-negatives-subset-Ring R S
  is-closed-under-negatives-is-closed-under-right-multiplication-subset-Ring
    H {x} K =
    is-closed-under-eq-subset-Ring R S
      ( H K)
      ( mul-neg-one-Ring' R x)
```

### Any additive submonoid of a ring that is closed under left or right multiplication is an additive subgroup

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-additive-subgroup-is-closed-under-left-multiplication-subset-Ring :
    is-additive-submonoid-subset-Ring R S →
    is-closed-under-left-multiplication-subset-Ring R S →
    is-additive-subgroup-subset-Ring R S
  is-additive-subgroup-is-closed-under-left-multiplication-subset-Ring
    (H , K) L =
    ( H ,
      K ,
      is-closed-under-negatives-is-closed-under-left-multiplication-subset-Ring
        R S L)

  is-additive-subgroup-is-closed-under-right-multiplication-subset-Ring :
    is-additive-submonoid-subset-Ring R S →
    is-closed-under-right-multiplication-subset-Ring R S →
    is-additive-subgroup-subset-Ring R S
  is-additive-subgroup-is-closed-under-right-multiplication-subset-Ring
    (H , K) L =
    ( H ,
      K ,
      is-closed-under-negatives-is-closed-under-right-multiplication-subset-Ring
        R S L)
```
