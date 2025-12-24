# Subsets of left modules over commutative rings

```agda
module linear-algebra.subsets-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.subsets-left-modules-rings
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a left module of a commutative ring" Agda=subset-left-module-Commutative-Ring}}
of a [left module](linear-algebra.left-modules-commutative-rings.md) `M` over a
[commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[subset](foundation.subtypes.md) of the underlying type of `M`.

## Definitions

### Subsets of left modules over commutative rings

```agda
module _
  {l1 l2 : Level}
  (l3 : Level)
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  subset-left-module-Commutative-Ring : UU (l2 ⊔ lsuc l3)
  subset-left-module-Commutative-Ring =
    subtype l3 (type-left-module-Commutative-Ring R M)
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (S : subset-left-module-Commutative-Ring l3 R M)
  where

  is-closed-under-addition-prop-subset-left-module-Commutative-Ring :
    Prop (l2 ⊔ l3)
  is-closed-under-addition-prop-subset-left-module-Commutative-Ring =
    is-closed-under-addition-prop-subset-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( S)

  is-closed-under-addition-subset-left-module-Commutative-Ring : UU (l2 ⊔ l3)
  is-closed-under-addition-subset-left-module-Commutative-Ring =
    type-Prop is-closed-under-addition-prop-subset-left-module-Commutative-Ring
```

### The condition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (S : subset-left-module-Commutative-Ring l3 R M)
  where

  is-closed-under-scalar-multiplication-prop-subset-left-module-Commutative-Ring :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-prop-subset-left-module-Commutative-Ring =
    is-closed-under-scalar-multiplication-prop-subset-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( S)

  is-closed-under-scalar-multiplication-subset-left-module-Commutative-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-left-module-Commutative-Ring =
    type-Prop
      ( is-closed-under-scalar-multiplication-prop-subset-left-module-Commutative-Ring)
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (S : subset-left-module-Commutative-Ring l3 R M)
  where

  contains-zero-prop-subset-left-module-Commutative-Ring : Prop l3
  contains-zero-prop-subset-left-module-Commutative-Ring =
    contains-zero-prop-subset-left-module-Ring
      ( ring-Commutative-Ring R)
      ( M)
      ( S)

  contains-zero-subset-left-module-Commutative-Ring : UU l3
  contains-zero-subset-left-module-Commutative-Ring =
    type-Prop contains-zero-prop-subset-left-module-Commutative-Ring
```
