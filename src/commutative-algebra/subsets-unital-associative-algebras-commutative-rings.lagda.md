# Subsets of unital associative algebras on commutative rings

```agda
module commutative-algebra.subsets-unital-associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-algebras-commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of a unital associative algebra over a commutative ring" Agda=subset-unital-associative-algebra-Commutative-Ring}}
of a
[unital associative algebra](commutative-algebra.unital-associative-algebras-commutative-rings.md)
`A` over a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[subset](foundation.subtypes.md) of the underlying type of `A`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  subset-unital-associative-algebra-Commutative-Ring : UU (l2 ⊔ lsuc l3)
  subset-unital-associative-algebra-Commutative-Ring =
    subtype l3 (type-unital-associative-algebra-Commutative-Ring R A)
```

## Properties

### The condition of a subset containing zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  contains-zero-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype l3 (subset-unital-associative-algebra-Commutative-Ring l3 R A)
  contains-zero-prop-subset-unital-associative-algebra-Commutative-Ring =
    contains-zero-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring R A)

  contains-zero-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A → UU l3
  contains-zero-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( contains-zero-prop-subset-unital-associative-algebra-Commutative-Ring)
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-addition-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype
      ( l2 ⊔ l3)
      ( subset-unital-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-addition-prop-subset-unital-associative-algebra-Commutative-Ring =
    is-closed-under-addition-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring R A)

  is-closed-under-addition-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-addition-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-addition-prop-subset-unital-associative-algebra-Commutative-Ring)
```

### The condition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-scalar-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( subset-unital-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-scalar-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring =
    is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring R A)

  is-closed-under-scalar-multiplication-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A →
    UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-scalar-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring)
```

### The condition that a subset is closed under multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype
      ( l2 ⊔ l3)
      ( subset-unital-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring =
    is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-unital-associative-algebra-Commutative-Ring R A)

  is-closed-under-multiplication-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-multiplication-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-multiplication-prop-subset-unital-associative-algebra-Commutative-Ring)
```

### The condition that a subset contains one

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  contains-one-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype l3 (subset-unital-associative-algebra-Commutative-Ring l3 R A)
  contains-one-prop-subset-unital-associative-algebra-Commutative-Ring S =
    S (one-unital-associative-algebra-Commutative-Ring R A)

  contains-one-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A → UU l3
  contains-one-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( contains-one-prop-subset-unital-associative-algebra-Commutative-Ring)
```
