# Subsets of associative algebras over commutative rings

```agda
module commutative-algebra.subsets-associative-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-algebras-commutative-rings

open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of an associative algebra over a commutative ring" Agda=subset-associative-algebra-Commutative-Ring}}
of an
[associative algebra](commutative-algebra.associative-algebras-commutative-rings.md)
`A` over a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[subset](foundation.subtypes.md) of the underlying type of `A`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  subset-associative-algebra-Commutative-Ring : UU (l2 ⊔ lsuc l3)
  subset-associative-algebra-Commutative-Ring =
    subtype l3 (type-associative-algebra-Commutative-Ring R A)
```

## Properties

### The condition of a subset containing zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  contains-zero-prop-subset-associative-algebra-Commutative-Ring :
    subtype l3 (subset-associative-algebra-Commutative-Ring l3 R A)
  contains-zero-prop-subset-associative-algebra-Commutative-Ring =
    contains-zero-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)

  contains-zero-subset-associative-algebra-Commutative-Ring :
    subset-associative-algebra-Commutative-Ring l3 R A → UU l3
  contains-zero-subset-associative-algebra-Commutative-Ring =
    is-in-subtype contains-zero-prop-subset-associative-algebra-Commutative-Ring
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-addition-prop-subset-associative-algebra-Commutative-Ring :
    subtype (l2 ⊔ l3) (subset-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-addition-prop-subset-associative-algebra-Commutative-Ring =
    is-closed-under-addition-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)

  is-closed-under-addition-subset-associative-algebra-Commutative-Ring :
    subset-associative-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-addition-subset-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-addition-prop-subset-associative-algebra-Commutative-Ring)
```

### The condition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-scalar-multiplication-prop-subset-associative-algebra-Commutative-Ring :
    subtype (l1 ⊔ l2 ⊔ l3) (subset-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-scalar-multiplication-prop-subset-associative-algebra-Commutative-Ring =
    is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)

  is-closed-under-scalar-multiplication-subset-associative-algebra-Commutative-Ring :
    subset-associative-algebra-Commutative-Ring l3 R A → UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-scalar-multiplication-prop-subset-associative-algebra-Commutative-Ring)
```

### The condition that a subset is closed under multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  is-closed-under-multiplication-prop-subset-associative-algebra-Commutative-Ring :
    subtype (l2 ⊔ l3) (subset-associative-algebra-Commutative-Ring l3 R A)
  is-closed-under-multiplication-prop-subset-associative-algebra-Commutative-Ring =
    is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)

  is-closed-under-multiplication-subset-associative-algebra-Commutative-Ring :
    subset-associative-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-multiplication-subset-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-closed-under-multiplication-prop-subset-associative-algebra-Commutative-Ring)
```
