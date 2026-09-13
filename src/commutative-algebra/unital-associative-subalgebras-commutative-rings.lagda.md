# Unital associative subalgebras on commutative rings

```agda
module commutative-algebra.unital-associative-subalgebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.associative-subalgebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-unital-associative-algebras-commutative-rings
open import commutative-algebra.unital-associative-algebras-commutative-rings

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels
```

</details>

## Idea

A
[subset](commutative-algebra.subsets-associative-algebras-commutative-rings.md)
of a
[unital associative algebra](commutative-algebra.unital-associative-algebras-commutative-rings.md)
over a [commutative ring](commutative-algebra.commutative-rings.md) is a
{{#concept "subalgebra" Disambiguation="of a unital associative algebra" Agda=unital-associative-subalgebra-Commutative-Ring}}
if it contains zero and one and is closed under addition, scalar multiplication,
and multiplication, in which case it is itself a unital associative algebra.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  is-subalgebra-prop-subset-unital-associative-algebra-Commutative-Ring :
    subtype
      ( l1 ⊔ l2 ⊔ l3)
      ( subset-unital-associative-algebra-Commutative-Ring l3 R A)
  is-subalgebra-prop-subset-unital-associative-algebra-Commutative-Ring S =
    ( contains-one-prop-subset-unital-associative-algebra-Commutative-Ring
      ( R)
      ( A)
      ( S)) ∧
    ( is-subalgebra-prop-subset-associative-algebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-algebra-Commutative-Ring R A)
      ( S))

  is-subalgebra-subset-unital-associative-algebra-Commutative-Ring :
    subset-unital-associative-algebra-Commutative-Ring l3 R A →
    UU (l1 ⊔ l2 ⊔ l3)
  is-subalgebra-subset-unital-associative-algebra-Commutative-Ring =
    is-in-subtype
      ( is-subalgebra-prop-subset-unital-associative-algebra-Commutative-Ring)

module _
  {l1 l2 : Level}
  (l3 : Level)
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  where

  unital-associative-subalgebra-Commutative-Ring : UU (l1 ⊔ l2 ⊔ lsuc l3)
  unital-associative-subalgebra-Commutative-Ring =
    type-subtype
      ( is-subalgebra-prop-subset-unital-associative-algebra-Commutative-Ring
        { l3 = l3}
        ( R)
        ( A))

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : unital-associative-algebra-Commutative-Ring l2 R)
  ((S , contains-one-S , is-subalgebra-S) :
    unital-associative-subalgebra-Commutative-Ring l3 R A)
  where

  associative-algebra-unital-associative-subalgebra-Commutative-Ring :
    associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  associative-algebra-unital-associative-subalgebra-Commutative-Ring =
    associative-algebra-associative-subalgebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-algebra-Commutative-Ring R A)
      ( S , is-subalgebra-S)

  type-unital-associative-subalgebra-Commutative-Ring : UU (l2 ⊔ l3)
  type-unital-associative-subalgebra-Commutative-Ring = type-subtype S

  mul-unital-associative-subalgebra-Commutative-Ring :
    type-unital-associative-subalgebra-Commutative-Ring →
    type-unital-associative-subalgebra-Commutative-Ring →
    type-unital-associative-subalgebra-Commutative-Ring
  mul-unital-associative-subalgebra-Commutative-Ring =
    mul-associative-algebra-Commutative-Ring
      ( R)
      ( associative-algebra-unital-associative-subalgebra-Commutative-Ring)

  one-unital-associative-subalgebra-Commutative-Ring :
    type-unital-associative-subalgebra-Commutative-Ring
  one-unital-associative-subalgebra-Commutative-Ring =
    ( one-unital-associative-algebra-Commutative-Ring R A ,
      contains-one-S)

  abstract
    left-unit-law-mul-unital-associative-subalgebra-Commutative-Ring :
      (x : type-unital-associative-subalgebra-Commutative-Ring) →
      mul-unital-associative-subalgebra-Commutative-Ring
        ( one-unital-associative-subalgebra-Commutative-Ring)
        ( x) ＝
      x
    left-unit-law-mul-unital-associative-subalgebra-Commutative-Ring (x , _) =
      eq-type-subtype
        ( S)
        ( left-unit-law-mul-unital-associative-algebra-Commutative-Ring R A x)

    right-unit-law-mul-unital-associative-subalgebra-Commutative-Ring :
      (x : type-unital-associative-subalgebra-Commutative-Ring) →
      mul-unital-associative-subalgebra-Commutative-Ring
        ( x)
        ( one-unital-associative-subalgebra-Commutative-Ring) ＝
      x
    right-unit-law-mul-unital-associative-subalgebra-Commutative-Ring (x , _) =
      eq-type-subtype
        ( S)
        ( right-unit-law-mul-unital-associative-algebra-Commutative-Ring R A x)

  is-unital-associative-algebra-unital-associative-subalgebra-Commutative-Ring :
    is-unital
      ( mul-unital-associative-subalgebra-Commutative-Ring)
  is-unital-associative-algebra-unital-associative-subalgebra-Commutative-Ring =
    ( one-unital-associative-subalgebra-Commutative-Ring ,
      left-unit-law-mul-unital-associative-subalgebra-Commutative-Ring ,
      right-unit-law-mul-unital-associative-subalgebra-Commutative-Ring)

  unital-associative-algebra-unital-associative-subalgebra-Commutative-Ring :
    unital-associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  unital-associative-algebra-unital-associative-subalgebra-Commutative-Ring =
    ( associative-algebra-unital-associative-subalgebra-Commutative-Ring ,
      is-unital-associative-algebra-unital-associative-subalgebra-Commutative-Ring)
```
