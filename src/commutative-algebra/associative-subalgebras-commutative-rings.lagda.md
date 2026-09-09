# Associative subalgebras over commutative rings

```agda
module commutative-algebra.associative-subalgebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.associative-algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.subalgebras-commutative-rings
open import commutative-algebra.subsets-associative-algebras-commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A
[subset](commutative-algebra.subsets-associative-algebras-commutative-rings.md)
of an
[associative algebra](commutative-algebra.associative-algebras-commutative-rings.md)
over a [commutative ring](commutative-algebra.commutative-rings.md) is a
{{#concept "subalgebra" Disambiguation="of an associative algebra" Agda=associative-subalgebra-Commutative-Ring}}
if it contains zero and is closed under addition, scalar multiplication, and
multiplication, in which case it is itself an associative algebra.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  is-subalgebra-prop-subset-associative-algebra-Commutative-Ring :
    subtype (l1 ⊔ l2 ⊔ l3) (subset-associative-algebra-Commutative-Ring l3 R A)
  is-subalgebra-prop-subset-associative-algebra-Commutative-Ring =
    is-subalgebra-prop-subset-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)

  is-subalgebra-subset-associative-algebra-Commutative-Ring :
    subset-associative-algebra-Commutative-Ring l3 R A → UU (l1 ⊔ l2 ⊔ l3)
  is-subalgebra-subset-associative-algebra-Commutative-Ring =
    is-in-subtype is-subalgebra-prop-subset-associative-algebra-Commutative-Ring

module _
  {l1 l2 : Level}
  (l3 : Level)
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  where

  associative-subalgebra-Commutative-Ring : UU (l1 ⊔ l2 ⊔ lsuc l3)
  associative-subalgebra-Commutative-Ring =
    type-subtype
      ( is-subalgebra-prop-subset-associative-algebra-Commutative-Ring
        { l3 = l3}
        ( R)
        ( A))

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : associative-algebra-Commutative-Ring l2 R)
  (SA@(S , is-subalgebra-S) :
    associative-subalgebra-Commutative-Ring l3 R A)
  where

  algebra-associative-subalgebra-Commutative-Ring :
    algebra-Commutative-Ring (l2 ⊔ l3) R
  algebra-associative-subalgebra-Commutative-Ring =
    algebra-subalgebra-Commutative-Ring
      ( R)
      ( algebra-associative-algebra-Commutative-Ring R A)
      ( SA)

  type-associative-subalgebra-Commutative-Ring : UU (l2 ⊔ l3)
  type-associative-subalgebra-Commutative-Ring = type-subtype S

  mul-algebra-associative-subalgebra-Commutative-Ring :
    type-associative-subalgebra-Commutative-Ring →
    type-associative-subalgebra-Commutative-Ring →
    type-associative-subalgebra-Commutative-Ring
  mul-algebra-associative-subalgebra-Commutative-Ring =
    mul-algebra-Commutative-Ring
      ( R)
      ( algebra-associative-subalgebra-Commutative-Ring)

  abstract
    associative-mul-algebra-associative-subalgebra-Commutative-Ring :
      (a b c : type-associative-subalgebra-Commutative-Ring) →
      mul-algebra-associative-subalgebra-Commutative-Ring
        ( mul-algebra-associative-subalgebra-Commutative-Ring a b)
        ( c) ＝
      mul-algebra-associative-subalgebra-Commutative-Ring
        ( a)
        ( mul-algebra-associative-subalgebra-Commutative-Ring b c)
    associative-mul-algebra-associative-subalgebra-Commutative-Ring
      (a , _) (b , _) (c , _) =
      eq-type-subtype
        ( S)
        ( associative-mul-associative-algebra-Commutative-Ring R A a b c)

  associative-algebra-associative-subalgebra-Commutative-Ring :
    associative-algebra-Commutative-Ring (l2 ⊔ l3) R
  associative-algebra-associative-subalgebra-Commutative-Ring =
    ( algebra-associative-subalgebra-Commutative-Ring ,
      associative-mul-algebra-associative-subalgebra-Commutative-Ring)
```
