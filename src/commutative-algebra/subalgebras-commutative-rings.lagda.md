# Subalgebras over commutative rings

```agda
module commutative-algebra.subalgebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings
open import commutative-algebra.subsets-algebras-commutative-rings

open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.left-submodules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

A [subset](commutative-algebra.subsets-algebras-commutative-rings.md) of an
[algebra](commutative-algebra.algebras-commutative-rings.md) over a
[commutative ring](commutative-algebra.commutative-rings.md) is a
{{#concept "subalgebra" WDID=Q629933 WD="subalgebra" Agda=subalgebra-Commutative-Ring}}
if it contains zero and is closed under addition, scalar multiplication, and
multiplication, in which case it is itself an algebra.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  (S : subset-algebra-Commutative-Ring l3 R A)
  where

  is-subalgebra-prop-subset-algebra-Commutative-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-subalgebra-prop-subset-algebra-Commutative-Ring =
    ( contains-zero-prop-subset-algebra-Commutative-Ring R A S) ∧
    ( is-closed-under-addition-prop-subset-algebra-Commutative-Ring R A S) ∧
    ( is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring
      ( R)
      ( A)
      ( S)) ∧
    ( is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring R A S)

  is-subalgebra-subset-algebra-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-subalgebra-subset-algebra-Commutative-Ring =
    type-Prop is-subalgebra-prop-subset-algebra-Commutative-Ring

subalgebra-Commutative-Ring :
  {l1 l2 : Level} (l3 : Level) →
  (R : Commutative-Ring l1) (A : algebra-Commutative-Ring l2 R) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
subalgebra-Commutative-Ring l3 R A =
  type-subtype
    ( is-subalgebra-prop-subset-algebra-Commutative-Ring {l3 = l3} R A)

module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  (S@(subtype-S , 0∈S , closed-addition-S , closed-scalar-S , closed-mul-S) :
    subalgebra-Commutative-Ring l3 R A)
  where

  left-module-subalgebra-Commutative-Ring :
    left-module-Commutative-Ring (l2 ⊔ l3) R
  left-module-subalgebra-Commutative-Ring =
    left-module-left-submodule-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring R A)
      ( subtype-S , 0∈S , closed-addition-S , closed-scalar-S)

  type-subalgebra-Commutative-Ring : UU (l2 ⊔ l3)
  type-subalgebra-Commutative-Ring = type-subtype subtype-S

  mul-subalgebra-Commutative-Ring :
    type-subalgebra-Commutative-Ring →
    type-subalgebra-Commutative-Ring →
    type-subalgebra-Commutative-Ring
  mul-subalgebra-Commutative-Ring (x , x∈S) (y , y∈S) =
    ( mul-algebra-Commutative-Ring R A x y ,
      closed-mul-S x y x∈S y∈S)

  abstract
    is-additive-left-mul-subalgebra-Commutative-Ring :
      (x : type-subalgebra-Commutative-Ring) →
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( left-module-subalgebra-Commutative-Ring)
        ( left-module-subalgebra-Commutative-Ring)
        ( mul-subalgebra-Commutative-Ring x)
    is-additive-left-mul-subalgebra-Commutative-Ring
      (x , x∈S) (y , y∈S) (z , z∈S) =
      eq-type-subtype
        ( subtype-S)
        ( left-distributive-mul-add-algebra-Commutative-Ring R A x y z)

    is-homogeneous-left-mul-subalgebra-Commutative-Ring :
      (x : type-subalgebra-Commutative-Ring) →
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( left-module-subalgebra-Commutative-Ring)
        ( left-module-subalgebra-Commutative-Ring)
        ( mul-subalgebra-Commutative-Ring x)
    is-homogeneous-left-mul-subalgebra-Commutative-Ring (x , x∈S) c (y , y∈S) =
      eq-type-subtype
        ( subtype-S)
        ( inv (left-swap-scalar-mul-mul-algebra-Commutative-Ring R A c x y))

    is-additive-right-mul-subalgebra-Commutative-Ring :
      (y : type-subalgebra-Commutative-Ring) →
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( left-module-subalgebra-Commutative-Ring)
        ( left-module-subalgebra-Commutative-Ring)
        ( λ x → mul-subalgebra-Commutative-Ring x y)
    is-additive-right-mul-subalgebra-Commutative-Ring
      (y , y∈S) (x , x∈S) (z , z∈S) =
      eq-type-subtype
        ( subtype-S)
        ( right-distributive-mul-add-algebra-Commutative-Ring R A x z y)

    is-homogeneous-right-mul-subalgebra-Commutative-Ring :
      (y : type-subalgebra-Commutative-Ring) →
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( left-module-subalgebra-Commutative-Ring)
        ( left-module-subalgebra-Commutative-Ring)
        ( λ x → mul-subalgebra-Commutative-Ring x y)
    is-homogeneous-right-mul-subalgebra-Commutative-Ring (y , y∈S) c (x , x∈S) =
      eq-type-subtype
        ( subtype-S)
        ( associative-scalar-mul-mul-algebra-Commutative-Ring R A c x y)

  is-linear-left-mul-subalgebra-Commutative-Ring :
    (x : type-subalgebra-Commutative-Ring) →
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-subalgebra-Commutative-Ring)
      ( left-module-subalgebra-Commutative-Ring)
      ( mul-subalgebra-Commutative-Ring x)
  is-linear-left-mul-subalgebra-Commutative-Ring x =
    ( is-additive-left-mul-subalgebra-Commutative-Ring x ,
      is-homogeneous-left-mul-subalgebra-Commutative-Ring x)

  is-linear-right-mul-subalgebra-Commutative-Ring :
    (y : type-subalgebra-Commutative-Ring) →
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-subalgebra-Commutative-Ring)
      ( left-module-subalgebra-Commutative-Ring)
      ( λ x → mul-subalgebra-Commutative-Ring x y)
  is-linear-right-mul-subalgebra-Commutative-Ring y =
    ( is-additive-right-mul-subalgebra-Commutative-Ring y ,
      is-homogeneous-right-mul-subalgebra-Commutative-Ring y)

  bilinear-mul-subalgebra-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-subalgebra-Commutative-Ring)
      ( left-module-subalgebra-Commutative-Ring)
      ( left-module-subalgebra-Commutative-Ring)
  bilinear-mul-subalgebra-Commutative-Ring =
    ( mul-subalgebra-Commutative-Ring ,
      is-linear-right-mul-subalgebra-Commutative-Ring ,
      is-linear-left-mul-subalgebra-Commutative-Ring)

  algebra-subalgebra-Commutative-Ring : algebra-Commutative-Ring (l2 ⊔ l3) R
  algebra-subalgebra-Commutative-Ring =
    ( left-module-subalgebra-Commutative-Ring ,
      bilinear-mul-subalgebra-Commutative-Ring)
```
