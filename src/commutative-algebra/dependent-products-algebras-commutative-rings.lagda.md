# Dependent products of algebras over commutative rings

```agda
module commutative-algebra.dependent-products-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.dependent-products-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

Given a [commutative ring](commutative-algebra.commutative-rings.md) `R` and a
family of [algebras](commutative-algebra.algebras-commutative-rings.md) `Aᵢ`
over `R` indexed by `i : I`, the dependent product `Π (i : I) Aᵢ` is an algebra
over `R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (I : UU l2)
  (A : I → algebra-Commutative-Ring l3 R)
  where

  left-module-Π-algebra-Commutative-Ring :
    left-module-Commutative-Ring (l2 ⊔ l3) R
  left-module-Π-algebra-Commutative-Ring =
    Π-left-module-Commutative-Ring R
      ( I)
      ( λ i → left-module-algebra-Commutative-Ring R (A i))

  type-Π-algebra-Commutative-Ring : UU (l2 ⊔ l3)
  type-Π-algebra-Commutative-Ring =
    (i : I) → type-algebra-Commutative-Ring R (A i)

  mul-Π-algebra-Commutative-Ring :
    type-Π-algebra-Commutative-Ring →
    type-Π-algebra-Commutative-Ring →
    type-Π-algebra-Commutative-Ring
  mul-Π-algebra-Commutative-Ring f g i =
    mul-algebra-Commutative-Ring R (A i) (f i) (g i)

  abstract
    is-additive-left-mul-Π-algebra-Commutative-Ring :
      (f : type-Π-algebra-Commutative-Ring) →
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( left-module-Π-algebra-Commutative-Ring)
        ( left-module-Π-algebra-Commutative-Ring)
        ( mul-Π-algebra-Commutative-Ring f)
    is-additive-left-mul-Π-algebra-Commutative-Ring f g h =
      eq-htpy
        ( λ i →
          is-additive-map-ev-left-bilinear-map-left-module-Commutative-Ring R
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( bilinear-mul-algebra-Commutative-Ring R (A i))
            ( f i)
            ( g i)
            ( h i))

    is-homogeneous-left-mul-Π-algebra-Commutative-Ring :
      (f : type-Π-algebra-Commutative-Ring) →
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( left-module-Π-algebra-Commutative-Ring)
        ( left-module-Π-algebra-Commutative-Ring)
        ( mul-Π-algebra-Commutative-Ring f)
    is-homogeneous-left-mul-Π-algebra-Commutative-Ring f c g =
      eq-htpy
        ( λ i →
          is-homogeneous-map-ev-left-bilinear-map-left-module-Commutative-Ring R
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( bilinear-mul-algebra-Commutative-Ring R (A i))
            ( f i)
            ( c)
            ( g i))

  is-linear-left-mul-Π-algebra-Commutative-Ring :
    (f : type-Π-algebra-Commutative-Ring) →
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-Π-algebra-Commutative-Ring)
      ( left-module-Π-algebra-Commutative-Ring)
      ( mul-Π-algebra-Commutative-Ring f)
  is-linear-left-mul-Π-algebra-Commutative-Ring f =
    ( is-additive-left-mul-Π-algebra-Commutative-Ring f ,
      is-homogeneous-left-mul-Π-algebra-Commutative-Ring f)

  abstract
    is-additive-right-mul-Π-algebra-Commutative-Ring :
      (g : type-Π-algebra-Commutative-Ring) →
      is-additive-map-left-module-Commutative-Ring
        ( R)
        ( left-module-Π-algebra-Commutative-Ring)
        ( left-module-Π-algebra-Commutative-Ring)
        ( λ f → mul-Π-algebra-Commutative-Ring f g)
    is-additive-right-mul-Π-algebra-Commutative-Ring f g h =
      eq-htpy
        ( λ i →
          is-additive-map-ev-right-bilinear-map-left-module-Commutative-Ring R
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( bilinear-mul-algebra-Commutative-Ring R (A i))
            ( f i)
            ( g i)
            ( h i))

    is-homogeneous-right-mul-Π-algebra-Commutative-Ring :
      (g : type-Π-algebra-Commutative-Ring) →
      is-homogeneous-map-left-module-Commutative-Ring
        ( R)
        ( left-module-Π-algebra-Commutative-Ring)
        ( left-module-Π-algebra-Commutative-Ring)
        ( λ f → mul-Π-algebra-Commutative-Ring f g)
    is-homogeneous-right-mul-Π-algebra-Commutative-Ring f c g =
      eq-htpy
        ( λ i →
          is-homogeneous-map-ev-right-bilinear-map-left-module-Commutative-Ring
            ( R)
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( left-module-algebra-Commutative-Ring R (A i))
            ( bilinear-mul-algebra-Commutative-Ring R (A i))
            ( f i)
            ( c)
            ( g i))

  is-linear-right-mul-Π-algebra-Commutative-Ring :
    (g : type-Π-algebra-Commutative-Ring) →
    is-linear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-Π-algebra-Commutative-Ring)
      ( left-module-Π-algebra-Commutative-Ring)
      ( λ f → mul-Π-algebra-Commutative-Ring f g)
  is-linear-right-mul-Π-algebra-Commutative-Ring g =
    ( is-additive-right-mul-Π-algebra-Commutative-Ring g ,
      is-homogeneous-right-mul-Π-algebra-Commutative-Ring g)

  bilinear-mul-Π-algebra-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-Π-algebra-Commutative-Ring)
      ( left-module-Π-algebra-Commutative-Ring)
      ( left-module-Π-algebra-Commutative-Ring)
  bilinear-mul-Π-algebra-Commutative-Ring =
    ( mul-Π-algebra-Commutative-Ring ,
      is-linear-right-mul-Π-algebra-Commutative-Ring ,
      is-linear-left-mul-Π-algebra-Commutative-Ring)

  Π-algebra-Commutative-Ring : algebra-Commutative-Ring (l2 ⊔ l3) R
  Π-algebra-Commutative-Ring =
    ( left-module-Π-algebra-Commutative-Ring ,
      bilinear-mul-Π-algebra-Commutative-Ring)
```

## See also

- [Function algebras over a commutative ring](commutative-algebra.function-algebras-commutative-rings.md)
