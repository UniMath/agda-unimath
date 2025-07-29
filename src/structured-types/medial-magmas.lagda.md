# Medial magmas

```agda
module structured-types.medial-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.magmas
open import structured-types.morphisms-magmas
open import structured-types.morphisms-h-spaces
open import structured-types.product-magmas
open import structured-types.h-spaces
```

</details>

## Idea

Multiplication in a [magma](structured-types.magmas.md) `M` induces by
uncurrying a map `M × M → M, (x , y) ↦ mul-Magma M x y`. `M` is
{{#concept "medial" Agda=is-medial-Magma}} if this map is a
[morphism](structured-types.morphisms-magmas.md) from the
[product magma](structured-types.product-magmas.md).

An [H-space](structured-types.h-spaces.md) is medial if and only if it is
commutative; this is the Eckmann-Hilton argument.

## Definition

```agda
module _
  {l : Level} (M : Magma l)
  where

  mul-uncurry-Magma : type-Magma M × type-Magma M → type-Magma M
  mul-uncurry-Magma (x , y) = mul-Magma M x y

  is-medial-Magma : UU l
  is-medial-Magma = preserves-mul-Magma (product-Magma M M) M mul-uncurry-Magma

medial-Magma : (l : Level) → UU (lsuc l)
medial-Magma l = Σ (Magma l) is-medial-Magma

module _
  {l : Level} (M : medial-Magma l)
  where

  magma-medial-Magma : Magma l
  magma-medial-Magma = pr1 M

  type-medial-Magma : UU l
  type-medial-Magma = type-Magma magma-medial-Magma

  mul-medial-Magma : type-medial-Magma → type-medial-Magma → type-medial-Magma
  mul-medial-Magma = mul-Magma magma-medial-Magma
```

## Properties

### Medial H-spaces are commutative and associative

As the binary homotopy showing `M` is medial is structure rather than a
property, so too should these commutators and associators be thought of as
structure. In principle, one may hope for an infinite tower of coherences
showing `M` to be something like an `E_n` space. This we do not formalize, as
the coherence problem for internal higher-algebraic structures in homotopy type
theory remains an open problem, but we note it for the interested reader.

```agda
module _
  {l : Level} (M : H-Space l) (med-M : is-medial-Magma (magma-H-Space M))
  where

  commutator-medial-H-Space :
    ( x y : type-H-Space M) → mul-H-Space M x y ＝ mul-H-Space M y x
  commutator-medial-H-Space x y = equational-reasoning
    mul-H-Space M x y
    ＝ mul-H-Space M (mul-uncurry-Magma (magma-H-Space M) (unit-H-Space M , x))
    ( mul-uncurry-Magma (magma-H-Space M) (y , unit-H-Space M))
      by ap-binary (mul-H-Space M) (inv (left-unit-law-mul-H-Space M x))
      ( inv (right-unit-law-mul-H-Space M y))
    ＝ mul-H-Space M (mul-uncurry-Magma (magma-H-Space M) (unit-H-Space M , y))
    ( mul-uncurry-Magma (magma-H-Space M) (x , unit-H-Space M))
      by med-M (pr2 (pr1 M) , y) (x , pr2 (pr1 M))
    ＝ mul-H-Space M (mul-uncurry-Magma (magma-H-Space M)
    ( unit-H-Space M , y)) x
      by ap (mul-H-Space M (mul-uncurry-Magma (magma-H-Space M)
      ( pr2 (pr1 M) , y))) (right-unit-law-mul-H-Space M x)
    ＝ mul-H-Space M y x
      by ap (λ z → mul-H-Space M z x) (left-unit-law-mul-H-Space M y)

  associator-medial-H-Space :
    ( x y z : type-H-Space M) →
    mul-H-Space M (mul-H-Space M x y) z ＝ mul-H-Space M x (mul-H-Space M y z)
  associator-medial-H-Space x y z = equational-reasoning
    mul-H-Space M (mul-H-Space M x y) z
    ＝ mul-H-Space M (mul-H-Space M x y) (mul-H-Space M (unit-H-Space M) z)
      by ap-binary (mul-H-Space M) refl (inv (left-unit-law-mul-H-Space M z))
    ＝ mul-H-Space M (mul-H-Space M x (unit-H-Space M)) (mul-H-Space M y z)
      by med-M (x , pr2 (pr1 M)) (y , z)
    ＝ mul-H-Space M x (mul-H-Space M y z)
      by ap-binary (mul-H-Space M) (right-unit-law-mul-H-Space M x) refl
```

## External links

- [Medial magmas](https://en.wikipedia.org/wiki/Medial_magma) at Wikipedia
