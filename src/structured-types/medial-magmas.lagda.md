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

open import structured-types.h-spaces
open import structured-types.magmas
open import structured-types.morphisms-h-spaces
open import structured-types.morphisms-magmas
open import structured-types.product-magmas
```

</details>

## Idea

Multiplication in a [magma](structured-types.magmas.md) `M` induces by
[uncurrying](foundation.universal-property-cartesian-product-types.md) a map
`M × M → M, (x , y) ↦ mul-Magma M x y`. `M` is
{{#concept "medial" Disambiguation="magma" Agda=is-medial-Magma WD="medial magma" WDID=Q6806018}}
if this map is a [morphism](structured-types.morphisms-magmas.md) from the
[product magma](structured-types.product-magmas.md): in other words, if the
equality

```text
(x * u) * (y * v) = (x * y) * (u * v)
```

is satisfied for all elements `x y u v : M`.

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

In traditional set-level mathematics, the carrier type for a magma is assumed to
be a set, in which case being medial is a property of a magma rather than
structure. In the absence of this assumption, there may be several homotopies
witnessing medial-ness of `M`, and thus the commutators and associators defined
below are not necessarily unique and should be thought of as additional
structure on `M`, potentially subject to coherence conditions and so on.

```agda
module _
  {l : Level} (M : H-Space l) (med-M : is-medial-Magma (magma-H-Space M))
  where

  commutator-medial-H-Space :
    (x y : type-H-Space M) → mul-H-Space M x y ＝ mul-H-Space M y x
  commutator-medial-H-Space x y = equational-reasoning
    mul-H-Space M x y
    ＝ ( mul-H-Space M
        ( mul-uncurry-Magma (magma-H-Space M) (unit-H-Space M , x))
        ( mul-uncurry-Magma (magma-H-Space M) (y , unit-H-Space M)))
      by
        ap-binary
          ( mul-H-Space M)
          ( inv (left-unit-law-mul-H-Space M x))
          ( inv (right-unit-law-mul-H-Space M y))
    ＝ ( mul-H-Space M
        ( mul-uncurry-Magma (magma-H-Space M) (unit-H-Space M , y))
        ( mul-uncurry-Magma (magma-H-Space M) (x , unit-H-Space M)))
      by med-M (unit-H-Space M , y) (x , unit-H-Space M)
    ＝ mul-H-Space M y x
      by
        ap-binary
          ( mul-H-Space M)
          ( left-unit-law-mul-H-Space M y)
          ( right-unit-law-mul-H-Space M x)

  associator-medial-H-Space :
    ( x y z : type-H-Space M) →
    mul-H-Space M (mul-H-Space M x y) z ＝ mul-H-Space M x (mul-H-Space M y z)
  associator-medial-H-Space x y z = equational-reasoning
    mul-H-Space M (mul-H-Space M x y) z
    ＝ mul-H-Space M (mul-H-Space M x y) (mul-H-Space M (unit-H-Space M) z)
      by ap-binary (mul-H-Space M) refl (inv (left-unit-law-mul-H-Space M z))
    ＝ mul-H-Space M (mul-H-Space M x (unit-H-Space M)) (mul-H-Space M y z)
      by med-M (x , unit-H-Space M) (y , z)
    ＝ mul-H-Space M x (mul-H-Space M y z)
      by ap-binary (mul-H-Space M) (right-unit-law-mul-H-Space M x) refl
```

### The commutative monoid of a medial H-space

```agda
module _
  {l : Level} (M : H-Space l) (med-M : is-medial-Magma (magma-H-Space M))
  where

  is-commutative-monoid-medial-H-Space :
    is-commutative-monoid-Magma (magma-H-Space M)
  pr1 (pr1 is-commutative-monoid-medial-H-Space) =
    associator-medial-H-Space M med-M
  pr2 (pr1 is-commutative-monoid-medial-H-Space) =
    unit-H-Space M , left-unit-law-mul-H-Space M , right-unit-law-mul-H-Space M
  pr2 is-commutative-monoid-medial-H-Space = commutator-medial-H-Space M med-M
```

## External links

- [Medial magmas](https://en.wikipedia.org/wiki/Medial_magma) at Wikipedia
