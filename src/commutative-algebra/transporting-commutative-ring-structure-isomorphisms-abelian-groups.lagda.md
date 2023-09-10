# Transporting commutative ring structures along isomorphisms of abelian groups

```agda
module
  commutative-algebra.transporting-commutative-ring-structure-isomorphisms-abelian-groups
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings
open import commutative-algebra.isomorphisms-commutative-rings

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.isomorphisms-abelian-groups
open import group-theory.semigroups

open import ring-theory.homomorphisms-rings
open import ring-theory.rings
open import ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groups
```

</details>

## Idea

If `A` is a [commutative ring](commutative-algebra.commutative-rings.md) and `B`
is an [abelian group](group-theory.abelian-groups.md) equipped with an
[isomorphism](group-theory.isomorphisms-abelian-groups.md) `A ≅ B` from the
additive abelian group of `A` to `B`, then the multiplicative structure of `A`
can be transported along the isomorphism to obtain a ring structure on `B`.

Note that this structure can be transported by
[univalence](foundation.univalence.md). However, we will give explicit
definitions, since univalence is not strictly necessary to obtain this
transported ring structure.

## Definitions

### Transporting the multiplicative structure of a commutative ring along an isomorphism of abelian groups

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (B : Ab l2)
  (f : type-iso-Ab (ab-Commutative-Ring A) B)
  where

  ring-transport-commutative-ring-structure-iso-Ab : Ring l2
  ring-transport-commutative-ring-structure-iso-Ab =
    transport-ring-structure-iso-Ab (ring-Commutative-Ring A) B f

  one-transport-commutative-ring-structure-iso-Ab : type-Ab B
  one-transport-commutative-ring-structure-iso-Ab =
    one-transport-ring-structure-iso-Ab (ring-Commutative-Ring A) B f

  mul-transport-commutative-ring-structure-iso-Ab :
    (x y : type-Ab B) → type-Ab B
  mul-transport-commutative-ring-structure-iso-Ab =
    mul-transport-ring-structure-iso-Ab (ring-Commutative-Ring A) B f

  private
    one = one-transport-commutative-ring-structure-iso-Ab
    mul = mul-transport-commutative-ring-structure-iso-Ab
    map-f = map-iso-Ab (ab-Commutative-Ring A) B f
    map-inv-f = map-inv-iso-Ab (ab-Commutative-Ring A) B f

  associative-mul-transport-commutative-ring-structure-iso-Ab :
    (x y z : type-Ab B) → mul (mul x y) z ＝ mul x (mul y z)
  associative-mul-transport-commutative-ring-structure-iso-Ab =
    associative-mul-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  left-unit-law-mul-transport-commutative-ring-structure-iso-Ab :
    (x : type-Ab B) → mul one x ＝ x
  left-unit-law-mul-transport-commutative-ring-structure-iso-Ab =
    left-unit-law-mul-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  right-unit-law-mul-transport-commutative-ring-structure-iso-Ab :
    (x : type-Ab B) → mul x one ＝ x
  right-unit-law-mul-transport-commutative-ring-structure-iso-Ab =
    right-unit-law-mul-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  left-distributive-mul-add-transport-commutative-ring-structure-iso-Ab :
    (x y z : type-Ab B) → mul x (add-Ab B y z) ＝ add-Ab B (mul x y) (mul x z)
  left-distributive-mul-add-transport-commutative-ring-structure-iso-Ab =
    left-distributive-mul-add-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  right-distributive-mul-add-transport-commutative-ring-structure-iso-Ab :
    (x y z : type-Ab B) → mul (add-Ab B x y) z ＝ add-Ab B (mul x z) (mul y z)
  right-distributive-mul-add-transport-commutative-ring-structure-iso-Ab =
    right-distributive-mul-add-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  commutative-mul-transport-commutative-ring-structure-iso-Ab :
    (x y : type-Ab B) → mul x y ＝ mul y x
  commutative-mul-transport-commutative-ring-structure-iso-Ab x y =
    ap map-f (commutative-mul-Commutative-Ring A _ _)

  transport-commutative-ring-structure-iso-Ab :
    Commutative-Ring l2
  pr1 transport-commutative-ring-structure-iso-Ab =
    ring-transport-commutative-ring-structure-iso-Ab
  pr2 transport-commutative-ring-structure-iso-Ab =
    commutative-mul-transport-commutative-ring-structure-iso-Ab

  preserves-mul-transport-commutative-ring-structure-iso-Ab :
    preserves-mul-hom-Ab
      ( ring-Commutative-Ring A)
      ( ring-transport-commutative-ring-structure-iso-Ab)
      ( hom-iso-Ab (ab-Commutative-Ring A) B f)
  preserves-mul-transport-commutative-ring-structure-iso-Ab =
    preserves-mul-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  hom-iso-transport-commutative-ring-structure-iso-Ab :
    type-hom-Commutative-Ring A transport-commutative-ring-structure-iso-Ab
  hom-iso-transport-commutative-ring-structure-iso-Ab =
    hom-iso-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  is-iso-iso-transport-commutative-ring-structure-iso-Ab :
    is-iso-hom-Commutative-Ring
      ( A)
      ( transport-commutative-ring-structure-iso-Ab)
      ( hom-iso-transport-commutative-ring-structure-iso-Ab)
  is-iso-iso-transport-commutative-ring-structure-iso-Ab =
    is-iso-iso-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)

  iso-transport-commutative-ring-structure-iso-Ab :
    iso-Commutative-Ring A transport-commutative-ring-structure-iso-Ab
  iso-transport-commutative-ring-structure-iso-Ab =
    iso-transport-ring-structure-iso-Ab
      ( ring-Commutative-Ring A)
      ( B)
      ( f)
```
