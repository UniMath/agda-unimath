# Transporting ring structures along isomorphisms of abelian groups

```agda
module
  ring-theory.transporting-ring-structure-along-isomorphisms-abelian-groups
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.isomorphisms-abelian-groups
open import group-theory.semigroups

open import ring-theory.homomorphisms-rings
open import ring-theory.isomorphisms-rings
open import ring-theory.rings
```

</details>

## Idea

If `R` is a [ring](ring-theory.rings.md) and `A` is an
[abelian group](group-theory.abelian-groups.md) equipped with an
[isomorphism](group-theory.isomorphisms-abelian-groups.md) `R ≅ A` from the
additive abelian group of `R` to `A`, then the multiplicative structure of `R`
can be transported along the isomorphism to obtain a ring structure on `A`.

Note that this structure can be transported by
[univalence](foundation.univalence.md). However, we will give explicit
definitions, since univalence is not necessary to obtain this transported ring
structure.

## Definitions

### Transporting the multiplicative structure of a ring along an isomorphism of abelian groups

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (A : Ab l2)
  (f : iso-Ab (ab-Ring R) A)
  where

  one-transport-ring-structure-iso-Ab : type-Ab A
  one-transport-ring-structure-iso-Ab =
    map-iso-Ab (ab-Ring R) A f (one-Ring R)

  mul-transport-ring-structure-iso-Ab :
    (x y : type-Ab A) → type-Ab A
  mul-transport-ring-structure-iso-Ab x y =
    map-iso-Ab (ab-Ring R) A f
      ( mul-Ring R
        ( map-inv-iso-Ab (ab-Ring R) A f x)
        ( map-inv-iso-Ab (ab-Ring R) A f y))

  private
    one = one-transport-ring-structure-iso-Ab
    mul = mul-transport-ring-structure-iso-Ab
    map-f = map-iso-Ab (ab-Ring R) A f
    map-inv-f = map-inv-iso-Ab (ab-Ring R) A f

  associative-mul-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul (mul x y) z ＝ mul x (mul y z)
  associative-mul-transport-ring-structure-iso-Ab x y z =
    ap
      ( map-f)
      ( ( ap (mul-Ring' R _) (is-retraction-map-inv-iso-Ab (ab-Ring R) A f _)) ∙
        ( ( associative-mul-Ring R _ _ _) ∙
          ( inv
            ( ap
              ( mul-Ring R _)
              ( is-retraction-map-inv-iso-Ab (ab-Ring R) A f _)))))

  left-unit-law-mul-transport-ring-structure-iso-Ab :
    (x : type-Ab A) → mul one x ＝ x
  left-unit-law-mul-transport-ring-structure-iso-Ab x =
    ( ap
      ( map-f)
      ( ( ap (mul-Ring' R _) (is-retraction-map-inv-iso-Ab (ab-Ring R) A f _)) ∙
        ( left-unit-law-mul-Ring R _))) ∙
    ( is-section-map-inv-iso-Ab (ab-Ring R) A f x)

  right-unit-law-mul-transport-ring-structure-iso-Ab :
    (x : type-Ab A) → mul x one ＝ x
  right-unit-law-mul-transport-ring-structure-iso-Ab x =
    ( ap
      ( map-f)
      ( ( ap (mul-Ring R _) (is-retraction-map-inv-iso-Ab (ab-Ring R) A f _)) ∙
        ( right-unit-law-mul-Ring R _))) ∙
    ( is-section-map-inv-iso-Ab (ab-Ring R) A f x)

  left-distributive-mul-add-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul x (add-Ab A y z) ＝ add-Ab A (mul x y) (mul x z)
  left-distributive-mul-add-transport-ring-structure-iso-Ab
    x y z =
    ( ap
      ( map-f)
      ( ( ap (mul-Ring R _) (preserves-add-inv-iso-Ab (ab-Ring R) A f)) ∙
        ( left-distributive-mul-add-Ring R _ _ _))) ∙
    ( preserves-add-iso-Ab (ab-Ring R) A f)

  right-distributive-mul-add-transport-ring-structure-iso-Ab :
    (x y z : type-Ab A) → mul (add-Ab A x y) z ＝ add-Ab A (mul x z) (mul y z)
  right-distributive-mul-add-transport-ring-structure-iso-Ab
    x y z =
    ( ap
      ( map-f)
      ( ( ap (mul-Ring' R _) (preserves-add-inv-iso-Ab (ab-Ring R) A f)) ∙
        ( right-distributive-mul-add-Ring R _ _ _))) ∙
    ( preserves-add-iso-Ab (ab-Ring R) A f)

  has-associative-mul-transport-ring-structure-iso-Ab :
    has-associative-mul-Set (set-Ab A)
  pr1 has-associative-mul-transport-ring-structure-iso-Ab =
    mul
  pr2 has-associative-mul-transport-ring-structure-iso-Ab =
    associative-mul-transport-ring-structure-iso-Ab

  is-unital-transport-ring-structure-iso-Ab :
    is-unital mul
  pr1 is-unital-transport-ring-structure-iso-Ab = one
  pr1 (pr2 is-unital-transport-ring-structure-iso-Ab) =
    left-unit-law-mul-transport-ring-structure-iso-Ab
  pr2 (pr2 is-unital-transport-ring-structure-iso-Ab) =
    right-unit-law-mul-transport-ring-structure-iso-Ab

  transport-ring-structure-iso-Ab : Ring l2
  pr1 transport-ring-structure-iso-Ab = A
  pr1 (pr2 transport-ring-structure-iso-Ab) =
    has-associative-mul-transport-ring-structure-iso-Ab
  pr1 (pr2 (pr2 transport-ring-structure-iso-Ab)) =
    is-unital-transport-ring-structure-iso-Ab
  pr1 (pr2 (pr2 (pr2 transport-ring-structure-iso-Ab))) =
    left-distributive-mul-add-transport-ring-structure-iso-Ab
  pr2 (pr2 (pr2 (pr2 transport-ring-structure-iso-Ab))) =
    right-distributive-mul-add-transport-ring-structure-iso-Ab

  preserves-mul-transport-ring-structure-iso-Ab :
    preserves-mul-hom-Ab
      ( R)
      ( transport-ring-structure-iso-Ab)
      ( hom-iso-Ab (ab-Ring R) A f)
  preserves-mul-transport-ring-structure-iso-Ab {x} {y} =
    ap map-f
      ( ap-mul-Ring R
        ( inv (is-retraction-map-inv-iso-Ab (ab-Ring R) A f x))
        ( inv (is-retraction-map-inv-iso-Ab (ab-Ring R) A f y)))

  hom-iso-transport-ring-structure-iso-Ab :
    hom-Ring R transport-ring-structure-iso-Ab
  pr1 hom-iso-transport-ring-structure-iso-Ab =
    hom-iso-Ab (ab-Ring R) A f
  pr1 (pr2 hom-iso-transport-ring-structure-iso-Ab) =
    preserves-mul-transport-ring-structure-iso-Ab
  pr2 (pr2 hom-iso-transport-ring-structure-iso-Ab) =
    refl

  is-iso-iso-transport-ring-structure-iso-Ab :
    is-iso-Ring
      ( R)
      ( transport-ring-structure-iso-Ab)
      ( hom-iso-transport-ring-structure-iso-Ab)
  is-iso-iso-transport-ring-structure-iso-Ab =
    is-iso-ring-is-iso-Ab
      ( R)
      ( transport-ring-structure-iso-Ab)
      ( hom-iso-transport-ring-structure-iso-Ab)
      ( is-iso-iso-Ab (ab-Ring R) A f)

  iso-transport-ring-structure-iso-Ab :
    iso-Ring R transport-ring-structure-iso-Ab
  pr1 (pr1 iso-transport-ring-structure-iso-Ab) = hom-iso-Ab (ab-Ring R) A f
  pr1 (pr2 (pr1 iso-transport-ring-structure-iso-Ab)) =
    preserves-mul-transport-ring-structure-iso-Ab
  pr2 (pr2 (pr1 iso-transport-ring-structure-iso-Ab)) =
    refl
  pr2 iso-transport-ring-structure-iso-Ab =
    is-iso-iso-transport-ring-structure-iso-Ab
```
