# Quotients of left modules over rings

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.quotients-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.functoriality-set-quotients
open import foundation.identity-types
open import foundation.set-quotients
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.quotients-abelian-groups
open import group-theory.subgroups-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.left-submodules-rings
open import linear-algebra.linear-maps-left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

Given a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R`, and a
[submodule](linear-algebra.left-submodules-rings.md) `N` of `M`, the
{{#concept "quotient module" Disambiguation="of left modules over rings"}} `M/N`
is the [quotient group](group-theory.quotients-abelian-groups.md) `M/N` equipped
with the induced scalar multiplication operation to make it a left module over
`R`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-submodule-Ring l3 R M)
  where

  ab-quotient-left-module-Ring : Ab (l2 ⊔ l3)
  ab-quotient-left-module-Ring =
    quotient-Ab
      ( ab-left-module-Ring R M)
      ( subgroup-ab-left-submodule-Ring R M N)

  set-quotient-left-module-Ring : Set (l2 ⊔ l3)
  set-quotient-left-module-Ring = set-Ab ab-quotient-left-module-Ring

  type-quotient-left-module-Ring : UU (l2 ⊔ l3)
  type-quotient-left-module-Ring = type-Ab ab-quotient-left-module-Ring

  map-quotient-hom-left-module-Ring :
    type-left-module-Ring R M → type-quotient-left-module-Ring
  map-quotient-hom-left-module-Ring =
    map-quotient-hom-Ab
      ( ab-left-module-Ring R M)
      ( subgroup-ab-left-submodule-Ring R M N)

  add-quotient-left-module-Ring :
    type-quotient-left-module-Ring → type-quotient-left-module-Ring →
    type-quotient-left-module-Ring
  add-quotient-left-module-Ring = add-Ab ab-quotient-left-module-Ring

  abstract
    compute-add-quotient-left-module-Ring :
      (x y : type-left-module-Ring R M) →
      add-quotient-left-module-Ring
        ( map-quotient-hom-left-module-Ring x)
        ( map-quotient-hom-left-module-Ring y) ＝
      map-quotient-hom-left-module-Ring (add-left-module-Ring R M x y)
    compute-add-quotient-left-module-Ring =
      compute-add-quotient-Ab
        ( ab-left-module-Ring R M)
        ( subgroup-ab-left-submodule-Ring R M N)

  equivalence-relation-congruence-left-submodule-Ring :
    equivalence-relation l3 (type-left-module-Ring R M)
  equivalence-relation-congruence-left-submodule-Ring =
    equivalence-relation-congruence-Subgroup-Ab
      ( ab-left-module-Ring R M)
      ( subgroup-ab-left-submodule-Ring R M N)

  hom-mul-quotient-left-module-Ring :
    type-Ring R →
    hom-equivalence-relation
      ( equivalence-relation-congruence-left-submodule-Ring)
      ( equivalence-relation-congruence-left-submodule-Ring)
  pr1 (hom-mul-quotient-left-module-Ring r) = mul-left-module-Ring R M r
  pr2 (hom-mul-quotient-left-module-Ring r) {x} {y} x~y =
    tr
      ( is-in-left-submodule-Ring R M N)
      ( equational-reasoning
        mul-left-module-Ring R M
          ( r)
          ( add-left-module-Ring R M (neg-left-module-Ring R M x) y)
        ＝
          add-left-module-Ring R M
            ( mul-left-module-Ring R M r (neg-left-module-Ring R M x))
            ( mul-left-module-Ring R M r y)
          by left-distributive-mul-add-left-module-Ring R M r _ y
        ＝
          add-left-module-Ring R M
            ( neg-left-module-Ring R M (mul-left-module-Ring R M r x))
            ( mul-left-module-Ring R M r y)
          by
            ap-add-left-module-Ring R M
              ( right-negative-law-mul-left-module-Ring R M r x)
              ( refl))
      ( is-closed-under-scalar-multiplication-left-submodule-Ring
        ( R)
        ( M)
        ( N)
        ( r)
        ( _)
        ( x~y))

  mul-quotient-left-module-Ring :
    type-Ring R →
    type-quotient-left-module-Ring → type-quotient-left-module-Ring
  mul-quotient-left-module-Ring r =
    map-set-quotient
      ( equivalence-relation-congruence-left-submodule-Ring)
      ( equivalence-relation-congruence-left-submodule-Ring)
      ( hom-mul-quotient-left-module-Ring r)

  abstract
    compute-mul-quotient-left-module-Ring :
      (r : type-Ring R) (x : type-left-module-Ring R M) →
      mul-quotient-left-module-Ring
        ( r)
        ( map-quotient-hom-left-module-Ring x) ＝
      map-quotient-hom-left-module-Ring (mul-left-module-Ring R M r x)
    compute-mul-quotient-left-module-Ring r =
      coherence-square-map-set-quotient
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( hom-mul-quotient-left-module-Ring r)

    left-distributive-mul-add-quotient-left-module-Ring :
      (r : type-Ring R) (x y : type-quotient-left-module-Ring) →
      mul-quotient-left-module-Ring r (add-quotient-left-module-Ring x y) ＝
      add-quotient-left-module-Ring
        ( mul-quotient-left-module-Ring r x)
        ( mul-quotient-left-module-Ring r y)
    left-distributive-mul-add-quotient-left-module-Ring r =
      double-induction-set-quotient'
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( λ x y →
          Id-Prop
            ( set-quotient-left-module-Ring)
            ( mul-quotient-left-module-Ring
              ( r)
              ( add-quotient-left-module-Ring x y))
            ( add-quotient-left-module-Ring
              ( mul-quotient-left-module-Ring r x)
              ( mul-quotient-left-module-Ring r y)))
        ( λ x y →
          ( ap
            ( mul-quotient-left-module-Ring r)
            ( compute-add-quotient-left-module-Ring x y)) ∙
          ( compute-mul-quotient-left-module-Ring r _) ∙
          ( ap
            ( map-quotient-hom-left-module-Ring)
            ( left-distributive-mul-add-left-module-Ring R M r x y)) ∙
          ( inv (compute-add-quotient-left-module-Ring _ _)) ∙
          ( ap-binary
            ( add-quotient-left-module-Ring)
            ( inv (compute-mul-quotient-left-module-Ring r x))
            ( inv (compute-mul-quotient-left-module-Ring r y))))

    right-distributive-mul-add-quotient-left-module-Ring :
      (r s : type-Ring R) (x : type-quotient-left-module-Ring) →
      mul-quotient-left-module-Ring (add-Ring R r s) x ＝
      add-quotient-left-module-Ring
        ( mul-quotient-left-module-Ring r x)
        ( mul-quotient-left-module-Ring s x)
    right-distributive-mul-add-quotient-left-module-Ring r s =
      induction-set-quotient
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( λ x →
          Id-Prop
            ( set-quotient-left-module-Ring)
            ( mul-quotient-left-module-Ring (add-Ring R r s) x)
            ( add-quotient-left-module-Ring
              ( mul-quotient-left-module-Ring r x)
              ( mul-quotient-left-module-Ring s x)))
        ( λ x →
          ( compute-mul-quotient-left-module-Ring _ x) ∙
          ( ap
            ( map-quotient-hom-left-module-Ring)
            ( right-distributive-mul-add-left-module-Ring R M r s x)) ∙
          ( inv (compute-add-quotient-left-module-Ring _ _)) ∙
          ( ap-binary
            ( add-quotient-left-module-Ring)
            ( inv (compute-mul-quotient-left-module-Ring r x))
            ( inv (compute-mul-quotient-left-module-Ring s x))))

    left-unit-law-mul-quotient-left-module-Ring :
      (x : type-quotient-left-module-Ring) →
      mul-quotient-left-module-Ring (one-Ring R) x ＝ x
    left-unit-law-mul-quotient-left-module-Ring =
      induction-set-quotient
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( λ x →
          Id-Prop
            ( set-quotient-left-module-Ring)
            ( mul-quotient-left-module-Ring (one-Ring R) x)
            ( x))
        ( λ x →
          ( compute-mul-quotient-left-module-Ring (one-Ring R) x) ∙
          ( ap
            ( map-quotient-hom-left-module-Ring)
            ( left-unit-law-mul-left-module-Ring R M x)))

    associative-mul-quotient-left-module-Ring :
      (r s : type-Ring R) (x : type-quotient-left-module-Ring) →
      mul-quotient-left-module-Ring (mul-Ring R r s) x ＝
      mul-quotient-left-module-Ring r (mul-quotient-left-module-Ring s x)
    associative-mul-quotient-left-module-Ring r s =
      induction-set-quotient
        ( equivalence-relation-congruence-left-submodule-Ring)
        ( λ x →
          Id-Prop
            ( set-quotient-left-module-Ring)
            ( mul-quotient-left-module-Ring (mul-Ring R r s) x)
            ( mul-quotient-left-module-Ring
              ( r)
              ( mul-quotient-left-module-Ring s x)))
        ( λ x →
          ( compute-mul-quotient-left-module-Ring (mul-Ring R r s) _) ∙
          ( ap
            ( map-quotient-hom-left-module-Ring)
            ( associative-mul-left-module-Ring R M r s x)) ∙
          ( inv (compute-mul-quotient-left-module-Ring r _)) ∙
          ( ap
            ( mul-quotient-left-module-Ring r)
            ( inv (compute-mul-quotient-left-module-Ring s x))))

  quotient-left-module-Ring : left-module-Ring (l2 ⊔ l3) R
  quotient-left-module-Ring =
    make-left-module-Ring
      ( R)
      ( ab-quotient-left-module-Ring)
      ( mul-quotient-left-module-Ring)
      ( left-distributive-mul-add-quotient-left-module-Ring)
      ( right-distributive-mul-add-quotient-left-module-Ring)
      ( left-unit-law-mul-quotient-left-module-Ring)
      ( associative-mul-quotient-left-module-Ring)
```

## Properties

### The linear map from `M` to `M/N`

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (N : left-submodule-Ring l3 R M)
  where

  abstract
    is-additive-map-quotient-hom-left-module-Ring :
      is-additive-map-left-module-Ring
        ( R)
        ( M)
        ( quotient-left-module-Ring R M N)
        ( map-quotient-hom-left-module-Ring R M N)
    is-additive-map-quotient-hom-left-module-Ring x y =
      inv (compute-add-quotient-left-module-Ring R M N x y)

    is-homogeneous-map-quotient-hom-left-module-Ring :
      is-homogeneous-map-left-module-Ring
        ( R)
        ( M)
        ( quotient-left-module-Ring R M N)
        ( map-quotient-hom-left-module-Ring R M N)
    is-homogeneous-map-quotient-hom-left-module-Ring r x =
      inv (compute-mul-quotient-left-module-Ring R M N r x)

  linear-map-quotient-left-module-Ring :
    linear-map-left-module-Ring
      ( R)
      ( M)
      ( quotient-left-module-Ring R M N)
  linear-map-quotient-left-module-Ring =
    ( map-quotient-hom-left-module-Ring R M N ,
      is-additive-map-quotient-hom-left-module-Ring ,
      is-homogeneous-map-quotient-hom-left-module-Ring)
```

## External links

- [Quotient module](https://en.wikipedia.org/wiki/Quotient_module) on Wikipedia
- [Quotient module](https://ncatlab.org/nlab/show/quotient+module) on $n$Lab
