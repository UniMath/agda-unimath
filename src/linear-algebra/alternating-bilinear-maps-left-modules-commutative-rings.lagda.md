# Alternating bilinear maps on left modules over commutative rings

```agda
module linear-algebra.alternating-bilinear-maps-left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
```

</details>

## Idea

Given two [left modules](linear-algebra.left-modules-commutative-rings.md) `M`
and `N` over a [commutative ring](commutative-algebra.commutative-rings.md), a
[bilinear map](linear-algebra.bilinear-maps-left-modules-commutative-rings.md)
`f : M → M → N` is
{{#concept "alternating" Disambiguation="bilinear map between left modules on commutative rings" Agda=is-alternating-bilinear-map-left-module-Commutative-Ring}}
if for all `m : M`, `f m m = 0`.

As a corollary, alternating bilinear maps are antisymmetric:
`f m₁ m₂ = -(f m₂ m₁)`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  where

  is-alternating-prop-bilinear-map-left-module-Commutative-Ring :
    subtype
      ( l2 ⊔ l3)
      ( bilinear-map-left-module-Commutative-Ring R M M N)
  is-alternating-prop-bilinear-map-left-module-Commutative-Ring f =
    Π-Prop
      ( type-left-module-Commutative-Ring R M)
      ( λ m →
        is-zero-prop-left-module-Commutative-Ring R N
          ( map-bilinear-map-left-module-Commutative-Ring R M M N f m m))

  is-alternating-bilinear-map-left-module-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring R M M N → UU (l2 ⊔ l3)
  is-alternating-bilinear-map-left-module-Commutative-Ring =
    is-in-subtype is-alternating-prop-bilinear-map-left-module-Commutative-Ring

  alternating-bilinear-map-left-module-Commutative-Ring : UU (l1 ⊔ l2 ⊔ l3)
  alternating-bilinear-map-left-module-Commutative-Ring =
    type-subtype is-alternating-prop-bilinear-map-left-module-Commutative-Ring

  bilinear-map-alternating-bilinear-map-left-module-Commutative-Ring :
    alternating-bilinear-map-left-module-Commutative-Ring →
    bilinear-map-left-module-Commutative-Ring R M M N
  bilinear-map-alternating-bilinear-map-left-module-Commutative-Ring = pr1

  map-alternating-bilinear-map-left-module-Commutative-Ring :
    alternating-bilinear-map-left-module-Commutative-Ring →
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R M →
    type-left-module-Commutative-Ring R N
  map-alternating-bilinear-map-left-module-Commutative-Ring ((f , _) , _) = f
```

## Properties

### Alternating bilinear maps are antisymmetric

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  (N : left-module-Commutative-Ring l3 R)
  (af@(f@(map-f , _) , alt-f) :
    alternating-bilinear-map-left-module-Commutative-Ring R M N)
  (let _+M_ = add-left-module-Commutative-Ring R M)
  (let _+N_ = add-left-module-Commutative-Ring R N)
  (let 0N = zero-left-module-Commutative-Ring R N)
  where abstract

  is-antisymmetric-map-alternating-bilinear-map-left-module-Commutative-Ring :
    (m₁ m₂ : type-left-module-Commutative-Ring R M) →
    map-alternating-bilinear-map-left-module-Commutative-Ring R M N af m₁ m₂ ＝
    neg-left-module-Commutative-Ring R N
      (map-alternating-bilinear-map-left-module-Commutative-Ring R M N af m₂ m₁)
  is-antisymmetric-map-alternating-bilinear-map-left-module-Commutative-Ring
    m₁ m₂ =
    unique-left-neg-Ab
      ( ab-left-module-Commutative-Ring R N)
      ( _)
      ( _)
      ( equational-reasoning
        map-f m₁ m₂ +N map-f m₂ m₁
        ＝ (0N +N map-f m₁ m₂) +N (map-f m₂ m₁ +N 0N)
          by
            ap-add-left-module-Commutative-Ring R N
              ( inv (left-unit-law-add-left-module-Commutative-Ring R N _))
              ( inv (right-unit-law-add-left-module-Commutative-Ring R N _))
        ＝ (map-f m₁ m₁ +N map-f m₁ m₂) +N (map-f m₂ m₁ +N map-f m₂ m₂)
          by
            ap-add-left-module-Commutative-Ring R N
              ( ap-add-left-module-Commutative-Ring R N (inv (alt-f m₁)) refl)
              ( ap-add-left-module-Commutative-Ring R N refl (inv (alt-f m₂)))
        ＝ map-f m₁ (m₁ +M m₂) +N map-f m₂ (m₁ +M m₂)
          by
            ap-add-left-module-Commutative-Ring R N
              ( inv
                ( is-additive-map-ev-left-bilinear-map-left-module-Commutative-Ring
                  ( R)
                  ( M)
                  ( M)
                  ( N)
                  ( f)
                  ( m₁)
                  ( m₁)
                  ( m₂)))
              ( inv
                ( is-additive-map-ev-left-bilinear-map-left-module-Commutative-Ring
                  ( R)
                  ( M)
                  ( M)
                  ( N)
                  ( f)
                  ( m₂)
                  ( m₁)
                  ( m₂)))
        ＝ map-f (m₁ +M m₂) (m₁ +M m₂)
          by
            inv
              ( is-additive-map-ev-right-bilinear-map-left-module-Commutative-Ring
                ( R)
                ( M)
                ( M)
                ( N)
                ( f)
                ( m₁ +M m₂)
                ( m₁)
                ( m₂))
        ＝ 0N
          by alt-f (m₁ +M m₂))
```
