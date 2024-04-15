# Cartesian products of set quotients

```agda
module foundation.cartesian-products-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality
open import foundation.products-equivalence-relations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Given two types `A` and `B`, equipped with equivalence relations `R` and `S`,
respectively, the cartesian product of their set quotients is the set quotient
of their product.

## Definition

### The product of two relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  where

  product-set-quotient-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  product-set-quotient-Set = product-Set (quotient-Set R) (quotient-Set S)

  product-set-quotient : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  product-set-quotient = pr1 product-set-quotient-Set

  is-set-product-set-quotient : is-set product-set-quotient
  is-set-product-set-quotient = pr2 product-set-quotient-Set

  product-set-quotient-map : (A × B) → product-set-quotient
  product-set-quotient-map (a , b) =
    pair (quotient-map R a) (quotient-map S b)

  reflecting-map-product-quotient-map :
    reflecting-map-equivalence-relation
      ( product-equivalence-relation R S)
      ( product-set-quotient)
  reflecting-map-product-quotient-map =
    pair
      product-set-quotient-map
      ( λ (p , q) →
        ( eq-pair
          ( apply-effectiveness-quotient-map' R p)
          ( apply-effectiveness-quotient-map' S q)))
```

## Properties

### The product of sets quotients is a set quotient

```agda
  inv-precomp-set-quotient-product-set-quotient :
    {l : Level}
    (X : Set l) →
    reflecting-map-equivalence-relation
      ( product-equivalence-relation R S)
      ( type-Set X) →
    hom-Set product-set-quotient-Set X
  inv-precomp-set-quotient-product-set-quotient X (f , H) (qa , qb) =
    inv-precomp-set-quotient
      ( R)
      ( hom-set-Set (quotient-Set S) X)
      ( pair
        ( λ a qb' →
          inv-precomp-set-quotient S X
            ( pair
              (λ b → f (a , b))
              (λ p → H (refl-equivalence-relation R a , p)))
            qb')
        ( λ {a1} {a2} p →
          ( ap (inv-precomp-set-quotient S X)
            ( eq-pair-Σ
              ( eq-htpy (λ b → H (p , refl-equivalence-relation S b)))
              ( eq-is-prop
                ( is-prop-reflects-equivalence-relation S X _))))))
      ( qa)
      ( qb)

  is-section-inv-precomp-set-quotient-product-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( precomp-Set-Quotient
      ( product-equivalence-relation R S)
      ( product-set-quotient-Set)
      ( reflecting-map-product-quotient-map)
      ( X) ∘
      ( inv-precomp-set-quotient-product-set-quotient X)) ~
    ( id)
  is-section-inv-precomp-set-quotient-product-set-quotient X (f , H) =
    eq-pair-Σ
      ( eq-htpy
        ( λ (a , b) →
          ( htpy-eq
            ( is-section-inv-precomp-set-quotient R
              ( hom-set-Set (quotient-Set S) X) _ a)
            ( quotient-map S b) ∙
          ( is-section-inv-precomp-set-quotient S X _ b))))
      ( eq-is-prop
        ( is-prop-reflects-equivalence-relation
          ( product-equivalence-relation R S) X f))

  is-retraction-inv-precomp-set-quotient-product-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( ( inv-precomp-set-quotient-product-set-quotient X) ∘
      ( precomp-Set-Quotient
        ( product-equivalence-relation R S)
        ( product-set-quotient-Set)
        ( reflecting-map-product-quotient-map)
        ( X))) ~
    ( id)
  is-retraction-inv-precomp-set-quotient-product-set-quotient X f =
    ( eq-htpy
      ( λ (qa , qb) →
        htpy-eq
        ( htpy-eq
          ( ap
            ( inv-precomp-set-quotient
              ( R)
              ( hom-set-Set (quotient-Set S) X))
              ( eq-pair-Σ
                ( eq-htpy λ a →
                  ( ap
                    ( inv-precomp-set-quotient S X)
                    ( eq-pair-eq-fiber
                      ( eq-is-prop
                        ( is-prop-reflects-equivalence-relation S X _)))) ∙
                    ( is-retraction-inv-precomp-set-quotient S X _))
                ( eq-is-prop
                  ( is-prop-reflects-equivalence-relation R
                    ( hom-set-Set (quotient-Set S) X) _))) ∙
            ( is-retraction-inv-precomp-set-quotient R
                ( hom-set-Set (quotient-Set S) X)
                ( λ qa qb → f (qa , qb))))
          ( qa))
          ( qb)))

  is-set-quotient-product-set-quotient :
    is-set-quotient
      ( product-equivalence-relation R S)
      ( product-set-quotient-Set)
      ( reflecting-map-product-quotient-map)
  pr1 (pr1 (is-set-quotient-product-set-quotient X)) =
    inv-precomp-set-quotient-product-set-quotient X
  pr2 (pr1 (is-set-quotient-product-set-quotient X)) =
    is-section-inv-precomp-set-quotient-product-set-quotient X
  pr1 (pr2 (is-set-quotient-product-set-quotient X)) =
    inv-precomp-set-quotient-product-set-quotient X
  pr2 (pr2 (is-set-quotient-product-set-quotient X)) =
    is-retraction-inv-precomp-set-quotient-product-set-quotient X

  quotient-product : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-product = quotient-Set (product-equivalence-relation R S)

  type-quotient-product : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-quotient-product = pr1 quotient-product

  equiv-quotient-product-product-set-quotient :
    product-set-quotient ≃ type-Set (quotient-product)
  equiv-quotient-product-product-set-quotient =
    equiv-uniqueness-set-quotient
      ( product-equivalence-relation R S)
      ( product-set-quotient-Set)
      ( reflecting-map-product-quotient-map)
      ( is-set-quotient-product-set-quotient)
      ( quotient-product)
      ( reflecting-map-quotient-map (product-equivalence-relation R S))
      ( is-set-quotient-set-quotient (product-equivalence-relation R S))

  triangle-uniqueness-product-set-quotient :
    ( map-equiv equiv-quotient-product-product-set-quotient ∘
      product-set-quotient-map) ~
    quotient-map (product-equivalence-relation R S)
  triangle-uniqueness-product-set-quotient =
    triangle-uniqueness-set-quotient
      ( product-equivalence-relation R S)
      ( product-set-quotient-Set)
      ( reflecting-map-product-quotient-map)
      ( is-set-quotient-product-set-quotient)
      ( quotient-product)
      ( reflecting-map-quotient-map (product-equivalence-relation R S))
      ( is-set-quotient-set-quotient (product-equivalence-relation R S))
```
