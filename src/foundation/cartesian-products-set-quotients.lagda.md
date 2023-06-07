# Cartesian products of set quotients

```agda
module foundation.cartesian-products-set-quotients where
```

<details><summary>Imports</summary>

```agda
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
open import foundation-core.functions
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
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  where

  prod-set-quotient-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient-Set = prod-Set (quotient-Set R) (quotient-Set S)

  prod-set-quotient : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  prod-set-quotient = pr1 prod-set-quotient-Set

  is-set-prod-set-quotient : is-set prod-set-quotient
  is-set-prod-set-quotient = pr2 prod-set-quotient-Set

  prod-set-quotient-map : (A × B) → prod-set-quotient
  prod-set-quotient-map (a , b) =
    pair (quotient-map R a) (quotient-map S b)

  reflecting-map-prod-quotient-map :
    reflecting-map-Eq-Rel (prod-Eq-Rel R S) prod-set-quotient
  reflecting-map-prod-quotient-map =
    pair
      prod-set-quotient-map
      ( λ (p , q) →
        ( eq-pair
          ( apply-effectiveness-quotient-map' R p)
          ( apply-effectiveness-quotient-map' S q)))
```

## Properties

### The product of sets quotients is a set quotient

```agda
  inv-precomp-set-quotient-prod-set-quotient :
    {l : Level}
    (X : Set l) →
    reflecting-map-Eq-Rel (prod-Eq-Rel R S) (type-Set X) →
    type-hom-Set prod-set-quotient-Set X
  inv-precomp-set-quotient-prod-set-quotient X (f , H) (qa , qb) =
    inv-precomp-set-quotient
      ( R)
      ( hom-Set (quotient-Set S) X)
      ( pair
        ( λ a qb' →
          inv-precomp-set-quotient S X
            ( pair
              (λ b → f (a , b))
              (λ p → H (pair (refl-Eq-Rel R) p)))
            qb')
        ( λ {a1} {a2} p →
          ( ap (inv-precomp-set-quotient S X)
            ( eq-pair-Σ
              ( eq-htpy (λ b → H (pair p (refl-Eq-Rel S))))
              ( eq-is-prop
                ( is-prop-reflects-Eq-Rel S X _))))))
      ( qa)
      ( qb)

  issec-inv-precomp-set-quotient-prod-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( precomp-Set-Quotient
      ( prod-Eq-Rel R S)
      ( prod-set-quotient-Set)
      ( reflecting-map-prod-quotient-map)
      ( X) ∘
      ( inv-precomp-set-quotient-prod-set-quotient X)) ~
    ( id)
  issec-inv-precomp-set-quotient-prod-set-quotient X (f , H) =
    eq-pair-Σ
      ( eq-htpy
        ( λ (a , b) →
          ( htpy-eq
            ( issec-inv-precomp-set-quotient R
              ( hom-Set (quotient-Set S) X) _ a)
            ( quotient-map S b) ∙
          ( issec-inv-precomp-set-quotient S X _ b))))
      ( eq-is-prop
        ( is-prop-reflects-Eq-Rel (prod-Eq-Rel R S) X f))

  isretr-inv-precomp-set-quotient-prod-set-quotient :
    { l : Level}
    ( X : Set l) →
    ( ( inv-precomp-set-quotient-prod-set-quotient X) ∘
      ( precomp-Set-Quotient
        ( prod-Eq-Rel R S)
        ( prod-set-quotient-Set)
        ( reflecting-map-prod-quotient-map)
        ( X))) ~
    ( id)
  isretr-inv-precomp-set-quotient-prod-set-quotient X f =
    ( eq-htpy
      ( λ (qa , qb) →
        htpy-eq
        ( htpy-eq
          ( ap
            ( inv-precomp-set-quotient
              ( R)
              ( hom-Set (quotient-Set S) X))
              ( eq-pair-Σ
                ( eq-htpy λ a →
                  ( ap
                    ( inv-precomp-set-quotient S X)
                    ( eq-pair-Σ refl
                      ( eq-is-prop
                        ( is-prop-reflects-Eq-Rel S X _)))) ∙
                    ( isretr-inv-precomp-set-quotient S X _))
                ( eq-is-prop
                  ( is-prop-reflects-Eq-Rel R
                    (hom-Set (quotient-Set S) X) _))) ∙
            ( isretr-inv-precomp-set-quotient R
                ( hom-Set (quotient-Set S) X)
                ( λ qa qb → f (qa , qb))))
          ( qa))
          ( qb)))

  is-set-quotient-prod-set-quotient :
    { l : Level} →
    ( is-set-quotient l
      (prod-Eq-Rel R S)
      prod-set-quotient-Set
      reflecting-map-prod-quotient-map)
  pr1 (pr1 (is-set-quotient-prod-set-quotient X)) =
    inv-precomp-set-quotient-prod-set-quotient X
  pr2 (pr1 (is-set-quotient-prod-set-quotient X)) =
    issec-inv-precomp-set-quotient-prod-set-quotient X
  pr1 (pr2 (is-set-quotient-prod-set-quotient X)) =
    inv-precomp-set-quotient-prod-set-quotient X
  pr2 (pr2 (is-set-quotient-prod-set-quotient X)) =
    isretr-inv-precomp-set-quotient-prod-set-quotient X

  quotient-prod : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-prod = quotient-Set (prod-Eq-Rel R S)

  type-quotient-prod : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  type-quotient-prod = pr1 quotient-prod

  equiv-quotient-prod-prod-set-quotient :
    prod-set-quotient ≃ type-Set (quotient-prod)
  equiv-quotient-prod-prod-set-quotient =
    equiv-uniqueness-set-quotient
      ( prod-Eq-Rel R S)
      ( prod-set-quotient-Set)
      ( reflecting-map-prod-quotient-map)
      ( is-set-quotient-prod-set-quotient)
      ( quotient-prod)
      ( reflecting-map-quotient-map (prod-Eq-Rel R S))
      ( is-set-quotient-set-quotient (prod-Eq-Rel R S))

  triangle-uniqueness-prod-set-quotient :
    ( map-equiv equiv-quotient-prod-prod-set-quotient ∘
      prod-set-quotient-map) ~
    quotient-map (prod-Eq-Rel R S)
  triangle-uniqueness-prod-set-quotient =
    triangle-uniqueness-set-quotient
      ( prod-Eq-Rel R S)
      ( prod-set-quotient-Set)
      ( reflecting-map-prod-quotient-map)
      ( is-set-quotient-prod-set-quotient)
      ( quotient-prod)
      ( reflecting-map-quotient-map (prod-Eq-Rel R S))
      ( is-set-quotient-set-quotient (prod-Eq-Rel R S))
```
