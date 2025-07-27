# Concrete automorphism groups on sets

```agda
module group-theory.loop-groups-sets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-truncated-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.univalence
open import foundation.universe-levels

open import group-theory.automorphism-groups
open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.monoids
open import group-theory.semigroups
open import group-theory.symmetric-groups
```

</details>

## Definitions

```agda
module _
  {l : Level} (X : Set l)
  where

  type-loop-Set : UU (lsuc l)
  type-loop-Set = Id (type-Set X) (type-Set X)

  is-set-type-loop-Set : is-set type-loop-Set
  is-set-type-loop-Set =
    is-trunc-id-is-trunc zero-𝕋 (is-set-type-Set X) (is-set-type-Set X)

  set-loop-Set : Set (lsuc l)
  pr1 set-loop-Set = type-loop-Set
  pr2 set-loop-Set = is-set-type-loop-Set

  has-associative-mul-loop-Set : has-associative-mul-Set (set-loop-Set)
  pr1 has-associative-mul-loop-Set = _∙_
  pr2 has-associative-mul-loop-Set = assoc

  loop-semigroup-Set : Semigroup (lsuc l)
  pr1 loop-semigroup-Set = set-loop-Set
  pr2 loop-semigroup-Set = has-associative-mul-loop-Set

  is-unital-Semigroup-loop-semigroup-Set :
    is-unital-Semigroup loop-semigroup-Set
  pr1 is-unital-Semigroup-loop-semigroup-Set = refl
  pr1 (pr2 is-unital-Semigroup-loop-semigroup-Set) y = left-unit
  pr2 (pr2 is-unital-Semigroup-loop-semigroup-Set) x = right-unit

  is-group-loop-semigroup-Set' :
    is-group-is-unital-Semigroup
      ( loop-semigroup-Set)
      ( is-unital-Semigroup-loop-semigroup-Set)
  pr1 is-group-loop-semigroup-Set' = inv
  pr1 (pr2 is-group-loop-semigroup-Set') = left-inv
  pr2 (pr2 is-group-loop-semigroup-Set') = right-inv

  loop-group-Set : Group (lsuc l)
  pr1 loop-group-Set = loop-semigroup-Set
  pr1 (pr2 loop-group-Set) = is-unital-Semigroup-loop-semigroup-Set
  pr2 (pr2 loop-group-Set) = is-group-loop-semigroup-Set'
```

## Properties

### The symmetry group and the loop group of a set are isomorphic

```agda
module _
  {l : Level}
  where

  map-hom-symmetric-group-loop-group-Set :
    (X Y : Set l) →
    Id (type-Set X) (type-Set Y) → (type-Set Y) ≃ (type-Set X)
  map-hom-symmetric-group-loop-group-Set X Y p = equiv-eq (inv p)

  map-hom-inv-symmetric-group-loop-group-Set :
    (X Y : Set l) →
    (type-Set X) ≃ (type-Set Y) → Id (type-Set Y) (type-Set X)
  map-hom-inv-symmetric-group-loop-group-Set X Y f = inv (eq-equiv f)

  commutative-inv-map-hom-symmetric-group-loop-group-Set :
    (X Y : UU l) (p : Id X Y) (sX : is-set X) (sY : is-set Y) →
    Id
      ( map-hom-symmetric-group-loop-group-Set (Y , sY) (X , sX) (inv p))
      ( inv-equiv
        ( map-hom-symmetric-group-loop-group-Set (X , sX) (Y , sY) p))
  commutative-inv-map-hom-symmetric-group-loop-group-Set X .X refl sX sY =
    ( inv (right-inverse-law-equiv id-equiv)) ∙
    ( left-unit-law-equiv (inv-equiv id-equiv))

module _
  {l : Level} (X : Set l)
  where

  hom-symmetric-group-loop-group-Set :
    hom-Group (loop-group-Set X) (symmetric-Group X)
  pr1 hom-symmetric-group-loop-group-Set =
    map-hom-symmetric-group-loop-group-Set X X
  pr2 hom-symmetric-group-loop-group-Set {p} {q} =
    ( ap equiv-eq (distributive-inv-concat p q)) ∙
    ( inv (compute-equiv-eq-concat (inv q) (inv p)))

  hom-inv-symmetric-group-loop-group-Set :
    hom-Group (symmetric-Group X) (loop-group-Set X)
  pr1 hom-inv-symmetric-group-loop-group-Set =
    map-hom-inv-symmetric-group-loop-group-Set X X
  pr2 hom-inv-symmetric-group-loop-group-Set {f} {g} =
    ( ap inv (inv (compute-eq-equiv-comp-equiv g f))) ∙
    ( distributive-inv-concat (eq-equiv g) (eq-equiv f))

  is-section-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( hom-symmetric-group-loop-group-Set)
        ( hom-inv-symmetric-group-loop-group-Set))
      ( id-hom-Group (symmetric-Group X))
  is-section-hom-inv-symmetric-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ f →
          ( ap equiv-eq (inv-inv (eq-equiv f))) ∙
            ( ap
              ( λ e → map-equiv e f)
              ( right-inverse-law-equiv equiv-univalence))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group X))
          ( semigroup-Group (symmetric-Group X))
          ( id)))

  is-retraction-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( hom-inv-symmetric-group-loop-group-Set)
        ( hom-symmetric-group-loop-group-Set))
      ( id-hom-Group (loop-group-Set X))
  is-retraction-hom-inv-symmetric-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( inv)
            ( ap
              ( λ e → map-equiv e (inv p))
              ( left-inverse-law-equiv equiv-univalence))) ∙
            ( inv-inv p)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set X))
          ( semigroup-Group (loop-group-Set X))
          ( id)))

  iso-symmetric-group-loop-group-Set :
    iso-Group (loop-group-Set X) (symmetric-Group X)
  pr1 iso-symmetric-group-loop-group-Set = hom-symmetric-group-loop-group-Set
  pr1 (pr2 iso-symmetric-group-loop-group-Set) =
    hom-inv-symmetric-group-loop-group-Set
  pr1 (pr2 (pr2 iso-symmetric-group-loop-group-Set)) =
    is-section-hom-inv-symmetric-group-loop-group-Set
  pr2 (pr2 (pr2 iso-symmetric-group-loop-group-Set)) =
    is-retraction-hom-inv-symmetric-group-loop-group-Set
```

### The abstracted automorphism group and the loop group of a set are isomorphic

```agda
module _
  {l : Level} (X : Set l)
  where

  hom-abstract-automorphism-group-loop-group-Set :
    hom-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
  pr1 hom-abstract-automorphism-group-loop-group-Set p =
    eq-pair-Σ
      ( eq-pair-Σ
        ( p)
        ( eq-is-prop (is-prop-is-set (type-Set X))))
      ( eq-is-prop is-prop-type-trunc-Prop)
  pr2 hom-abstract-automorphism-group-loop-group-Set {p} {q} =
    ( ap
      ( λ r → eq-pair-Σ r (eq-is-prop is-prop-type-trunc-Prop))
      ( ( ap
          ( λ w → eq-pair-Σ (p ∙ q) w)
          ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set X) _ _)))) ∙
        ( interchange-concat-eq-pair-Σ
          ( p)
          ( q)
          ( eq-is-prop (is-prop-is-set (type-Set X)))
          ( eq-is-prop (is-prop-is-set (type-Set X)))))) ∙
    ( ap
      ( λ w →
        eq-pair-Σ
          ( ( eq-pair-Σ p (eq-is-prop (is-prop-is-set (pr1 X)))) ∙
            ( eq-pair-Σ q (eq-is-prop (is-prop-is-set (pr1 X)))))
          ( w))
      ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
    ( interchange-concat-eq-pair-Σ
      ( eq-pair-Σ p (eq-is-prop (is-prop-is-set (type-Set X))))
      ( eq-pair-Σ q (eq-is-prop (is-prop-is-set (type-Set X))))
      ( eq-is-prop is-prop-type-trunc-Prop)
      ( eq-is-prop is-prop-type-trunc-Prop))

  hom-inv-abstract-automorphism-group-loop-group-Set :
    hom-Group
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
      ( loop-group-Set X)
  pr1 hom-inv-abstract-automorphism-group-loop-group-Set p =
    pr1 (pair-eq-Σ (pr1 (pair-eq-Σ p)))
  pr2 hom-inv-abstract-automorphism-group-loop-group-Set {p} {q} =
    ( ap
      ( λ r → pr1 (pair-eq-Σ r))
      ( pr1-interchange-concat-pair-eq-Σ p q)) ∙
    ( pr1-interchange-concat-pair-eq-Σ (pr1 (pair-eq-Σ p)) (pr1 (pair-eq-Σ q)))

  is-section-hom-inv-abstract-automorphism-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X))
        ( loop-group-Set X)
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X))
        ( hom-abstract-automorphism-group-loop-group-Set)
        ( hom-inv-abstract-automorphism-group-loop-group-Set))
      ( id-hom-Group
        ( group-Concrete-Group
          ( Automorphism-Group (Set-1-Type l) X)))
  is-section-hom-inv-abstract-automorphism-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ r (eq-is-prop is-prop-type-trunc-Prop))
            ( ( ap
                ( eq-pair-Σ (pr1 (pair-eq-Σ (pr1 (pair-eq-Σ p)))))
                ( eq-is-prop (is-trunc-Id (is-prop-is-set (type-Set X) _ _)))) ∙
              ( is-section-pair-eq-Σ X X (pr1 (pair-eq-Σ p))))) ∙
          ( ap
            ( eq-pair-Σ (pr1 (pair-eq-Σ p)))
            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
          ( is-section-pair-eq-Σ
            ( X , unit-trunc-Prop refl)
            ( X , unit-trunc-Prop refl)
            ( p))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group
            ( group-Concrete-Group
              ( Automorphism-Group (Set-1-Type l) X)))
          ( semigroup-Group
            ( group-Concrete-Group
              ( Automorphism-Group (Set-1-Type l) X)))
          ( id)))

  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Set :
    comp-hom-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
      ( loop-group-Set X)
      ( hom-inv-abstract-automorphism-group-loop-group-Set)
      ( hom-abstract-automorphism-group-loop-group-Set) ＝
    id-hom-Group (loop-group-Set X)
  is-retraction-hom-inv-abstract-automorphism-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ w → pr1 (pair-eq-Σ (pr1 w)))
            ( is-retraction-pair-eq-Σ
              ( X , unit-trunc-Prop refl)
              ( X , unit-trunc-Prop refl)
              ( pair
                ( eq-pair-Σ
                  ( p)
                  ( eq-is-prop (is-prop-is-set (type-Set X))))
                ( eq-is-prop is-prop-type-trunc-Prop)))) ∙
            ( ap pr1
              ( is-retraction-pair-eq-Σ X X
                ( p , eq-is-prop (is-prop-is-set (type-Set X)))))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set X))
          ( semigroup-Group (loop-group-Set X))
          ( id)))

  iso-abstract-automorphism-group-loop-group-Set :
    iso-Group
      ( loop-group-Set X)
      ( group-Concrete-Group
        ( Automorphism-Group (Set-1-Type l) X))
  pr1 iso-abstract-automorphism-group-loop-group-Set =
    hom-abstract-automorphism-group-loop-group-Set
  pr1 (pr2 iso-abstract-automorphism-group-loop-group-Set) =
    hom-inv-abstract-automorphism-group-loop-group-Set
  pr1 (pr2 (pr2 iso-abstract-automorphism-group-loop-group-Set)) =
    is-section-hom-inv-abstract-automorphism-group-loop-group-Set
  pr2 (pr2 (pr2 iso-abstract-automorphism-group-loop-group-Set)) =
    is-retraction-hom-inv-abstract-automorphism-group-loop-group-Set
```

### The loop groups of two equivalent sets are isomorphic

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) (e : type-Set X ≃ type-Set Y)
  where

  iso-loop-group-equiv-Set :
    iso-Group
      ( loop-group-Set X)
      ( loop-group-Set Y)
  iso-loop-group-equiv-Set =
    comp-iso-Group
      ( loop-group-Set X)
      ( symmetric-Group X)
      ( loop-group-Set Y)
      ( comp-iso-Group
        ( symmetric-Group X)
        ( symmetric-Group Y)
        ( loop-group-Set Y)
        ( inv-iso-Group
          ( loop-group-Set Y)
          ( symmetric-Group Y)
          ( iso-symmetric-group-loop-group-Set Y))
        ( iso-symmetric-group-equiv-Set X Y e))
      ( iso-symmetric-group-loop-group-Set X)
```
