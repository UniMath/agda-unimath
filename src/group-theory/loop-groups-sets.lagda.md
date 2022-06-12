---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.loop-groups-sets where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; inv-equiv; id-equiv; left-inverse-law-equiv; right-inverse-law-equiv;
    left-unit-law-equiv; eq-htpy-equiv)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.functions using (id)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.homotopies using (refl-htpy)
open import foundation.identity-truncated-types using (is-trunc-id-is-trunc)
open import foundation.identity-types using
  ( Id; refl; _∙_; inv; ap; assoc; left-unit; right-unit; left-inv; right-inv;
    distributive-inv-concat; inv-inv)
open import foundation.propositions using (eq-is-prop)
open import foundation.sets using (UU-Set; is-set; type-Set; is-set-type-Set)
open import foundation.truncated-types using (is-trunc-is-emb)
open import foundation.truncation-levels using (zero-𝕋; neg-one-𝕋)
open import foundation.univalence using
  ( equiv-univalence; equiv-eq; eq-equiv; comp-eq-equiv; comp-equiv-eq)
open import foundation.universe-levels using (UU; Level; _⊔_; lsuc)

open import group-theory.groups using (Group; is-group'; semigroup-Group)
open import group-theory.homomorphisms-groups using
  ( type-hom-Group; comp-hom-Group; id-hom-Group)
open import group-theory.homomorphisms-semigroups using (is-prop-preserves-mul-Semigroup)
open import group-theory.isomorphisms-groups using (type-iso-Group)
open import group-theory.monoids using (is-unital-Semigroup)
open import group-theory.semigroups using (has-associative-mul-Set; Semigroup)
open import group-theory.symmetric-groups using (symmetric-Group)
```

## Idea

## Definitions
```agda
module _
  {l : Level} (X : UU-Set l)
  where

  type-loop-Set : UU (lsuc l)
  type-loop-Set = Id (type-Set X) (type-Set X)

  is-set-type-loop-Set : is-set type-loop-Set
  is-set-type-loop-Set =
    is-trunc-id-is-trunc zero-𝕋 (is-set-type-Set X) (is-set-type-Set X)

  set-loop-Set : UU-Set (lsuc l)
  pr1 set-loop-Set = type-loop-Set
  pr2 set-loop-Set = is-set-type-loop-Set

  has-associative-mul-loop-Set : has-associative-mul-Set (set-loop-Set)
  pr1 has-associative-mul-loop-Set = _∙_
  pr2 has-associative-mul-loop-Set = assoc

  loop-semigroup-Set : Semigroup (lsuc l)
  pr1 loop-semigroup-Set = set-loop-Set
  pr2 loop-semigroup-Set = has-associative-mul-loop-Set

  is-unital-Semigroup-loop-semigroup-Set : is-unital-Semigroup loop-semigroup-Set
  pr1 is-unital-Semigroup-loop-semigroup-Set = refl
  pr1 (pr2 is-unital-Semigroup-loop-semigroup-Set) y = left-unit
  pr2 (pr2 is-unital-Semigroup-loop-semigroup-Set) x = right-unit

  is-group-loop-semigroup-Set' : is-group' loop-semigroup-Set is-unital-Semigroup-loop-semigroup-Set
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

  map-hom-symmetric-group-loop-group-Set : (X Y : UU-Set l) →
    Id (type-Set X) (type-Set Y) → (type-Set Y) ≃ (type-Set X)
  map-hom-symmetric-group-loop-group-Set X Y p = equiv-eq (inv p)

  map-hom-inv-symmetric-group-loop-group-Set : (X Y : UU-Set l) →
    (type-Set X) ≃ (type-Set Y) → Id (type-Set Y) (type-Set X)
  map-hom-inv-symmetric-group-loop-group-Set X Y f =
    inv (eq-equiv (type-Set X) (type-Set Y) f)

  commutative-inv-map-hom-symmetric-group-loop-group-Set :
    (X Y : UU l) (p : Id X Y) (sX : is-set X) (sY : is-set Y) →
    Id
      ( map-hom-symmetric-group-loop-group-Set (pair Y sY) (pair X sX) (inv p))
      ( inv-equiv
        ( map-hom-symmetric-group-loop-group-Set (pair X sX) (pair Y sY) p))
  commutative-inv-map-hom-symmetric-group-loop-group-Set X .X refl sX sY =
    ( inv (right-inverse-law-equiv id-equiv)) ∙
      ( left-unit-law-equiv (inv-equiv id-equiv))

module _
  {l : Level} (X : UU-Set l)
  where

  hom-symmetric-group-loop-group-Set :
    type-hom-Group (loop-group-Set X) (symmetric-Group X)
  pr1 hom-symmetric-group-loop-group-Set =
    map-hom-symmetric-group-loop-group-Set X X
  pr2 hom-symmetric-group-loop-group-Set p q =
    ( ap equiv-eq (distributive-inv-concat p q)) ∙
      ( inv (comp-equiv-eq (inv q) (inv p)))

  hom-inv-symmetric-group-loop-group-Set :
    type-hom-Group (symmetric-Group X) (loop-group-Set X)
  pr1 hom-inv-symmetric-group-loop-group-Set =
    map-hom-inv-symmetric-group-loop-group-Set X X
  pr2 hom-inv-symmetric-group-loop-group-Set f g =
    ( ap inv (inv (comp-eq-equiv (type-Set X) (type-Set X) (type-Set X) g f))) ∙
      ( distributive-inv-concat
        ( eq-equiv (type-Set X) (type-Set X) g)
        ( eq-equiv (type-Set X) (type-Set X) f))

  is-sec-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( hom-symmetric-group-loop-group-Set)
        ( hom-inv-symmetric-group-loop-group-Set))
      ( id-hom-Group (symmetric-Group X))
  is-sec-hom-inv-symmetric-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ f →
          ( ap equiv-eq (inv-inv (eq-equiv (type-Set X) (type-Set X) f))) ∙
            ( ap (λ e → map-equiv e f) (right-inverse-law-equiv equiv-univalence))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (symmetric-Group X))
          ( semigroup-Group (symmetric-Group X))
          ( id)))

  is-retr-hom-inv-symmetric-group-loop-group-Set :
    Id
      ( comp-hom-Group
        ( loop-group-Set X)
        ( symmetric-Group X)
        ( loop-group-Set X)
        ( hom-inv-symmetric-group-loop-group-Set)
        ( hom-symmetric-group-loop-group-Set))
      ( id-hom-Group (loop-group-Set X))
  is-retr-hom-inv-symmetric-group-loop-group-Set =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap inv (ap (λ e → map-equiv e (inv p)) (left-inverse-law-equiv equiv-univalence))) ∙
            ( inv-inv p)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set X))
          ( semigroup-Group (loop-group-Set X))
          ( id)))

  iso-symmetric-group-loop-group-Set :
    type-iso-Group (loop-group-Set X) (symmetric-Group X)
  pr1 iso-symmetric-group-loop-group-Set = hom-symmetric-group-loop-group-Set
  pr1 (pr2 iso-symmetric-group-loop-group-Set) = hom-inv-symmetric-group-loop-group-Set
  pr1 (pr2 (pr2 iso-symmetric-group-loop-group-Set)) = is-sec-hom-inv-symmetric-group-loop-group-Set
  pr2 (pr2 (pr2 iso-symmetric-group-loop-group-Set)) = is-retr-hom-inv-symmetric-group-loop-group-Set
```

