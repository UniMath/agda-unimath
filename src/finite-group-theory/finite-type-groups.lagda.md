# The group of n-element types

```agda
{-# OPTIONS --lossy-unification #-}

module finite-group-theory.finite-type-groups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.truncated-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

### Definition

```agda
UU-Fin-Group : (l : Level) (n : ℕ) → Concrete-Group (lsuc l)
pr1 (pr1 (pr1 (UU-Fin-Group l n))) = UU-Fin l n
pr2 (pr1 (pr1 (UU-Fin-Group l n))) = Fin-UU-Fin l n
pr2 (pr1 (UU-Fin-Group l n)) = is-0-connected-UU-Fin n
pr2 (UU-Fin-Group l n) =
  is-1-type-UU-Fin n (Fin-UU-Fin l n) (Fin-UU-Fin l n)
```

### Properties

```agda
module _
  (l : Level) (n : ℕ)
  where

  hom-loop-group-fin-UU-Fin-Group :
    hom-Group
      ( group-Concrete-Group (UU-Fin-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 hom-loop-group-fin-UU-Fin-Group p = pr1 (pair-eq-Σ p)
  pr2 hom-loop-group-fin-UU-Fin-Group {p} {q} =
    pr1-interchange-concat-pair-eq-Σ p q

  hom-inv-loop-group-fin-UU-Fin-Group :
    hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set n)))
      ( group-Concrete-Group (UU-Fin-Group l n))
  pr1 hom-inv-loop-group-fin-UU-Fin-Group p =
    eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)
  pr2 hom-inv-loop-group-fin-UU-Fin-Group {p} {q} =
    ( ap
      ( λ r → eq-pair-Σ (p ∙ q) r)
      ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
      ( interchange-concat-eq-pair-Σ
        ( p)
        ( q)
        ( eq-is-prop is-prop-type-trunc-Prop)
        ( eq-is-prop is-prop-type-trunc-Prop))

  is-section-hom-inv-loop-group-fin-UU-Fin-Group :
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( hom-loop-group-fin-UU-Fin-Group)
        ( hom-inv-loop-group-fin-UU-Fin-Group))
      ( id-hom-Group (loop-group-Set (raise-Set l (Fin-Set n))))
  is-section-hom-inv-loop-group-fin-UU-Fin-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ap pr1
            ( is-retraction-pair-eq-Σ
              ( Fin-UU-Fin l n)
              ( Fin-UU-Fin l n)
              ( pair p (eq-is-prop is-prop-type-trunc-Prop)))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( id)))

  is-retraction-hom-inv-loop-group-fin-UU-Fin-Group :
    Id
      ( comp-hom-Group
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( group-Concrete-Group (UU-Fin-Group l n))
        ( hom-inv-loop-group-fin-UU-Fin-Group)
        ( hom-loop-group-fin-UU-Fin-Group))
      ( id-hom-Group (group-Concrete-Group (UU-Fin-Group l n)))
  is-retraction-hom-inv-loop-group-fin-UU-Fin-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ (pr1 (pair-eq-Σ p)) r)
            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
            ( is-section-pair-eq-Σ (Fin-UU-Fin l n) (Fin-UU-Fin l n) p)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (group-Concrete-Group (UU-Fin-Group l n)))
          ( semigroup-Group (group-Concrete-Group (UU-Fin-Group l n)))
          ( id)))

  iso-loop-group-fin-UU-Fin-Group :
    iso-Group
      ( group-Concrete-Group (UU-Fin-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 iso-loop-group-fin-UU-Fin-Group =
    hom-loop-group-fin-UU-Fin-Group
  pr1 (pr2 iso-loop-group-fin-UU-Fin-Group) =
    hom-inv-loop-group-fin-UU-Fin-Group
  pr1 (pr2 (pr2 iso-loop-group-fin-UU-Fin-Group)) =
    is-section-hom-inv-loop-group-fin-UU-Fin-Group
  pr2 (pr2 (pr2 iso-loop-group-fin-UU-Fin-Group)) =
    is-retraction-hom-inv-loop-group-fin-UU-Fin-Group
```
