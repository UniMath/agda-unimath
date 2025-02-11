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
Type-With-Cardinality-ℕ-Group :
  (l : Level) (n : ℕ) → Concrete-Group (lsuc l)
pr1 (pr1 (pr1 (Type-With-Cardinality-ℕ-Group l n))) =
  Type-With-Cardinality-ℕ l n
pr2 (pr1 (pr1 (Type-With-Cardinality-ℕ-Group l n))) =
  raise-Fin-Type-With-Cardinality-ℕ l n
pr2 (pr1 (Type-With-Cardinality-ℕ-Group l n)) =
  is-0-connected-Type-With-Cardinality-ℕ n
pr2 (Type-With-Cardinality-ℕ-Group l n) =
  is-1-type-Type-With-Cardinality-ℕ n
    ( raise-Fin-Type-With-Cardinality-ℕ l n)
    ( raise-Fin-Type-With-Cardinality-ℕ l n)

Type-With-Cardinality-ℕ-Group' : (l : Level) (n : ℕ) → Group (lsuc l)
Type-With-Cardinality-ℕ-Group' l n =
  group-Concrete-Group (Type-With-Cardinality-ℕ-Group l n)
```

### Properties

```agda
module _
  (l : Level) (n : ℕ)
  where

  hom-loop-group-fin-Type-With-Cardinality-ℕ-Group :
    hom-Group
      ( Type-With-Cardinality-ℕ-Group' l n)
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 hom-loop-group-fin-Type-With-Cardinality-ℕ-Group p =
    pr1 (pair-eq-Σ p)
  pr2 hom-loop-group-fin-Type-With-Cardinality-ℕ-Group {p} {q} =
    pr1-interchange-concat-pair-eq-Σ p q

  hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group :
    hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set n)))
      ( Type-With-Cardinality-ℕ-Group' l n)
  pr1 hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group p =
    eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)
  pr2 hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group {p} {q} =
    ( ap
      ( λ r → eq-pair-Σ (p ∙ q) r)
      ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
      ( interchange-concat-eq-pair-Σ
        ( p)
        ( q)
        ( eq-is-prop is-prop-type-trunc-Prop)
        ( eq-is-prop is-prop-type-trunc-Prop))

  is-section-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group :
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( Type-With-Cardinality-ℕ-Group' l n)
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( hom-loop-group-fin-Type-With-Cardinality-ℕ-Group)
        ( hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group))
      ( id-hom-Group (loop-group-Set (raise-Set l (Fin-Set n))))
  is-section-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ap pr1
            ( is-retraction-pair-eq-Σ
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( pair p (eq-is-prop is-prop-type-trunc-Prop)))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( id)))

  is-retraction-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group :
    Id
      ( comp-hom-Group
        ( Type-With-Cardinality-ℕ-Group' l n)
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( Type-With-Cardinality-ℕ-Group' l n)
        ( hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group)
        ( hom-loop-group-fin-Type-With-Cardinality-ℕ-Group))
      ( id-hom-Group (Type-With-Cardinality-ℕ-Group' l n))
  is-retraction-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ (pr1 (pair-eq-Σ p)) r)
            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
            ( is-section-pair-eq-Σ
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( raise-Fin-Type-With-Cardinality-ℕ l n)
              ( p))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (Type-With-Cardinality-ℕ-Group' l n))
          ( semigroup-Group (Type-With-Cardinality-ℕ-Group' l n))
          ( id)))

  iso-loop-group-fin-Type-With-Cardinality-ℕ-Group :
    iso-Group
      ( Type-With-Cardinality-ℕ-Group' l n)
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 iso-loop-group-fin-Type-With-Cardinality-ℕ-Group =
    hom-loop-group-fin-Type-With-Cardinality-ℕ-Group
  pr1 (pr2 iso-loop-group-fin-Type-With-Cardinality-ℕ-Group) =
    hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group
  pr1 (pr2 (pr2 iso-loop-group-fin-Type-With-Cardinality-ℕ-Group)) =
    is-section-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group
  pr2 (pr2 (pr2 iso-loop-group-fin-Type-With-Cardinality-ℕ-Group)) =
    is-retraction-hom-inv-loop-group-fin-Type-With-Cardinality-ℕ-Group
```
