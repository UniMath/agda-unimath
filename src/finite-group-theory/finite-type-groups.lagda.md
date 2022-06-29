# The group of n-element types

```agda
{-# OPTIONS --without-K --exact-split --experimental-lossy-unification #-}

module finite-group-theory.finite-type-groups where

open import elementary-number-theory.natural-numbers

open import foundation.connected-types 
open import foundation.dependent-pair-types 
open import foundation.equality-dependent-pair-types 
open import foundation.equivalences 
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types 
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.truncated-types
open import foundation.univalence 
open import foundation.universe-levels 

open import group-theory.concrete-groups 
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.loop-groups-sets

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

### Definition

```agda
UU-Fin-Level-Group : (l : Level) (n : ℕ) → Concrete-Group (lsuc l)
pr1 (pr1 (pr1 (UU-Fin-Level-Group l n))) = UU-Fin-Level l n
pr2 (pr1 (pr1 (UU-Fin-Level-Group l n))) = Fin-UU-Fin-Level l n
pr2 (pr1 (UU-Fin-Level-Group l n)) = is-path-connected-UU-Fin-Level n
pr2 (UU-Fin-Level-Group l n) =
  is-set-equiv
    ( equiv-UU-Fin-Level (Fin-UU-Fin-Level l n) (Fin-UU-Fin-Level l n))
    ( equiv-equiv-eq-UU-Fin-Level (Fin-UU-Fin-Level l n) (Fin-UU-Fin-Level l n))
    ( is-set-equiv-is-set
      ( is-set-type-Set (raise-Set l (Fin-Set n)))
      ( is-set-type-Set (raise-Set l (Fin-Set n))))
```

### Properties

```agda
module _
  (l : Level) (n : ℕ)
  where

  hom-loop-group-fin-UU-Fin-Level-Group :
    type-hom-Group
      ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 hom-loop-group-fin-UU-Fin-Level-Group p = pr1 (pair-eq-Σ p)
  pr2 hom-loop-group-fin-UU-Fin-Level-Group p q =
    inv (comp-pair-eq-Σ p q)
  
  hom-inv-loop-group-fin-UU-Fin-Level-Group :
    type-hom-Group
      ( loop-group-Set (raise-Set l (Fin-Set n)))
      ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
  pr1 hom-inv-loop-group-fin-UU-Fin-Level-Group p =
    eq-pair-Σ p (eq-is-prop is-prop-type-trunc-Prop)
  pr2 hom-inv-loop-group-fin-UU-Fin-Level-Group p q =
    ( ap
      ( λ r → eq-pair-Σ (p ∙ q) r)
      ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _)))) ∙
      ( inv
        ( comp-eq-pair-Σ
          ( pr2 (Fin-UU-Fin-Level l n))
          ( pr2 (Fin-UU-Fin-Level l n))
          ( pr2 (Fin-UU-Fin-Level l n))
          ( p)
          ( q)
          ( eq-is-prop is-prop-type-trunc-Prop)
          ( eq-is-prop is-prop-type-trunc-Prop)))

  is-sec-hom-inv-loop-group-fin-UU-Fin-Level-Group :
    Id
      ( comp-hom-Group
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( hom-loop-group-fin-UU-Fin-Level-Group)
        ( hom-inv-loop-group-fin-UU-Fin-Level-Group))
      ( id-hom-Group (loop-group-Set (raise-Set l (Fin-Set n))))
  is-sec-hom-inv-loop-group-fin-UU-Fin-Level-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ap pr1
            ( isretr-pair-eq-Σ
              ( Fin-UU-Fin-Level l n)
              ( Fin-UU-Fin-Level l n)
              ( pair p (eq-is-prop is-prop-type-trunc-Prop)))))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( semigroup-Group (loop-group-Set (raise-Set l (Fin-Set n))))
          ( id)))

  is-retr-hom-inv-loop-group-fin-UU-Fin-Level-Group :
    Id
      ( comp-hom-Group
        ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
        ( loop-group-Set (raise-Set l (Fin-Set n)))
        ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
        ( hom-inv-loop-group-fin-UU-Fin-Level-Group)
        ( hom-loop-group-fin-UU-Fin-Level-Group))
      ( id-hom-Group (abstract-group-Concrete-Group (UU-Fin-Level-Group l n)))
  is-retr-hom-inv-loop-group-fin-UU-Fin-Level-Group =
    eq-pair-Σ
      ( eq-htpy
        ( λ p →
          ( ap
            ( λ r → eq-pair-Σ (pr1 (pair-eq-Σ p)) r)
            ( eq-is-prop (is-trunc-Id (is-prop-type-trunc-Prop _ _))))  ∙
            ( issec-pair-eq-Σ (Fin-UU-Fin-Level l n) (Fin-UU-Fin-Level l n) p)))
      ( eq-is-prop
        ( is-prop-preserves-mul-Semigroup
          ( semigroup-Group (abstract-group-Concrete-Group (UU-Fin-Level-Group l n)))
          ( semigroup-Group (abstract-group-Concrete-Group (UU-Fin-Level-Group l n)))
          ( id)))

  iso-loop-group-fin-UU-Fin-Level-Group :
    type-iso-Group
      ( abstract-group-Concrete-Group (UU-Fin-Level-Group l n))
      ( loop-group-Set (raise-Set l (Fin-Set n)))
  pr1 iso-loop-group-fin-UU-Fin-Level-Group = hom-loop-group-fin-UU-Fin-Level-Group
  pr1 (pr2 iso-loop-group-fin-UU-Fin-Level-Group) = hom-inv-loop-group-fin-UU-Fin-Level-Group
  pr1 (pr2 (pr2 iso-loop-group-fin-UU-Fin-Level-Group)) = is-sec-hom-inv-loop-group-fin-UU-Fin-Level-Group
  pr2 (pr2 (pr2 iso-loop-group-fin-UU-Fin-Level-Group)) = is-retr-hom-inv-loop-group-fin-UU-Fin-Level-Group
```




