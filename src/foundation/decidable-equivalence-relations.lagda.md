---
title: Decidable equivalence relations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-equivalence-relations where

open import foundation.decidable-propositions
open import foundation.decidable-relations
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.identity-types
open import foundation.images
open import foundation.propositional-extensionality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.slice
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-image
open import foundation.universe-levels
```

## Idea

A decidable equivalence relation on a type `X` is an equivalence relation `R` on `X` such that `R x y` is a decidable proposition for each `x y : X`.

## Definitions

### Decidable equivalence relations

```agda
Decidable-Equivalence-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Decidable-Equivalence-Relation l2 X =
  Σ ( Decidable-Relation l2 X)
    ( λ R → is-equivalence-relation (relation-Decidable-Relation R))

module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  decidable-relation-Decidable-Equivalence-Relation :
    Decidable-Relation l2 X
  decidable-relation-Decidable-Equivalence-Relation = pr1 R

  relation-Decidable-Equivalence-Relation : X → X → UU-Prop l2
  relation-Decidable-Equivalence-Relation =
    relation-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  sim-Decidable-Equivalence-Relation : X → X → UU l2
  sim-Decidable-Equivalence-Relation =
    type-Decidable-Relation decidable-relation-Decidable-Equivalence-Relation

  is-prop-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-prop (sim-Decidable-Equivalence-Relation x y)
  is-prop-sim-Decidable-Equivalence-Relation =
    is-prop-type-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-decidable-sim-Decidable-Equivalence-Relation :
    (x y : X) → is-decidable (sim-Decidable-Equivalence-Relation x y)
  is-decidable-sim-Decidable-Equivalence-Relation =
    is-decidable-type-Decidable-Relation
      decidable-relation-Decidable-Equivalence-Relation

  is-equivalence-relation-Decidable-Equivalence-Relation :
    is-equivalence-relation relation-Decidable-Equivalence-Relation
  is-equivalence-relation-Decidable-Equivalence-Relation = pr2 R

  equivalence-relation-Decidable-Equivalence-Relation : Eq-Rel l2 X
  pr1 equivalence-relation-Decidable-Equivalence-Relation =
    relation-Decidable-Equivalence-Relation
  pr2 equivalence-relation-Decidable-Equivalence-Relation =
    is-equivalence-relation-Decidable-Equivalence-Relation

  refl-Decidable-Equivalence-Relation :
    {x : X} → sim-Decidable-Equivalence-Relation x x
  refl-Decidable-Equivalence-Relation =
    refl-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation

  symmetric-Decidable-Equivalence-Relation :
    {x y : X} → sim-Decidable-Equivalence-Relation x y →
    sim-Decidable-Equivalence-Relation y x
  symmetric-Decidable-Equivalence-Relation =
    symm-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation

  transitive-Decidable-Equivalence-Relation :
    {x y z : X} → sim-Decidable-Equivalence-Relation x y →
    sim-Decidable-Equivalence-Relation y z →
    sim-Decidable-Equivalence-Relation x z
  transitive-Decidable-Equivalence-Relation =
    trans-Eq-Rel equivalence-relation-Decidable-Equivalence-Relation
```

### Equivalence classes of decidable equivalence relations

```agda
module _
  {l1 l2 : Level} {X : UU l1} (R : Decidable-Equivalence-Relation l2 X)
  where

  is-equivalence-class-Decidable-Equivalence-Relation :
    decidable-subtype l2 X → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Decidable-Equivalence-Relation P =
    ∃ (λ x → Id P (decidable-relation-Decidable-Equivalence-Relation R x))

  equivalence-class-Decidable-Equivalence-Relation : UU (l1 ⊔ lsuc l2)
  equivalence-class-Decidable-Equivalence-Relation =
    im (decidable-relation-Decidable-Equivalence-Relation R)

  class-Decidable-Equivalence-Relation :
    X → equivalence-class-Decidable-Equivalence-Relation
  pr1 (class-Decidable-Equivalence-Relation x) =
    decidable-relation-Decidable-Equivalence-Relation R x
  pr2 (class-Decidable-Equivalence-Relation x) =
    intro-∃ x refl

  emb-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation ↪ decidable-subtype l2 X
  emb-equivalence-class-Decidable-Equivalence-Relation =
    emb-im (decidable-relation-Decidable-Equivalence-Relation R)

  decidable-subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → decidable-subtype l2 X
  decidable-subtype-equivalence-class-Decidable-Equivalence-Relation =
    map-emb emb-equivalence-class-Decidable-Equivalence-Relation

  subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → subtype l2 X
  subtype-equivalence-class-Decidable-Equivalence-Relation =
    subtype-decidable-subtype ∘
    decidable-subtype-equivalence-class-Decidable-Equivalence-Relation

  is-in-subtype-equivalence-class-Decidable-Equivalence-Relation :
    equivalence-class-Decidable-Equivalence-Relation → X → UU l2
  is-in-subtype-equivalence-class-Decidable-Equivalence-Relation =
    is-in-subtype ∘ subtype-equivalence-class-Decidable-Equivalence-Relation

  is-prop-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation :
    (P : equivalence-class-Decidable-Equivalence-Relation) (x : X) →
    is-prop (is-in-subtype-equivalence-class-Decidable-Equivalence-Relation P x)
  is-prop-is-in-subtype-equivalence-class-Decidable-Equivalence-Relation P =
    is-prop-is-in-subtype
      ( subtype-equivalence-class-Decidable-Equivalence-Relation P)

  is-set-equivalence-class-Decidable-Equivalence-Relation :
    is-set equivalence-class-Decidable-Equivalence-Relation
  is-set-equivalence-class-Decidable-Equivalence-Relation =
    is-set-im
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( is-set-decidable-subtype)

  equivalence-class-Decidable-Equivalence-Relation-Set : UU-Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Decidable-Equivalence-Relation-Set =
    equivalence-class-Decidable-Equivalence-Relation
  pr2 equivalence-class-Decidable-Equivalence-Relation-Set =
    is-set-equivalence-class-Decidable-Equivalence-Relation

  unit-im-equivalence-class-Decidable-Equivalence-Relation :
    hom-slice
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( decidable-subtype-equivalence-class-Decidable-Equivalence-Relation)
  unit-im-equivalence-class-Decidable-Equivalence-Relation =
    unit-im (decidable-relation-Decidable-Equivalence-Relation R)

  is-image-equivalence-class-Decidable-Equivalence-Relation :
    {l : Level} →
    is-image l
      ( decidable-relation-Decidable-Equivalence-Relation R)
      ( emb-equivalence-class-Decidable-Equivalence-Relation)
      ( unit-im-equivalence-class-Decidable-Equivalence-Relation)
  is-image-equivalence-class-Decidable-Equivalence-Relation =
    is-image-im (decidable-relation-Decidable-Equivalence-Relation R)

  is-surjective-class-Decidable-Equivalence-Relation :
    is-surjective class-Decidable-Equivalence-Relation
  is-surjective-class-Decidable-Equivalence-Relation =
    is-surjective-map-unit-im
      ( decidable-relation-Decidable-Equivalence-Relation R)
```

## Properties

### We characterize the identity type of the equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Decidable-Equivalence-Relation l2 A) (a : A)
  where

  abstract
    center-total-subtype-equivalence-class-Decidable-Equivalence-Relation :
      Σ ( equivalence-class-Decidable-Equivalence-Relation R)
        ( λ P →
          is-in-subtype-equivalence-class-Decidable-Equivalence-Relation R P a)
    pr1 center-total-subtype-equivalence-class-Decidable-Equivalence-Relation =
      class-Decidable-Equivalence-Relation R a
    pr2 center-total-subtype-equivalence-class-Decidable-Equivalence-Relation =
      refl-Decidable-Equivalence-Relation R

    contraction-total-subtype-equivalence-class-Decidable-Equivalence-Relation :
      ( t :
        Σ ( equivalence-class-Decidable-Equivalence-Relation R)
          ( λ P →
            is-in-subtype-equivalence-class-Decidable-Equivalence-Relation
              R P a)) →
      Id center-total-subtype-equivalence-class-Decidable-Equivalence-Relation t
    contraction-total-subtype-equivalence-class-Decidable-Equivalence-Relation
      ( pair (pair P p) H) =
      eq-subtype
        ( λ Q → subtype-equivalence-class-Decidable-Equivalence-Relation R Q a)
        ( apply-universal-property-trunc-Prop
          ( p)
          ( Id-Prop
            ( equivalence-class-Decidable-Equivalence-Relation-Set R)
            ( class-Decidable-Equivalence-Relation R a)
            ( pair P p))
          ( α))
      where
        α :
          fib (pr1 R) P →
          Id (class-Decidable-Equivalence-Relation R a) (pair P p)
        α (pair x refl) =
          eq-subtype
            ( λ z →
              trunc-Prop
                ( fib (decidable-relation-Decidable-Equivalence-Relation R) z))
            ( eq-htpy
              ( λ y →
                {!is-injective-is-emb!}))

```
      α : fib (pr1 R) P → Id (class R a) (pair P p)
      α (pair x refl) =
        eq-subtype
          ( λ z → trunc-Prop (fib (prop-Eq-Rel R) z))
          ( eq-htpy
            ( λ y →
              eq-iff
                ( trans-Eq-Rel R H)
                ( trans-Eq-Rel R (symm-Eq-Rel R H))))
  
    is-contr-total-subtype-equivalence-class :
      is-contr
        ( Σ ( equivalence-class R)
            ( λ P → is-in-subtype-equivalence-class R P a))
    pr1 is-contr-total-subtype-equivalence-class =
      center-total-subtype-equivalence-class
    pr2 is-contr-total-subtype-equivalence-class =
      contraction-total-subtype-equivalence-class

  related-eq-quotient :
    (q : equivalence-class R) → Id (class R a) q →
    is-in-subtype-equivalence-class R q a
  related-eq-quotient .(class R a) refl =
    refl-Eq-Rel R

  abstract
    is-equiv-related-eq-quotient :
      (q : equivalence-class R) → is-equiv (related-eq-quotient q)
    is-equiv-related-eq-quotient =
      fundamental-theorem-id
        ( class R a)
        ( refl-Eq-Rel R)
        ( is-contr-total-subtype-equivalence-class)
        ( related-eq-quotient)

  abstract
    effective-quotient' :
      (q : equivalence-class R) →
      ( Id (class R a) q) ≃
      ( is-in-subtype-equivalence-class R q a)
    pr1 (effective-quotient' q) = related-eq-quotient q
    pr2 (effective-quotient' q) = is-equiv-related-eq-quotient q

  abstract
    eq-effective-quotient' :
      (q : equivalence-class R) → is-in-subtype-equivalence-class R q a →
      Id (class R a) q
    eq-effective-quotient' q = map-inv-is-equiv (is-equiv-related-eq-quotient q)


### The quotient map into the large set quotient is effective


module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  abstract
    is-effective-class :
      is-effective R (class R)
    is-effective-class x y =
      ( equiv-symm-Eq-Rel R y x) ∘e
      ( effective-quotient' R x (class R y))
  
  abstract
    apply-effectiveness-class :
      {x y : A} →
      Id ( class R x)
         ( class R y) →
      sim-Eq-Rel R x y
    apply-effectiveness-class {x} {y} =
      map-equiv (is-effective-class x y)

  abstract
    apply-effectiveness-class' :
      {x y : A} → sim-Eq-Rel R x y →
      Id ( class R x)
         ( class R y)
    apply-effectiveness-class' {x} {y} =
      map-inv-equiv (is-effective-class x y)


### The quotient map into the large set quotient is surjective and effective

agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-surjective-and-effective-class :
    is-surjective-and-effective R (class R)
  pr1 is-surjective-and-effective-class =
    is-surjective-class R
  pr2 is-surjective-and-effective-class =
    is-effective-class R


### The quotient map into the large set quotient is a reflecting map

agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  quotient-reflecting-map-equivalence-class :
    reflecting-map-Eq-Rel R (equivalence-class R)
  pr1 quotient-reflecting-map-equivalence-class =
    class R
  pr2 quotient-reflecting-map-equivalence-class =
    apply-effectiveness-class' R


agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  transitive-is-in-subtype-equivalence-class : (P : equivalence-class R) (a b : A) →
    is-in-subtype-equivalence-class R P a → sim-Eq-Rel R a b →
    is-in-subtype-equivalence-class R P b
  transitive-is-in-subtype-equivalence-class P a b p q =
    apply-universal-property-trunc-Prop
      ( pr2 P)
      ( subtype-equivalence-class R P b)
      ( λ (pair x T) →
        tr
          ( λ Z → is-in-subtype-equivalence-class R Z b)
          { x = class R x} {y = P}
          ( eq-pair-Σ
            ( T)
            ( all-elements-equal-type-trunc-Prop _ _))
          ( trans-Eq-Rel R
            ( tr
              ( λ Z → is-in-subtype-equivalence-class R Z a)
              { x = P} {y = class R x}
              ( eq-pair-Σ (inv T) (all-elements-equal-type-trunc-Prop _ _))
              ( p))
            q))


agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-decidable-is-in-subtype-equivalence-class-is-decidable :
    ((a b : A) → is-decidable (sim-Eq-Rel R a b)) →
    (T : equivalence-class R) →
    (a : A) →
    is-decidable (is-in-subtype-equivalence-class R T a)
  is-decidable-is-in-subtype-equivalence-class-is-decidable F T a =
    apply-universal-property-trunc-Prop
      ( pr2 T)
      ( is-decidable-Prop
        ( subtype-equivalence-class R T a))
      ( λ (pair t P) →
        cases-decidable-is-in-subtype-equivalence-class
          T a t (eq-pair-Σ (inv P) (all-elements-equal-type-trunc-Prop _ _)) (F t a))
    where
    cases-decidable-is-in-subtype-equivalence-class :
      (T : equivalence-class R)
      (a t : A) →
      Id T (class R t) →
      is-decidable (sim-Eq-Rel R t a) →
      is-decidable (is-in-subtype-equivalence-class R T a)
    cases-decidable-is-in-subtype-equivalence-class T a t p1 (inl p) =
      inl
        ( tr
          ( λ x → is-in-subtype-equivalence-class R x a)
          ( inv p1)
          ( p))
    cases-decidable-is-in-subtype-equivalence-class T a t p1 (inr np) =
      inr
        ( λ p →
          np
          ( tr
            ( λ x →
              is-in-subtype-equivalence-class R x a)
            ( p1)
            ( p)))

