---
title: Equivalence classes
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalence-classes where

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable; is-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.effective-maps-equivalence-relations using
  ( is-effective; is-surjective-and-effective)
open import foundation.equivalence-relations using
  ( Eq-Rel; sim-Eq-Rel; prop-Eq-Rel; refl-Eq-Rel; trans-Eq-Rel; symm-Eq-Rel;
    equiv-symm-Eq-Rel)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; _∘e_; map-equiv; map-inv-equiv)
open import foundation.existential-quantification using (∃)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.identity-types using (_＝_; refl; tr; inv)
open import foundation.images using
  ( im; map-unit-im; emb-im; is-set-im; unit-im; is-surjective-map-unit-im)
open import foundation.propositional-extensionality using
  ( eq-iff; is-set-UU-Prop)
open import foundation.propositional-truncations using
  ( trunc-Prop; apply-universal-property-trunc-Prop; all-elements-equal-type-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop; is-prop-type-Prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel)
open import foundation.sets using
  ( is-set; is-set-function-type; UU-Set; Id-Prop)
open import foundation.slice using (hom-slice)
open import foundation.subtypes using (eq-subtype; subtype)
open import foundation.surjective-maps using
  ( is-surjective)
open import foundation.universal-property-image using
  ( is-image; is-image-im)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

An equivalence class of an equivalence relation `R` on `A` is a subtype of `A` that is merely equivalent to a subtype of the form `R x`. The type of equivalence classes of an equivalence relation satisfies the universal property of the set quotient.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-equivalence-class : subtype l2 A → UU (l1 ⊔ lsuc l2)
  is-equivalence-class P = ∃ A (λ x → (type-Prop ∘ P) ＝ sim-Eq-Rel R x)

  equivalence-class : UU (l1 ⊔ lsuc l2)
  equivalence-class = im (prop-Eq-Rel R)
  
  class : A → equivalence-class
  class = map-unit-im (prop-Eq-Rel R)

  emb-equivalence-class : equivalence-class ↪ subtype l2 A
  emb-equivalence-class = emb-im (prop-Eq-Rel R)

  subtype-equivalence-class : equivalence-class → subtype l2 A
  subtype-equivalence-class = map-emb emb-equivalence-class

  is-in-subtype-equivalence-class : equivalence-class → (A → UU l2)
  is-in-subtype-equivalence-class P x =
    type-Prop (subtype-equivalence-class P x)

  abstract
    is-prop-is-in-subtype-equivalence-class :
      (x : equivalence-class) (a : A) →
      is-prop (is-in-subtype-equivalence-class x a)
    is-prop-is-in-subtype-equivalence-class P x =
      is-prop-type-Prop (subtype-equivalence-class P x)

  abstract
    is-set-equivalence-class : is-set equivalence-class
    is-set-equivalence-class =
      is-set-im (prop-Eq-Rel R) (is-set-function-type is-set-UU-Prop)

  equivalence-class-Set : UU-Set (l1 ⊔ lsuc l2)
  pr1 equivalence-class-Set = equivalence-class
  pr2 equivalence-class-Set = is-set-equivalence-class

  unit-im-equivalence-class :
    hom-slice (prop-Eq-Rel R) subtype-equivalence-class
  unit-im-equivalence-class = unit-im (prop-Eq-Rel R)

  is-image-equivalence-class :
    {l : Level} →
    is-image l (prop-Eq-Rel R) emb-equivalence-class unit-im-equivalence-class
  is-image-equivalence-class = is-image-im (prop-Eq-Rel R)

  is-surjective-class : is-surjective class
  is-surjective-class = is-surjective-map-unit-im (prop-Eq-Rel R)
```

## Properties

### We characterize the identity type of the type of equivalence classes

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  where

  abstract
    center-total-subtype-equivalence-class :
      Σ (equivalence-class R) (λ P → is-in-subtype-equivalence-class R P a)
    pr1 center-total-subtype-equivalence-class = class R a
    pr2 center-total-subtype-equivalence-class = refl-Eq-Rel R
  
    contraction-total-subtype-equivalence-class :
      ( t :
        Σ ( equivalence-class R)
          ( λ P → is-in-subtype-equivalence-class R P a)) →
      center-total-subtype-equivalence-class ＝ t
    contraction-total-subtype-equivalence-class (pair (pair P p) H) =
      eq-subtype
        ( λ Q → subtype-equivalence-class R Q a)
        ( apply-universal-property-trunc-Prop
          ( p)
          ( Id-Prop
            ( equivalence-class-Set R)
            ( class R a)
            ( pair P p))
          ( α))
      where
      α : fib (pr1 R) P → class R a ＝ pair P p
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
    (q : equivalence-class R) → class R a ＝ q →
    is-in-subtype-equivalence-class R q a
  related-eq-quotient .(class R a) refl =
    refl-Eq-Rel R

  abstract
    is-equiv-related-eq-quotient :
      (q : equivalence-class R) → is-equiv (related-eq-quotient q)
    is-equiv-related-eq-quotient =
      fundamental-theorem-id
        ( is-contr-total-subtype-equivalence-class)
        ( related-eq-quotient)

  abstract
    effective-quotient' :
      (q : equivalence-class R) →
      ( class R a ＝ q) ≃
      ( is-in-subtype-equivalence-class R q a)
    pr1 (effective-quotient' q) = related-eq-quotient q
    pr2 (effective-quotient' q) = is-equiv-related-eq-quotient q

  abstract
    eq-effective-quotient' :
      (q : equivalence-class R) → is-in-subtype-equivalence-class R q a →
      class R a ＝ q
    eq-effective-quotient' q = map-inv-is-equiv (is-equiv-related-eq-quotient q)
```

### The map `class` into the type of equivalence classes is effective

```
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
      {x y : A} → class R x ＝ class R y → sim-Eq-Rel R x y
    apply-effectiveness-class {x} {y} =
      map-equiv (is-effective-class x y)

  abstract
    apply-effectiveness-class' :
      {x y : A} → sim-Eq-Rel R x y → class R x ＝ class R y
    apply-effectiveness-class' {x} {y} =
      map-inv-equiv (is-effective-class x y)
```

### The map `class` into the type of equivalence classes is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-surjective-and-effective-class :
    is-surjective-and-effective R (class R)
  pr1 is-surjective-and-effective-class =
    is-surjective-class R
  pr2 is-surjective-and-effective-class =
    is-effective-class R
```

### The map `class` into the type of equivalence classes is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  quotient-reflecting-map-equivalence-class :
    reflecting-map-Eq-Rel R (equivalence-class R)
  pr1 quotient-reflecting-map-equivalence-class =
    class R
  pr2 quotient-reflecting-map-equivalence-class =
    apply-effectiveness-class' R
```

```agda
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
```

```agda
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
      T ＝ class R t →
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
```
