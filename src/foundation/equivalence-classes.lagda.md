# Equivalence classes

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalence-classes where

open import foundation.contractible-types using (is-contr)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable; is-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.effective-maps-equivalence-relations using
  ( is-effective; is-surjective-and-effective)
open import foundation.equivalence-relations using
  ( Eq-Rel; type-Eq-Rel; prop-Eq-Rel; refl-Eq-Rel; trans-Eq-Rel; symm-Eq-Rel;
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
open import foundation.identity-types using (Id; refl; tr; inv)
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
open import foundation.subtypes using (eq-subtype)
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

  class-Eq-Rel : A → A → UU l2
  class-Eq-Rel = type-Eq-Rel R

  is-equivalence-class-Eq-Rel : (A → UU-Prop l2) → UU (l1 ⊔ lsuc l2)
  is-equivalence-class-Eq-Rel P =
    ∃ (λ x → Id (type-Prop ∘ P) (class-Eq-Rel x))

  large-set-quotient : UU (l1 ⊔ lsuc l2)
  large-set-quotient = im (prop-Eq-Rel R)
  
  quotient-map-large-set-quotient : A → large-set-quotient
  quotient-map-large-set-quotient = map-unit-im (prop-Eq-Rel R)

  emb-large-set-quotient : large-set-quotient ↪ (A → UU-Prop l2)
  emb-large-set-quotient = emb-im (prop-Eq-Rel R)

  class-large-set-quotient : large-set-quotient → (A → UU-Prop l2)
  class-large-set-quotient = map-emb emb-large-set-quotient

  type-class-large-set-quotient : large-set-quotient → (A → UU l2)
  type-class-large-set-quotient P x = type-Prop (class-large-set-quotient P x)

  abstract
    is-prop-type-class-large-set-quotient :
      (x : large-set-quotient) (a : A) →
      is-prop (type-class-large-set-quotient x a)
    is-prop-type-class-large-set-quotient P x =
      is-prop-type-Prop (class-large-set-quotient P x)

  abstract
    is-set-large-set-quotient : is-set large-set-quotient
    is-set-large-set-quotient =
      is-set-im (prop-Eq-Rel R) (is-set-function-type is-set-UU-Prop)

  large-quotient-Set : UU-Set (l1 ⊔ lsuc l2)
  pr1 large-quotient-Set = large-set-quotient
  pr2 large-quotient-Set = is-set-large-set-quotient

  unit-im-large-set-quotient :
    hom-slice (prop-Eq-Rel R) class-large-set-quotient
  unit-im-large-set-quotient = unit-im (prop-Eq-Rel R)

  is-image-large-set-quotient :
    {l : Level} →
    is-image l (prop-Eq-Rel R) emb-large-set-quotient unit-im-large-set-quotient
  is-image-large-set-quotient = is-image-im (prop-Eq-Rel R)

  is-surjective-quotient-map-large-set-quotient :
    is-surjective quotient-map-large-set-quotient
  is-surjective-quotient-map-large-set-quotient =
    is-surjective-map-unit-im (prop-Eq-Rel R)
```

## Properties

### We characterize the identity type of the large set quotient

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) (a : A)
  where

  abstract
    center-total-class-Eq-Rel :
      Σ (large-set-quotient R) (λ P → type-class-large-set-quotient R P a)
    pr1 center-total-class-Eq-Rel = quotient-map-large-set-quotient R a
    pr2 center-total-class-Eq-Rel = refl-Eq-Rel R
  
    contraction-total-class-Eq-Rel :
      ( t :
        Σ (large-set-quotient R) (λ P → type-class-large-set-quotient R P a)) →
      Id center-total-class-Eq-Rel t
    contraction-total-class-Eq-Rel (pair (pair P p) H) =
      eq-subtype
        ( λ Q → class-large-set-quotient R Q a)
        ( apply-universal-property-trunc-Prop
          ( p)
          ( Id-Prop
            ( large-quotient-Set R)
            ( quotient-map-large-set-quotient R a)
            ( pair P p))
          ( α))
      where
      α : fib (pr1 R) P → Id (quotient-map-large-set-quotient R a) (pair P p)
      α (pair x refl) =
        eq-subtype
          ( λ z → trunc-Prop (fib (prop-Eq-Rel R) z))
          ( eq-htpy
            ( λ y →
              eq-iff
                ( trans-Eq-Rel R H)
                ( trans-Eq-Rel R (symm-Eq-Rel R H))))
  
    is-contr-total-class-Eq-Rel :
      is-contr
        ( Σ (large-set-quotient R) (λ P → type-class-large-set-quotient R P a))
    pr1 is-contr-total-class-Eq-Rel = center-total-class-Eq-Rel
    pr2 is-contr-total-class-Eq-Rel = contraction-total-class-Eq-Rel

  related-eq-quotient :
    (q : large-set-quotient R) → Id (quotient-map-large-set-quotient R a) q →
    type-class-large-set-quotient R q a
  related-eq-quotient .(quotient-map-large-set-quotient R a) refl =
    refl-Eq-Rel R

  abstract
    is-equiv-related-eq-quotient :
      (q : large-set-quotient R) → is-equiv (related-eq-quotient q)
    is-equiv-related-eq-quotient =
      fundamental-theorem-id
        ( quotient-map-large-set-quotient R a)
        ( refl-Eq-Rel R)
        ( is-contr-total-class-Eq-Rel)
        ( related-eq-quotient)

  abstract
    effective-quotient' :
      (q : large-set-quotient R) →
      ( Id (quotient-map-large-set-quotient R a) q) ≃
      ( type-class-large-set-quotient R q a)
    pr1 (effective-quotient' q) = related-eq-quotient q
    pr2 (effective-quotient' q) = is-equiv-related-eq-quotient q

{-
  abstract
    is-locally-small-large-set-quotient :
      is-locally-small l2 (large-set-quotient R)
    is-locally-small-large-set-quotient = {!!}
-}

  abstract
    eq-effective-quotient' :
      (q : large-set-quotient R) → type-class-large-set-quotient R q a →
      Id (quotient-map-large-set-quotient R a) q
    eq-effective-quotient' q = map-inv-is-equiv (is-equiv-related-eq-quotient q)
```

### The quotient map into the large set quotient is effective

```
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  abstract
    is-effective-quotient-map-large-set-quotient :
      is-effective R (quotient-map-large-set-quotient R)
    is-effective-quotient-map-large-set-quotient x y =
      ( equiv-symm-Eq-Rel R y x) ∘e
      ( effective-quotient' R x (quotient-map-large-set-quotient R y))
  
  abstract
    apply-effectiveness-quotient-map-large-set-quotient :
      {x y : A} →
      Id ( quotient-map-large-set-quotient R x)
         ( quotient-map-large-set-quotient R y) →
      type-Eq-Rel R x y
    apply-effectiveness-quotient-map-large-set-quotient {x} {y} =
      map-equiv (is-effective-quotient-map-large-set-quotient x y)

  abstract
    apply-effectiveness-quotient-map-large-set-quotient' :
      {x y : A} → type-Eq-Rel R x y →
      Id ( quotient-map-large-set-quotient R x)
         ( quotient-map-large-set-quotient R y)
    apply-effectiveness-quotient-map-large-set-quotient' {x} {y} =
      map-inv-equiv (is-effective-quotient-map-large-set-quotient x y)
```

### The quotient map into the large set quotient is surjective and effective

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-surjective-and-effective-quotient-map-large-set-quotient :
    is-surjective-and-effective R (quotient-map-large-set-quotient R)
  pr1 is-surjective-and-effective-quotient-map-large-set-quotient =
    is-surjective-quotient-map-large-set-quotient R
  pr2 is-surjective-and-effective-quotient-map-large-set-quotient =
    is-effective-quotient-map-large-set-quotient R
```

### The quotient map into the large set quotient is a reflecting map

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  quotient-reflecting-map-large-set-quotient :
    reflecting-map-Eq-Rel R (large-set-quotient R)
  pr1 quotient-reflecting-map-large-set-quotient =
    quotient-map-large-set-quotient R
  pr2 quotient-reflecting-map-large-set-quotient =
    apply-effectiveness-quotient-map-large-set-quotient' R
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  transitive-type-class-large-set-quotient : (P : large-set-quotient R) (a b : A) →
    type-class-large-set-quotient R P a → type-Eq-Rel R a b →
    type-class-large-set-quotient R P b
  transitive-type-class-large-set-quotient P a b p q =
    apply-universal-property-trunc-Prop
      ( pr2 P)
      ( class-large-set-quotient R P b)
      ( λ (pair x T) →
        tr
          ( λ Z → type-class-large-set-quotient R Z b)
          { x = quotient-map-large-set-quotient R x} {y = P}
          ( eq-pair-Σ
            ( T)
            ( all-elements-equal-type-trunc-Prop _ _))
          ( trans-Eq-Rel R
            ( tr
              ( λ Z → type-class-large-set-quotient R Z a)
              { x = P} {y = quotient-map-large-set-quotient R x}
              ( eq-pair-Σ (inv T) (all-elements-equal-type-trunc-Prop _ _))
              ( p))
            q))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  is-decidable-type-class-large-set-quotient-is-decidable :
    ((a b : A) → is-decidable (type-Eq-Rel R a b)) →
    (T : large-set-quotient R) →
    (a : A) →
    is-decidable (type-class-large-set-quotient R T a)
  is-decidable-type-class-large-set-quotient-is-decidable F T a =
    apply-universal-property-trunc-Prop
      ( pr2 T)
      ( is-decidable-Prop
        ( class-large-set-quotient R T a))
      ( λ (pair t P) →
        cases-decidable-type-class-large-set-quotient
          T a t (eq-pair-Σ (inv P) (all-elements-equal-type-trunc-Prop _ _)) (F t a))
    where
    cases-decidable-type-class-large-set-quotient :
      (T : large-set-quotient R)
      (a t : A) →
      Id T (quotient-map-large-set-quotient R t) →
      is-decidable (type-Eq-Rel R t a) →
      is-decidable (type-class-large-set-quotient R T a)
    cases-decidable-type-class-large-set-quotient T a t p1 (inl p) =
      inl
        ( tr
          ( λ x → type-class-large-set-quotient R x a)
          ( inv p1)
          ( p))
    cases-decidable-type-class-large-set-quotient T a t p1 (inr np) =
      inr
        ( λ p →
          np
          ( tr
            ( λ x →
              type-class-large-set-quotient R x a)
            ( p1)
            ( p)))
```
