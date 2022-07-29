---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --allow-unsolved-metas --exact-split #-}

module synthetic-homotopy-theory.24-pushouts where

open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cones-pullbacks
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.unit-type
open import foundation.universal-property-pullbacks
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts

-- Exercises

-- Exercise 13.1

-- Exercise 13.2

is-equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f →
  ({l : Level} → universal-property-pushout l f g c) → is-equiv (pr1 (pr2 c))
is-equiv-universal-property-pushout
  {A = A} {B} f g (pair i (pair j H)) is-equiv-f up-c =
  is-equiv-is-equiv-precomp j
    ( λ l T →
      is-equiv-is-pullback'
        ( λ (h : A → T) → h ∘ f)
        ( λ (h : B → T) → h ∘ g)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv f is-equiv-f T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) up-c T))

equiv-universal-property-pushout :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (e : S ≃ A) (g : S → B) (c : cocone (map-equiv e) g C) →
  ({l : Level} → universal-property-pushout l (map-equiv e) g c) →
  B ≃ C
equiv-universal-property-pushout e g c up-c =
  pair
    ( pr1 (pr2 c))
    ( is-equiv-universal-property-pushout
      ( map-equiv e)
      ( g)
      ( c)
      ( is-equiv-map-equiv e)
      ( up-c))

is-equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g →
  ({l : Level} → universal-property-pushout l f g c) →
  is-equiv (pr1 c)
is-equiv-universal-property-pushout' f g (pair i (pair j H)) is-equiv-g up-c =
  is-equiv-is-equiv-precomp i
    ( λ l T →
      is-equiv-is-pullback
        ( precomp f T)
        ( precomp g T)
        ( cone-pullback-property-pushout f g (pair i (pair j H)) T)
        ( is-equiv-precomp-is-equiv g is-equiv-g T)
        ( pullback-property-pushout-universal-property-pushout
          l f g (pair i (pair j H)) up-c T))

equiv-universal-property-pushout' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (e : S ≃ B) (c : cocone f (map-equiv e) C) →
  ({l : Level} → universal-property-pushout l f (map-equiv e) c) →
  A ≃ C
equiv-universal-property-pushout' f e c up-c =
  pair
    ( pr1 c)
    ( is-equiv-universal-property-pushout'
      ( f)
      ( map-equiv e)
      ( c)
      ( is-equiv-map-equiv e)
      ( up-c))

universal-property-pushout-is-equiv :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv f → is-equiv (pr1 (pr2 c)) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv f g (pair i (pair j H)) is-equiv-f is-equiv-j {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv'
      ( λ h → h ∘ f)
      ( λ h → h ∘ g)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv f is-equiv-f T)
      ( is-equiv-precomp-is-equiv j is-equiv-j T))

universal-property-pushout-is-equiv' :
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : S → A) (g : S → B) (c : cocone f g C) →
  is-equiv g → is-equiv (pr1 c) →
  ({l : Level} → universal-property-pushout l f g c)
universal-property-pushout-is-equiv'
  f g (pair i (pair j H)) is-equiv-g is-equiv-i {l} =
  let c = (pair i (pair j H)) in
  universal-property-pushout-pullback-property-pushout l f g c
    ( λ T → is-pullback-is-equiv
      ( precomp f T)
      ( precomp g T)
      ( cone-pullback-property-pushout f g c T)
      ( is-equiv-precomp-is-equiv g is-equiv-g T)
      ( is-equiv-precomp-is-equiv i is-equiv-i T))

is-equiv-cofiber-point :
  {l : Level} {B : UU l} (b : B) →
  is-equiv (pr1 (cocone-pushout (const unit B b) (const unit unit star)))
is-equiv-cofiber-point {l} {B} b =
  is-equiv-universal-property-pushout'
    ( const unit B b)
    ( const unit unit star)
    ( cocone-pushout (const unit B b) (const unit unit star))
    ( is-equiv-is-contr (const unit unit star) is-contr-unit is-contr-unit)
    ( up-pushout (const unit B b) (const unit unit star))

-- Exercise 16.2

-- ev-disjunction :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   ((type-Prop P) * (type-Prop Q) → (type-Prop R)) →
--   (type-Prop P → type-Prop R) × (type-Prop Q → type-Prop R)
-- ev-disjunction P Q R f =
--   pair
--     ( f ∘ (inl-join (type-Prop P) (type-Prop Q)))
--     ( f ∘ (inr-join (type-Prop P) (type-Prop Q)))

-- comparison-ev-disjunction :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   cocone-join (type-Prop P) (type-Prop Q) (type-Prop R)

-- universal-property-disjunction-join-prop :
--   {l1 l2 l3 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) (R : UU-Prop l3) →
--   is-equiv (ev-disjunction P Q R)
```
