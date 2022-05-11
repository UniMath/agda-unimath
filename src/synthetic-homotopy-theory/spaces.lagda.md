---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.spaces where

open import foundation.cartesian-product-types
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.24-pushouts

--------------------------------------------------------------------------------

-- Examples of pushouts

{- The cofiber of a map. -}

cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
cofiber {A = A} f = pushout f (const A unit star)

cocone-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  cocone f (const A unit star) (cofiber f)
cocone-cofiber {A = A} f = cocone-pushout f (const A unit star)

inl-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → B → cofiber f
inl-cofiber {A = A} f = pr1 (cocone-cofiber f)

inr-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → unit → cofiber f
inr-cofiber f = pr1 (pr2 (cocone-cofiber f))

pt-cofiber :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → cofiber f
pt-cofiber {A = A} f = inr-cofiber f star

cofiber-ptd :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → Pointed-Type (l1 ⊔ l2)
cofiber-ptd f = pair (cofiber f) (pt-cofiber f)

up-cofiber :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  ( {l : Level} →
    universal-property-pushout l f (const A unit star) (cocone-cofiber f))
up-cofiber {A = A} f = up-pushout f (const A unit star)

_*_ :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A * B = pushout (pr1 {A = A} {B = λ x → B}) pr2

cocone-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  cocone (pr1 {A = A} {B = λ x → B}) pr2 (A * B)
cocone-join A B = cocone-pushout pr1 pr2

up-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  ( {l : Level} → universal-property-pushout l
    ( pr1 {A = A} {B = λ x → B}) pr2 (cocone-join A B))
up-join A B = up-pushout pr1 pr2

inl-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → A → A * B
inl-join A B = pr1 (cocone-join A B)

inr-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → B → A * B
inr-join A B = pr1 (pr2 (cocone-join A B))

glue-join :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (t : A × B) →
  Id (inl-join A B (pr1 t)) (inr-join A B (pr2 t))
glue-join A B = pr2 (pr2 (cocone-join A B))

_∨_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
A ∨ B =
  pair
    ( pushout
      ( const unit (pr1 A) (pr2 A))
      ( const unit (pr1 B) (pr2 B)))
    ( inl-pushout
      ( const unit (pr1 A) (pr2 A))
      ( const unit (pr1 B) (pr2 B))
      ( pr2 A))

indexed-wedge :
  {l1 l2 : Level} (I : UU l1) (A : I → Pointed-Type l2) → Pointed-Type (l1 ⊔ l2)
indexed-wedge I A =
  pair
    ( cofiber (λ i → pair i (pr2 (A i))))
    ( pt-cofiber (λ i → pair i (pr2 (A i))))

wedge-inclusion :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  pr1 (A ∨ B) → (pr1 A) × (pr1 B)
wedge-inclusion {l1} {l2} (pair A a) (pair B b) =
  map-inv-is-equiv
    ( up-pushout
      ( const unit A a)
      ( const unit B b)
      ( A × B))
    ( pair
      ( λ x → pair x b)
      ( pair
        ( λ y → pair a y)
        ( refl-htpy)))

is-contr-cofiber-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-contr (cofiber f)
is-contr-cofiber-is-equiv {A = A} {B} f is-equiv-f =
  is-contr-is-equiv'
    ( unit)
    ( pr1 (pr2 (cocone-cofiber f)))
    ( is-equiv-universal-property-pushout
      ( f)
      ( const A unit star)
      ( cocone-cofiber f)
      ( is-equiv-f)
      ( up-cofiber f))
    ( is-contr-unit)

is-equiv-inr-join-empty :
  {l : Level} (X : UU l) → is-equiv (inr-join empty X)
is-equiv-inr-join-empty X =
  is-equiv-universal-property-pushout
    ( pr1 {A = empty} {B = λ t → X})
    ( pr2)
    ( cocone-join empty X)
    ( is-equiv-pr1-prod-empty X)
    ( up-join empty X)

left-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (empty * X)
left-unit-law-join X =
  pair (inr-join empty X) (is-equiv-inr-join-empty X)

is-equiv-inl-join-empty :
  {l : Level} (X : UU l) → is-equiv (inl-join X empty)
is-equiv-inl-join-empty X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join X empty)
    ( is-equiv-pr2-prod-empty X)
    ( up-join X empty)

right-unit-law-join :
  {l : Level} (X : UU l) → X ≃ (X * empty)
right-unit-law-join X =
  pair (inl-join X empty) (is-equiv-inl-join-empty X)

is-equiv-inl-join-unit :
  {l : Level} (X : UU l) → is-equiv (inl-join unit X)
is-equiv-inl-join-unit X =
  is-equiv-universal-property-pushout'
    ( pr1)
    ( pr2)
    ( cocone-join unit X)
    ( is-equiv-map-left-unit-law-prod)
    ( up-join unit X)

left-zero-law-join :
  {l : Level} (X : UU l) → is-contr (unit * X)
left-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( pair (inl-join unit X) (is-equiv-inl-join-unit X))
    ( is-contr-unit)
    
is-equiv-inr-join-unit :
  {l : Level} (X : UU l) → is-equiv (inr-join X unit)
is-equiv-inr-join-unit X =
  is-equiv-universal-property-pushout
    ( pr1)
    ( pr2)
    ( cocone-join X unit)
    ( is-equiv-map-right-unit-law-prod)
    ( up-join X unit)

right-zero-law-join :
  {l : Level} (X : UU l) → is-contr (X * unit)
right-zero-law-join X =
  is-contr-equiv'
    ( unit)
    ( pair (inr-join X unit) (is-equiv-inr-join-unit X))
    ( is-contr-unit)

unit-pt : Pointed-Type lzero
unit-pt = pair unit star

is-contr-pt :
  {l : Level} → Pointed-Type l → UU l
is-contr-pt A = is-contr (pr1 A)
```
