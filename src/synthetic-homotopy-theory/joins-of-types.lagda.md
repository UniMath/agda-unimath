---
title: Joins of types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module synthetic-homotopy-theory.joins-of-types where

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.24-pushouts
open import synthetic-homotopy-theory.cocones-pushouts
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts

```

## Idea

The join of `A` and `B` is the pushout of the span `A ← A × B → B`.

## Definition

```agda
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
```

## Properties

```agda
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
```
