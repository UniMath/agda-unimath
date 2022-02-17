# Set truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.set-truncations where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.effective-maps-equivalence-relations using
  ( is-surjective-and-effective; is-effective)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.empty-types using (empty; empty-Set; is-empty)
open import foundation.equivalences using
  ( _≃_; is-equiv; map-inv-equiv; map-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id)
open import foundation.mere-equality using
  ( mere-eq-Eq-Rel; reflects-mere-eq; mere-eq; mere-eq-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel)
open import foundation.sets using
  ( is-set; type-Set; UU-Set; precomp-Set; type-hom-Set; is-set-type-Set;
    is-set-is-contr)
open import foundation.slice using
  ( hom-slice)
open import foundation.surjective-maps using (is-surjective)
open import foundation.uniqueness-set-truncations using
  ( is-equiv-is-set-truncation-is-set-truncation;
    is-set-truncation-is-equiv-is-set-truncation;
    is-set-truncation-is-set-truncation-is-equiv; uniqueness-set-truncation)
open import foundation.unit-type using (unit; unit-Set)
open import foundation.universal-property-image using (is-image)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient; is-surjective-and-effective-is-set-quotient;
    emb-is-surjective-and-effective; triangle-emb-is-surjective-and-effective;
    is-image-is-surjective-and-effective)
open import foundation.universal-property-set-truncation using
  ( is-set-truncation; universal-property-set-truncation;
    universal-property-is-set-truncation; map-is-set-truncation;
    triangle-is-set-truncation; precomp-Π-Set;
    dependent-universal-property-set-truncation;
    dependent-universal-property-is-set-truncation;
    is-set-quotient-is-set-truncation; is-set-truncation-id)
open import foundation.universe-levels using (Level; UU)
```

## Idea

The set truncation of a type `A` is a map `η : A → trunc-Set A` that satisfies the universal property of set truncations.

## Postulates

```agda
postulate type-trunc-Set : {l : Level} → UU l → UU l

postulate
  is-set-type-trunc-Set : {l : Level} {A : UU l} → is-set (type-trunc-Set A)

trunc-Set : {l : Level} → UU l → UU-Set l
pr1 (trunc-Set A) = type-trunc-Set A
pr2 (trunc-Set A) = is-set-type-trunc-Set

postulate unit-trunc-Set : {l : Level} {A : UU l} → A → type-trunc-Set A

postulate
  is-set-truncation-trunc-Set :
    {l1 l2 : Level} (A : UU l1) →
    is-set-truncation l2 (trunc-Set A) unit-trunc-Set
```

## Properties

```agda
equiv-universal-property-trunc-Set :
  {l1 l2 : Level} (A : UU l1) (B : UU-Set l2) →
  (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
equiv-universal-property-trunc-Set A B =
  pair
    ( precomp-Set unit-trunc-Set B)
    ( is-set-truncation-trunc-Set A B)

abstract
  universal-property-trunc-Set : {l1 l2 : Level} (A : UU l1) →
    universal-property-set-truncation l2
      ( trunc-Set A)
      ( unit-trunc-Set)
  universal-property-trunc-Set A =
    universal-property-is-set-truncation _
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-set-truncation-trunc-Set A)

map-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (A → type-Set B) → type-hom-Set (trunc-Set A) B
map-universal-property-trunc-Set {A = A} B f =
  map-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)
    ( B)
    ( f)

triangle-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (f : A → type-Set B) →
  (map-universal-property-trunc-Set B f ∘ unit-trunc-Set) ~ f
triangle-universal-property-trunc-Set {A = A} B f =
  triangle-is-set-truncation
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-set-truncation-trunc-Set A)
    ( B)
    ( f)

apply-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (t : type-trunc-Set A) (B : UU-Set l2) →
  (A → type-Set B) → type-Set B
apply-universal-property-trunc-Set t B f =
  map-universal-property-trunc-Set B f t

abstract
  dependent-universal-property-trunc-Set :
    {l1 : Level} {A : UU l1} {l : Level} →
    dependent-universal-property-set-truncation l (trunc-Set A) unit-trunc-Set
  dependent-universal-property-trunc-Set {A = A} =
    dependent-universal-property-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

equiv-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1} (B : type-trunc-Set A → UU-Set l2) →
  ((x : type-trunc-Set A) → type-Set (B x)) ≃
  ((a : A) → type-Set (B (unit-trunc-Set a)))
pr1 (equiv-dependent-universal-property-trunc-Set B) =
  precomp-Π-Set unit-trunc-Set B
pr2 (equiv-dependent-universal-property-trunc-Set B) =
  dependent-universal-property-trunc-Set B

apply-dependent-universal-property-trunc-Set :
  {l1 l2 : Level} {A : UU l1}
  (B : type-trunc-Set A → UU-Set l2) →
  ((x : A) → type-Set (B (unit-trunc-Set x))) →
  (x : type-trunc-Set A) → type-Set (B x)
apply-dependent-universal-property-trunc-Set B =
  map-inv-equiv (equiv-dependent-universal-property-trunc-Set B)
```

```agda
reflecting-map-mere-eq-unit-trunc-Set :
  {l : Level} (A : UU l) →
  reflecting-map-Eq-Rel (mere-eq-Eq-Rel A) (type-trunc-Set A)
reflecting-map-mere-eq-unit-trunc-Set A =
  pair unit-trunc-Set (reflects-mere-eq (trunc-Set A) unit-trunc-Set)

abstract
  is-set-quotient-trunc-Set :
    {l1 l2 : Level} (A : UU l1) →
    is-set-quotient l2
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( reflecting-map-mere-eq-unit-trunc-Set A)
  is-set-quotient-trunc-Set A =
    is-set-quotient-is-set-truncation
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( λ {l} → is-set-truncation-trunc-Set A)

abstract
  is-surjective-and-effective-unit-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-surjective-and-effective (mere-eq-Eq-Rel A) unit-trunc-Set
  is-surjective-and-effective-unit-trunc-Set A =
    is-surjective-and-effective-is-set-quotient
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( reflects-mere-eq (trunc-Set A) unit-trunc-Set)
      ( λ {l} → is-set-quotient-trunc-Set A)

abstract
  is-surjective-unit-trunc-Set :
    {l1 : Level} (A : UU l1) → is-surjective (unit-trunc-Set {A = A})
  is-surjective-unit-trunc-Set A =
    pr1 (is-surjective-and-effective-unit-trunc-Set A)

abstract
  is-effective-unit-trunc-Set :
    {l1 : Level} (A : UU l1) →
    is-effective (mere-eq-Eq-Rel A) (unit-trunc-Set {A = A})
  is-effective-unit-trunc-Set A =
    pr2 (is-surjective-and-effective-unit-trunc-Set A)

abstract
  apply-effectiveness-unit-trunc-Set :
    {l1 : Level} {A : UU l1} {x y : A} →
    Id (unit-trunc-Set x) (unit-trunc-Set y) → mere-eq x y
  apply-effectiveness-unit-trunc-Set {A = A} {x} {y} =
    map-equiv (is-effective-unit-trunc-Set A x y)

abstract
  apply-effectiveness-unit-trunc-Set' :
    {l1 : Level} {A : UU l1} {x y : A} →
    mere-eq x y → Id (unit-trunc-Set x) (unit-trunc-Set y)
  apply-effectiveness-unit-trunc-Set' {A = A} {x} {y} =
    map-inv-equiv (is-effective-unit-trunc-Set A x y)

emb-trunc-Set :
  {l1 : Level} (A : UU l1) → type-trunc-Set A ↪ (A → UU-Prop l1)
emb-trunc-Set A =
  emb-is-surjective-and-effective
    ( mere-eq-Eq-Rel A)
    ( trunc-Set A)
    ( unit-trunc-Set)
    ( is-surjective-and-effective-unit-trunc-Set A)

hom-slice-trunc-Set :
  {l1 : Level} (A : UU l1) →
  hom-slice (mere-eq-Prop {A = A}) (map-emb (emb-trunc-Set A))
hom-slice-trunc-Set A =
  pair
    ( unit-trunc-Set)
    ( triangle-emb-is-surjective-and-effective
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A))

abstract
  is-image-trunc-Set :
    {l1 l2 : Level} (A : UU l1) →
    is-image l2
      ( mere-eq-Prop {A = A})
      ( emb-trunc-Set A)
      ( hom-slice-trunc-Set A)
  is-image-trunc-Set A =
    is-image-is-surjective-and-effective
      ( mere-eq-Eq-Rel A)
      ( trunc-Set A)
      ( unit-trunc-Set)
      ( is-surjective-and-effective-unit-trunc-Set A)

-- Uniqueness of trunc-Set

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set B (trunc-Set A)} (H : (h ∘ f) ~ unit-trunc-Set)
  where

  abstract
    is-equiv-is-set-truncation' :
      ({l : Level} → is-set-truncation l B f) → is-equiv h
    is-equiv-is-set-truncation' Sf =
      is-equiv-is-set-truncation-is-set-truncation
        ( B)
        ( f)
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( H)
        ( Sf)
        ( λ {h} → is-set-truncation-trunc-Set A)

  abstract
    is-set-truncation-is-equiv' :
      is-equiv h → ({l : Level} → is-set-truncation l B f)
    is-set-truncation-is-equiv' Eh =
      is-set-truncation-is-equiv-is-set-truncation
        ( B)
        ( f)
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( H)
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Eh)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  {h : type-hom-Set (trunc-Set A) B} (H : (h ∘ unit-trunc-Set) ~ f)
  where

  abstract
    is-equiv-is-set-truncation :
      ({l : Level} → is-set-truncation l B f) → is-equiv h
    is-equiv-is-set-truncation Sf =
      is-equiv-is-set-truncation-is-set-truncation
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( B)
        ( f)
        ( H)
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Sf)

  abstract
    is-set-truncation-is-equiv :
      is-equiv h → ({l : Level} → is-set-truncation l B f)
    is-set-truncation-is-equiv Eh =
      is-set-truncation-is-set-truncation-is-equiv
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( B)
        ( f)
        ( H)
        ( Eh)
        ( λ {l} → is-set-truncation-trunc-Set A)

abstract
  is-equiv-unit-trunc-Set :
    {l : Level} (A : UU-Set l) → is-equiv (unit-trunc-Set {A = type-Set A})
  is-equiv-unit-trunc-Set A =
    is-equiv-is-set-truncation' A id refl-htpy
      ( is-set-truncation-id (is-set-type-Set A))

equiv-unit-trunc-Set :
  {l : Level} (A : UU-Set l) → type-Set A ≃ type-trunc-Set (type-Set A)
equiv-unit-trunc-Set A =
  pair unit-trunc-Set (is-equiv-unit-trunc-Set A)

equiv-unit-trunc-empty-Set : empty ≃ type-trunc-Set empty
equiv-unit-trunc-empty-Set = equiv-unit-trunc-Set empty-Set

abstract
  is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty A → is-empty (type-trunc-Set A)
  is-empty-trunc-Set f x = apply-universal-property-trunc-Set x empty-Set f

abstract
  is-empty-is-empty-trunc-Set :
    {l : Level} {A : UU l} → is-empty (type-trunc-Set A) → is-empty A
  is-empty-is-empty-trunc-Set f = f ∘ unit-trunc-Set

equiv-unit-trunc-unit-Set : unit ≃ type-trunc-Set unit
equiv-unit-trunc-unit-Set = equiv-unit-trunc-Set unit-Set

abstract
  is-contr-trunc-Set :
    {l : Level} {A : UU l} → is-contr A → is-contr (type-trunc-Set A)
  is-contr-trunc-Set {l} {A} H =
    is-contr-equiv'
      ( A)
      ( equiv-unit-trunc-Set (pair A (is-set-is-contr H)))
      ( H)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  abstract
    uniqueness-trunc-Set :
      is-contr
        ( Σ (type-trunc-Set A ≃ type-Set B)
        ( λ e → (map-equiv e ∘ unit-trunc-Set) ~ f))
    uniqueness-trunc-Set =
      uniqueness-set-truncation (trunc-Set A) unit-trunc-Set B f
        ( λ {l} → is-set-truncation-trunc-Set A)
        ( Sf)

  equiv-uniqueness-trunc-Set : type-trunc-Set A ≃ type-Set B
  equiv-uniqueness-trunc-Set =
    pr1 (center uniqueness-trunc-Set)

  map-equiv-uniqueness-trunc-Set : type-trunc-Set A → type-Set B
  map-equiv-uniqueness-trunc-Set =
    map-equiv equiv-uniqueness-trunc-Set

  triangle-uniqueness-trunc-Set :
    (map-equiv-uniqueness-trunc-Set ∘ unit-trunc-Set) ~ f
  triangle-uniqueness-trunc-Set =
    pr2 (center uniqueness-trunc-Set)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  (Sf : {l : Level} → is-set-truncation l B f)
  where

  abstract
    uniqueness-trunc-Set' :
      is-contr
        ( Σ ( type-Set B ≃ type-trunc-Set A)
            ( λ e → (map-equiv e ∘ f) ~ unit-trunc-Set))
    uniqueness-trunc-Set' =
      uniqueness-set-truncation B f (trunc-Set A) unit-trunc-Set Sf
        ( λ {l} → is-set-truncation-trunc-Set A)

  equiv-uniqueness-trunc-Set' : type-Set B ≃ type-trunc-Set A
  equiv-uniqueness-trunc-Set' =
    pr1 (center uniqueness-trunc-Set')

  map-equiv-uniqueness-trunc-Set' : type-Set B → type-trunc-Set A
  map-equiv-uniqueness-trunc-Set' =
    map-equiv equiv-uniqueness-trunc-Set'
  
  triangle-uniqueness-trunc-Set' :
    (map-equiv-uniqueness-trunc-Set' ∘ f) ~ unit-trunc-Set
  triangle-uniqueness-trunc-Set' =
    pr2 (center uniqueness-trunc-Set')
```
