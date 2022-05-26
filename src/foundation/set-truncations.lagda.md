---
title: Set truncations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.set-truncations where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; ev-pair)
open import foundation.effective-maps-equivalence-relations using
  ( is-surjective-and-effective; is-effective)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.empty-types using (empty; empty-Set; is-empty)
open import foundation.equality-coproduct-types using
  ( coprod-Set)
open import foundation.equivalences using
  ( _≃_; is-equiv; map-inv-equiv; map-equiv; is-equiv-right-factor';
    is-equiv-comp'; is-equiv-htpy-equiv; _∘e_; issec-map-inv-equiv)
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-cartesian-product-types using
  ( map-prod; is-equiv-map-prod)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π)
open import foundation.functoriality-dependent-pair-types using (tot)
open import foundation.functoriality-function-types using (equiv-postcomp)
open import foundation.homotopies using (_~_; refl-htpy; inv-htpy)
open import foundation.identity-types using (Id)
open import foundation.mere-equality using
  ( mere-eq-Eq-Rel; reflects-mere-eq; mere-eq; mere-eq-Prop)
open import foundation.propositions using (UU-Prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel)
open import foundation.sets using
  ( is-set; type-Set; UU-Set; precomp-Set; type-hom-Set; is-set-type-Set;
    is-set-is-contr; type-equiv-Set; prod-Set; Π-Set')
open import foundation.slice using
  ( hom-slice)
open import foundation.surjective-maps using (is-surjective)
open import foundation.uniqueness-set-truncations using
  ( is-equiv-is-set-truncation-is-set-truncation;
    is-set-truncation-is-equiv-is-set-truncation;
    is-set-truncation-is-set-truncation-is-equiv; uniqueness-set-truncation)
open import foundation.unit-type using (unit; unit-Set)
open import foundation.universal-property-coproduct-types using
  ( ev-inl-inr; universal-property-coprod)
open import foundation.universal-property-dependent-pair-types using
  ( is-equiv-ev-pair; equiv-ev-pair)
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

### The dependent universal property of set truncations

```agda
module _
  {l1 : Level} {A : UU l1}
  where
  
  abstract
    dependent-universal-property-trunc-Set :
      {l : Level} →
      dependent-universal-property-set-truncation l (trunc-Set A) unit-trunc-Set
    dependent-universal-property-trunc-Set =
      dependent-universal-property-is-set-truncation
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( λ {l} → is-set-truncation-trunc-Set A)

  equiv-dependent-universal-property-trunc-Set :
    {l2 : Level} (B : type-trunc-Set A → UU-Set l2) →
    ((x : type-trunc-Set A) → type-Set (B x)) ≃
    ((a : A) → type-Set (B (unit-trunc-Set a)))
  pr1 (equiv-dependent-universal-property-trunc-Set B) =
    precomp-Π-Set unit-trunc-Set B
  pr2 (equiv-dependent-universal-property-trunc-Set B) =
    dependent-universal-property-trunc-Set B
  
  Π-trunc-Set :
    {l2 : Level} (B : type-trunc-Set A → UU-Set l2) →
    (f : (a : A) → type-Set (B (unit-trunc-Set a))) →
    Σ ( (x : type-trunc-Set A) → type-Set (B x))
      ( λ g → (g ∘ unit-trunc-Set) ~ f)
  pr1 (Π-trunc-Set B f) =
    map-inv-equiv (equiv-dependent-universal-property-trunc-Set B) f
  pr2 (Π-trunc-Set B f) =
    htpy-eq
      ( issec-map-inv-equiv (equiv-dependent-universal-property-trunc-Set B) f)

  function-dependent-universal-property-trunc-Set :
    {l2 : Level} (B : type-trunc-Set A → UU-Set l2) →
    ((x : A) → type-Set (B (unit-trunc-Set x))) →
    (x : type-trunc-Set A) → type-Set (B x)
  function-dependent-universal-property-trunc-Set B f = pr1 (Π-trunc-Set B f)

  compute-dependent-universal-property-trunc-Set :
    {l2 : Level} (B : type-trunc-Set A → UU-Set l2) →
    (f : (x : A) → type-Set (B (unit-trunc-Set x))) →
    (function-dependent-universal-property-trunc-Set B f ∘ unit-trunc-Set) ~ f
  compute-dependent-universal-property-trunc-Set B f = pr2 (Π-trunc-Set B f)

  apply-dependent-universal-property-trunc-Set :
    {l2 : Level} (B : type-trunc-Set A → UU-Set l2) →
    ((x : A) → type-Set (B (unit-trunc-Set x))) →
    (x : type-trunc-Set A) → type-Set (B x)
  apply-dependent-universal-property-trunc-Set B =
    map-inv-equiv (equiv-dependent-universal-property-trunc-Set B)
```

### The universal property of set truncations

```agda
module _
  {l1 : Level} {A : UU l1}
  where
  
  equiv-universal-property-trunc-Set :
    {l2 : Level} (B : UU-Set l2) →
    (type-trunc-Set A → type-Set B) ≃ (A → type-Set B)
  pr1 (equiv-universal-property-trunc-Set B) = precomp-Set unit-trunc-Set B
  pr2 (equiv-universal-property-trunc-Set B) =
    is-set-truncation-trunc-Set A B

  abstract
    universal-property-trunc-Set :
      {l2 : Level} →
      universal-property-set-truncation l2
        ( trunc-Set A)
        ( unit-trunc-Set)
    universal-property-trunc-Set =
      universal-property-is-set-truncation _
        ( trunc-Set A)
        ( unit-trunc-Set)
        ( is-set-truncation-trunc-Set A)

  Map-trunc-Set :
    {l2 : Level} (B : UU-Set l2) (f : A → type-Set B) →
    Σ (type-trunc-Set A → type-Set B) (λ g → (g ∘ unit-trunc-Set) ~ f)
  pr1 (Map-trunc-Set B f) =
    map-inv-equiv (equiv-universal-property-trunc-Set B) f
  pr2 (Map-trunc-Set B f) =
    htpy-eq (issec-map-inv-equiv (equiv-universal-property-trunc-Set B) f)

  map-universal-property-trunc-Set :
    {l2 : Level} (B : UU-Set l2) →
    (A → type-Set B) → type-hom-Set (trunc-Set A) B
  map-universal-property-trunc-Set B f = pr1 (Map-trunc-Set B f)

  triangle-universal-property-trunc-Set :
    {l2 : Level} (B : UU-Set l2) (f : A → type-Set B) →
    (map-universal-property-trunc-Set B f ∘ unit-trunc-Set) ~ f
  triangle-universal-property-trunc-Set B f = pr2 (Map-trunc-Set B f)

  apply-universal-property-trunc-Set :
    {l2 : Level} (t : type-trunc-Set A) (B : UU-Set l2) →
    (A → type-Set B) → type-Set B
  apply-universal-property-trunc-Set t B f =
    map-universal-property-trunc-Set B f t

{-
module _
  where

  universal-property-𝕊¹ :
    {l : Level} → universal-property-circle l free-loop-𝕊¹
  universal-property-𝕊¹ =
    universal-property-dependent-universal-property-circle
      free-loop-𝕊¹
      dependent-universal-property-𝕊¹

  uniqueness-universal-property-𝕊¹ :
    {l : Level} {X : UU l} (α : free-loop X) →
    is-contr
      ( Σ ( 𝕊¹ → X)
          ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) α))
  uniqueness-universal-property-𝕊¹ {l} {X} =
    uniqueness-universal-property-circle free-loop-𝕊¹ universal-property-𝕊¹ X

  module _
    {l : Level} {X : UU l} (x : X) (α : Id x x)
    where

    Map-𝕊¹ : UU l
    Map-𝕊¹ =
      Σ ( 𝕊¹ → X)
        ( λ h → Eq-free-loop (ev-free-loop free-loop-𝕊¹ X h) (pair x α))

    apply-universal-property-𝕊¹ : Map-𝕊¹
    apply-universal-property-𝕊¹ =
      center (uniqueness-universal-property-𝕊¹ (pair x α))
      
    map-apply-universal-property-𝕊¹ : 𝕊¹ → X
    map-apply-universal-property-𝕊¹ =
      pr1 apply-universal-property-𝕊¹

    base-universal-property-𝕊¹ :
      Id (map-apply-universal-property-𝕊¹ base-𝕊¹) x
    base-universal-property-𝕊¹ =
      pr1 (pr2 apply-universal-property-𝕊¹)

    loop-universal-property-𝕊¹ :
      Id ( ap map-apply-universal-property-𝕊¹ loop-𝕊¹ ∙
           base-universal-property-𝕊¹)
         ( base-universal-property-𝕊¹ ∙ α)
    loop-universal-property-𝕊¹ =
      pr2 (pr2 apply-universal-property-𝕊¹)
-}
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

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-coprod-Set :
      is-contr
        ( Σ ( type-equiv-Set
              ( trunc-Set (coprod A B))
              ( coprod-Set (trunc-Set A) (trunc-Set B)))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-coprod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-coprod-Set =
      uniqueness-trunc-Set
        ( coprod-Set (trunc-Set A) (trunc-Set B))
        ( map-coprod unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-inl-inr (λ x → type-Set C))
            ( precomp-Set (map-coprod unit-trunc-Set unit-trunc-Set) C)
            ( universal-property-coprod (type-Set C))
            ( is-equiv-comp'
              ( map-prod
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C))
              ( ev-inl-inr (λ x → type-Set C))
              ( universal-property-coprod (type-Set C))
              ( is-equiv-map-prod
                ( precomp-Set unit-trunc-Set C)
                ( precomp-Set unit-trunc-Set C)
                ( is-set-truncation-trunc-Set A C)
                ( is-set-truncation-trunc-Set B C))))

  equiv-distributive-trunc-coprod-Set :
    type-equiv-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  equiv-distributive-trunc-coprod-Set =
    pr1 (center distributive-trunc-coprod-Set)

  map-equiv-distributive-trunc-coprod-Set :
    type-hom-Set
      ( trunc-Set (coprod A B))
      ( coprod-Set (trunc-Set A) (trunc-Set B))
  map-equiv-distributive-trunc-coprod-Set =
    map-equiv equiv-distributive-trunc-coprod-Set

  triangle-distributive-trunc-coprod-Set :
    ( map-equiv-distributive-trunc-coprod-Set ∘ unit-trunc-Set) ~
    ( map-coprod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-coprod-Set =
    pr2 (center distributive-trunc-coprod-Set)

-- Set truncations of Σ-types

module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  abstract
    trunc-Σ-Set :
      is-contr
        ( Σ ( type-trunc-Set (Σ A B) ≃
              type-trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))))
    trunc-Σ-Set =
      uniqueness-trunc-Set
        ( trunc-Set (Σ A (λ x → type-trunc-Set (B x))))
        ( unit-trunc-Set ∘ tot (λ x → unit-trunc-Set))
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-pair)
            ( precomp-Set (unit-trunc-Set ∘ tot (λ x → unit-trunc-Set)) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-map-Π
                  ( λ x → equiv-universal-property-trunc-Set C)) ∘e
                ( ( equiv-ev-pair) ∘e
                  ( equiv-universal-property-trunc-Set C)))
              ( refl-htpy)))

  equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) ≃ type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  equiv-trunc-Σ-Set =
    pr1 (center trunc-Σ-Set)

  map-equiv-trunc-Σ-Set :
    type-trunc-Set (Σ A B) → type-trunc-Set (Σ A (λ x → type-trunc-Set (B x)))
  map-equiv-trunc-Σ-Set =
    map-equiv equiv-trunc-Σ-Set

-- trunc-Set distributes over products

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    distributive-trunc-prod-Set :
      is-contr
        ( Σ ( type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B))
            ( λ e →
              ( map-equiv e ∘ unit-trunc-Set) ~
              ( map-prod unit-trunc-Set unit-trunc-Set)))
    distributive-trunc-prod-Set =
      uniqueness-trunc-Set
        ( prod-Set (trunc-Set A) (trunc-Set B))
        ( map-prod unit-trunc-Set unit-trunc-Set)
        ( λ {l} C →
          is-equiv-right-factor'
            ( ev-pair)
            ( precomp-Set (map-prod unit-trunc-Set unit-trunc-Set) C)
            ( is-equiv-ev-pair)
            ( is-equiv-htpy-equiv
              ( ( equiv-universal-property-trunc-Set (Π-Set' B (λ y → C))) ∘e
                ( ( equiv-postcomp
                    ( type-trunc-Set A)
                    (equiv-universal-property-trunc-Set C)) ∘e
                  ( equiv-ev-pair)))
              ( refl-htpy)))

  equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) ≃ ( type-trunc-Set A × type-trunc-Set B)
  equiv-distributive-trunc-prod-Set =
    pr1 (center distributive-trunc-prod-Set)

  map-equiv-distributive-trunc-prod-Set :
    type-trunc-Set (A × B) → type-trunc-Set A × type-trunc-Set B
  map-equiv-distributive-trunc-prod-Set =
    map-equiv equiv-distributive-trunc-prod-Set

  triangle-distributive-trunc-prod-Set :
    ( map-equiv-distributive-trunc-prod-Set ∘ unit-trunc-Set) ~
    ( map-prod unit-trunc-Set unit-trunc-Set)
  triangle-distributive-trunc-prod-Set =
    pr2 (center distributive-trunc-prod-Set)
```
