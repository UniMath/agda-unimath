---
title: The universal property of set truncations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-set-truncation where

open import foundation.contractible-maps using
  ( is-equiv-is-contr-map; is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-equiv; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; ind-Σ)
open import foundation.equivalences using
  ( is-equiv; is-equiv-precomp-is-equiv; is-equiv-id; _≃_; map-equiv;
    is-equiv-map-equiv; is-equiv-equiv; is-equiv-comp; is-equiv-right-factor)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot; is-fiberwise-equiv-is-equiv-map-Σ)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (_＝_; refl)
open import foundation.mere-equality using
  ( mere-eq-Eq-Rel; reflecting-map-mere-eq; reflects-mere-eq)
open import foundation.propositions using (is-proof-irrelevant-is-prop)
open import foundation.reflecting-maps-equivalence-relations using
  ( is-prop-reflects-Eq-Rel)
open import foundation.sets using
  ( UU-Set; type-Set; precomp-Set; type-hom-Set; is-set; Σ-Set)
open import foundation.type-arithmetic-dependent-pair-types using
  ( is-equiv-pr1-is-contr)
open import foundation.type-theoretic-principle-of-choice using
  ( inv-distributive-Π-Σ)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient; precomp-Set-Quotient)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import foundation-core.equivalence-relations using (Eq-Rel)
```

## Idea

A map `f : A → B` into a set `B` satisfies the universal property of the set truncation of `A` if any map `A → C` into a set `C` extends uniquely along `f` to a map `B → C`.

## Definition

### The condition for a map into a set to be a set truncation

```agda
is-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  ( A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-set-truncation l B f =
  (C : UU-Set l) → is-equiv (precomp-Set f C)
```

### The universal property of set truncations

```agda
universal-property-set-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (B : UU-Set l2) (f : A → type-Set B) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-set-truncation l {A = A} B f =
  (C : UU-Set l) (g : A → type-Set C) →
  is-contr (Σ (type-hom-Set B C) (λ h → (h ∘ f) ~  g))
```

### The dependent universal property of set truncations

```agda
precomp-Π-Set :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU-Set l3) →
  ((b : B) → type-Set (C b)) → ((a : A) → type-Set (C (f a)))
precomp-Π-Set f C h a = h (f a)

dependent-universal-property-set-truncation :
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
dependent-universal-property-set-truncation l B f =
  (X : type-Set B → UU-Set l) → is-equiv (precomp-Π-Set f X)
```

## Properties

### A map into a set is a set truncation if it satisfies the universal property

```agda
abstract
  is-set-truncation-universal-property :
    (l : Level) {l1 l2 : Level} {A : UU l1}
    (B : UU-Set l2) (f : A → type-Set B) →
    universal-property-set-truncation l B f →
    is-set-truncation l B f
  is-set-truncation-universal-property l B f up-f C =
    is-equiv-is-contr-map
      ( λ g → is-contr-equiv
        ( Σ (type-hom-Set B C) (λ h → (h ∘ f) ~ g))
        ( equiv-tot (λ h → equiv-funext))
        ( up-f C g))
```

### A map into a set satisfies the universal property if it is a set truncation

```agda
abstract
  universal-property-is-set-truncation :
    (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU-Set l2)
    (f : A → type-Set B) →
    is-set-truncation l B f → universal-property-set-truncation l B f
  universal-property-is-set-truncation l B f is-settr-f C g =
    is-contr-equiv'
      ( Σ (type-hom-Set B C) (λ h → (h ∘ f) ＝ g))
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (is-settr-f C) g)

map-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  ({l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) → type-hom-Set B C
map-is-set-truncation B f is-settr-f C g =
  pr1
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))

triangle-is-set-truncation :
  {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  (is-settr-f : {l : Level} → is-set-truncation l B f) →
  (C : UU-Set l3) (g : A → type-Set C) →
  ((map-is-set-truncation B f is-settr-f C g) ∘ f) ~ g
triangle-is-set-truncation B f is-settr-f C g =
  pr2
    ( center
      ( universal-property-is-set-truncation _ B f is-settr-f C g))
```

### The identity function on any set is a set truncation

```agda
abstract
  is-set-truncation-id :
    {l1 : Level} {A : UU l1} (H : is-set A) →
    {l2 : Level} → is-set-truncation l2 (pair A H) id
  is-set-truncation-id H B =
    is-equiv-precomp-is-equiv id is-equiv-id (type-Set B)
```

### Any equivalence into a set is a set truncation

```agda
abstract
  is-set-truncation-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (e : A ≃ type-Set B) →
    {l : Level} → is-set-truncation l2 B (map-equiv e)
  is-set-truncation-equiv B e C =
    is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Set C)
```

### Any set truncation satisfies the dependent universal property of the set truncation

```agda
abstract
  dependent-universal-property-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    ({l : Level} → is-set-truncation l B f) →
    dependent-universal-property-set-truncation l3 B f
  dependent-universal-property-is-set-truncation {A = A} B f H X =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (h : A → type-Set B) → (a : A) → type-Set (X (h a)))
      ( λ (g : type-Set B → type-Set B) → g ∘ f)
      ( λ g (s : (b : type-Set B) → type-Set (X (g b))) (a : A) → s (f a))
      ( H B)
      ( is-equiv-equiv
        ( inv-distributive-Π-Σ)
        ( inv-distributive-Π-Σ)
        ( ind-Σ (λ g s → refl))
        ( H (Σ-Set B X)))
      ( id)
```

### Any map satisfying the dependent universal property of set truncations is a set truncation

```agda
abstract
  is-set-truncation-dependent-universal-property :
    {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    ({l : Level} → dependent-universal-property-set-truncation l B f) →
    is-set-truncation l3 B f
  is-set-truncation-dependent-universal-property B f H X =
    H (λ b → X)
```

### Any set quotient of the mere equality equivalence relation is a set truncation

```agda
abstract
  is-set-truncation-is-set-quotient :
    {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    ( {l : Level} →
      is-set-quotient l (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)) →
    is-set-truncation l3 B f
  is-set-truncation-is-set-quotient {A = A} B f H X =
    is-equiv-comp
      ( precomp-Set f X)
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( refl-htpy)
      ( H X)
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
            ( reflects-mere-eq X h)))
```

### Any set truncation is a quotient of the mere equality equivalence relation

```agda
abstract
  is-set-quotient-is-set-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    ( {l : Level} → is-set-truncation l B f) →
    is-set-quotient l3 (mere-eq-Eq-Rel A) B (reflecting-map-mere-eq B f)
  is-set-quotient-is-set-truncation {A = A} B f H X =
    is-equiv-right-factor
      ( precomp-Set f X)
      ( pr1)
      ( precomp-Set-Quotient
        ( mere-eq-Eq-Rel A)
        ( B)
        ( reflecting-map-mere-eq B f)
        ( X))
      ( refl-htpy)
      ( is-equiv-pr1-is-contr
        ( λ h →
          is-proof-irrelevant-is-prop
            ( is-prop-reflects-Eq-Rel (mere-eq-Eq-Rel A) X h)
            ( reflects-mere-eq X h)))
      ( H X)
```
