---
title: The uniqueness of set quotients
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.uniqueness-set-quotients where

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality using (htpy-eq)
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations
```

## Idea

The universal property of set quotients implies that set quotients are uniquely unique.

## Properties

### Uniqueness of set quotients

```agda
precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : Set l4) (g : type-hom-Set B C)
  (D : Set l5) (h : type-hom-Set C D) →
  ( precomp-Set-Quotient R B f D (h ∘ g)) ＝
  ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-Eq-Rel R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : Set l3) (f : reflecting-map-Eq-Rel R (type-Set B))
  (C : Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  {h : type-Set B → type-Set C}
  (H : (h ∘ map-reflecting-map-Eq-Rel R f) ~ map-reflecting-map-Eq-Rel R g)
  where

  abstract
    is-equiv-is-set-quotient-is-set-quotient :
      ({l : Level} → is-set-quotient l R B f) →
      ({l : Level} → is-set-quotient l R C g) →
      is-equiv h
    is-equiv-is-set-quotient-is-set-quotient Uf Ug =
      is-equiv-has-inverse 
        ( pr1 (center K))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Ug C)
            { h ∘ k}
            { id}
            ( ( precomp-comp-Set-Quotient R C g B k C h) ∙
              ( ( ap (λ t → precomp-Set-Quotient R B t C h) α) ∙
                ( ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H) ∙
                  ( inv (precomp-id-Set-Quotient R C g)))))))
        ( htpy-eq
          ( is-injective-is-equiv
            ( Uf B)
            { k ∘ h}
            { id}
            ( ( precomp-comp-Set-Quotient R B f C h B k) ∙
              ( ( ap
                  ( λ t → precomp-Set-Quotient R C t B k)
                  ( eq-htpy-reflecting-map-Eq-Rel R C
                    ( precomp-Set-Quotient R B f C h) g H)) ∙
                ( ( α) ∙
                  ( inv (precomp-id-Set-Quotient R B f)))))))
      where
      K : is-contr
            ( Σ ( type-hom-Set C B)
                ( λ h →
                  ( h ∘ map-reflecting-map-Eq-Rel R g) ~
                  ( map-reflecting-map-Eq-Rel R f)))
      K = universal-property-set-quotient-is-set-quotient R C g Ug B f
      k : type-Set C → type-Set B
      k = pr1 (center K)
      α : precomp-Set-Quotient R C g B k ＝ f
      α = eq-htpy-reflecting-map-Eq-Rel R B
            ( precomp-Set-Quotient R C g B k)
            ( f)
            ( pr2 (center K))

  abstract
    is-set-quotient-is-set-quotient-is-equiv :
      is-equiv h → ({l : Level} → is-set-quotient l R B f) →
      {l : Level} → is-set-quotient l R C g
    is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
      is-equiv-comp-htpy
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( is-equiv-precomp-is-equiv h E (type-Set X))
        ( Uf X)

  abstract
    is-set-quotient-is-equiv-is-set-quotient :
      ({l : Level} → is-set-quotient l R C g) → is-equiv h →
      {l : Level} → is-set-quotient l R B f
    is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
      is-equiv-left-factor-htpy
        ( precomp-Set-Quotient R C g X)
        ( precomp-Set-Quotient R B f X)
        ( precomp h (type-Set X))
        ( λ k →
          eq-htpy-reflecting-map-Eq-Rel R X
            ( precomp-Set-Quotient R C g X k)
            ( precomp-Set-Quotient R B f X (k ∘ h))
            ( inv-htpy (k ·l H)))
        ( Ug X)
        ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  (B : Set l3) (f : reflecting-map-Eq-Rel R (type-Set B)) 
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : Set l4) (g : reflecting-map-Eq-Rel R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where

  abstract
    uniqueness-set-quotient :
      is-contr
        ( Σ ( type-Set B ≃ type-Set C)
            ( λ e →
              ( map-equiv e ∘ map-reflecting-map-Eq-Rel R f) ~
              ( map-reflecting-map-Eq-Rel R g)))
    uniqueness-set-quotient =
      is-contr-total-Eq-subtype
        ( universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-property-is-equiv)
        ( map-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( triangle-universal-property-set-quotient-is-set-quotient R B f Uf C g)
        ( is-equiv-is-set-quotient-is-set-quotient R B f C g
          ( triangle-universal-property-set-quotient-is-set-quotient
            R B f Uf C g)
          ( Uf)
          ( Ug))

  equiv-uniqueness-set-quotient : type-Set B ≃ type-Set C
  equiv-uniqueness-set-quotient =
    pr1 (center uniqueness-set-quotient)

  map-equiv-uniqueness-set-quotient : type-Set B → type-Set C
  map-equiv-uniqueness-set-quotient =  map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘ map-reflecting-map-Eq-Rel R f) ~
    ( map-reflecting-map-Eq-Rel R g)
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)
```
