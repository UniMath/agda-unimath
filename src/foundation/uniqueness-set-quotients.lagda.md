# The uniqueness of set quotients

```agda
module foundation.uniqueness-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.reflecting-maps-equivalence-relations
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universal-property-equivalences
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.precomposition-functions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The universal property of set quotients implies that set quotients are uniquely
unique.

## Properties

### Uniqueness of set quotients

```agda
precomp-comp-Set-Quotient :
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : hom-Set B C)
  (D : Set l5) (h : hom-Set C D) →
  ( precomp-Set-Quotient R B f D (h ∘ g)) ＝
  ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
precomp-comp-Set-Quotient R B f C g D h =
  eq-htpy-reflecting-map-equivalence-relation R D
    ( precomp-Set-Quotient R B f D (h ∘ g))
    ( precomp-Set-Quotient R C (precomp-Set-Quotient R B f C g) D h)
    ( refl-htpy)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  {h : type-Set B → type-Set C}
  (H :
    (h ∘ map-reflecting-map-equivalence-relation R f) ~
    map-reflecting-map-equivalence-relation R g)
  where

  map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ({l : Level} → is-set-quotient l R B f) →
    ({l : Level} → is-set-quotient l R C g) →
    type-Set C → type-Set B
  map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    map-universal-property-set-quotient-is-set-quotient R C g Ug B f

  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : {l : Level} → is-set-quotient l R B f) →
    ( Ug : {l : Level} → is-set-quotient l R C g) →
    ( h ∘ map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug) ~ id
  is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    htpy-eq
      ( is-injective-is-equiv
      ( Ug C)
      { h ∘ map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug}
      { id}
      ( ( precomp-comp-Set-Quotient R C g B
          ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
          ( C)
          ( h)) ∙
        ( ( ap
            ( λ t → precomp-Set-Quotient R B t C h)
            ( eq-htpy-reflecting-map-equivalence-relation R B
              ( precomp-Set-Quotient R C g B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
              ( f)
              ( triangle-universal-property-set-quotient-is-set-quotient
                R C g Ug B f))) ∙
          ( ( eq-htpy-reflecting-map-equivalence-relation R C
              ( precomp-Set-Quotient R B f C h) g H) ∙
            ( inv (precomp-id-Set-Quotient R C g))))))

  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient :
    ( Uf : {l : Level} → is-set-quotient l R B f) →
    ( Ug : {l : Level} → is-set-quotient l R C g) →
    ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug ∘ h) ~ id
  is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    htpy-eq
      ( is-injective-is-equiv
      ( Uf B)
      { map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug ∘ h}
      { id}
      ( ( precomp-comp-Set-Quotient R B f C h B
          ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)) ∙
        ( ( ap
            ( λ t →
              precomp-Set-Quotient R C t B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
            ( eq-htpy-reflecting-map-equivalence-relation R C
              ( precomp-Set-Quotient R B f C h)
              ( g)
              ( H))) ∙
          ( ( eq-htpy-reflecting-map-equivalence-relation R B
              ( precomp-Set-Quotient R C g B
                ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug))
              ( f)
              ( triangle-universal-property-set-quotient-is-set-quotient
                R C g Ug B f)) ∙
            ( inv (precomp-id-Set-Quotient R B f))))))

  is-equiv-is-set-quotient-is-set-quotient :
    ({l : Level} → is-set-quotient l R B f) →
    ({l : Level} → is-set-quotient l R C g) →
    is-equiv h
  is-equiv-is-set-quotient-is-set-quotient Uf Ug =
    is-equiv-is-invertible
      ( map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
      ( is-section-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)
      ( is-retraction-map-inv-is-equiv-is-set-quotient-is-set-quotient Uf Ug)

  is-set-quotient-is-set-quotient-is-equiv :
    is-equiv h → ({l : Level} → is-set-quotient l R B f) →
    {l : Level} → is-set-quotient l R C g
  is-set-quotient-is-set-quotient-is-equiv E Uf {l} X =
    is-equiv-left-map-triangle
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-equivalence-relation R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( is-equiv-precomp-is-equiv h E (type-Set X))
      ( Uf X)

  is-set-quotient-is-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R C g) → is-equiv h →
    {l : Level} → is-set-quotient l R B f
  is-set-quotient-is-equiv-is-set-quotient Ug E {l} X =
    is-equiv-right-map-triangle
      ( precomp-Set-Quotient R C g X)
      ( precomp-Set-Quotient R B f X)
      ( precomp h (type-Set X))
      ( λ k →
        eq-htpy-reflecting-map-equivalence-relation R X
          ( precomp-Set-Quotient R C g X k)
          ( precomp-Set-Quotient R B f X (k ∘ h))
          ( inv-htpy (k ·l H)))
      ( Ug X)
      ( is-equiv-precomp-is-equiv h E (type-Set X))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  (B : Set l3) (f : reflecting-map-equivalence-relation R (type-Set B))
  (Uf : {l : Level} → is-set-quotient l R B f)
  (C : Set l4) (g : reflecting-map-equivalence-relation R (type-Set C))
  (Ug : {l : Level} → is-set-quotient l R C g)
  where

  uniqueness-set-quotient :
    is-contr
      ( Σ ( type-Set B ≃ type-Set C)
          ( λ e →
            ( map-equiv e ∘ map-reflecting-map-equivalence-relation R f) ~
            ( map-reflecting-map-equivalence-relation R g)))
  uniqueness-set-quotient =
    is-torsorial-Eq-subtype
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
  map-equiv-uniqueness-set-quotient = map-equiv equiv-uniqueness-set-quotient

  triangle-uniqueness-set-quotient :
    ( map-equiv-uniqueness-set-quotient ∘
      map-reflecting-map-equivalence-relation R f) ~
    ( map-reflecting-map-equivalence-relation R g)
  triangle-uniqueness-set-quotient =
    pr2 (center uniqueness-set-quotient)
```
