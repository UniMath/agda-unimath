---
title: Functoriality of set quotients
---

```agda
module foundation.functoriality-set-quotients where

open import foundation.commuting-squares
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations

```

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

### Maps preserving equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  map-Eq-Rel : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  map-Eq-Rel =
    Σ (A → B) ( λ f → {x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (f x) (f y))

  map-map-Eq-Rel : map-Eq-Rel → A → B
  map-map-Eq-Rel = pr1

  preserves-sim-map-Eq-Rel :
    (f : map-Eq-Rel) {x y : A} → sim-Eq-Rel R x y →
    sim-Eq-Rel S (map-map-Eq-Rel f x) (map-map-Eq-Rel f y)
  preserves-sim-map-Eq-Rel = pr2

id-map-Eq-Rel :
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A) → map-Eq-Rel R R
pr1 (id-map-Eq-Rel R) = id
pr2 (id-map-Eq-Rel R) = id
```

### Maps between types satisfying the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Rel S (type-Set QS))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : map-Eq-Rel R S) →
    is-contr
      ( Σ ( type-Set QR → type-Set QS)
          ( coherence-square
            ( map-map-Eq-Rel R S h)
            ( map-reflecting-map-Eq-Rel R f)
            ( map-reflecting-map-Eq-Rel S g)))
  unique-map-is-set-quotient Uf Ug h =
    universal-property-set-quotient-is-set-quotient R QR f Uf QS
      ( pair
        ( map-reflecting-map-Eq-Rel S g ∘ map-map-Eq-Rel R S h)
        ( λ r →
          reflects-map-reflecting-map-Eq-Rel S g
            (preserves-sim-map-Eq-Rel R S h r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : map-Eq-Rel R S) →
    type-Set QR → type-Set QS
  map-is-set-quotient Uf Ug h =
    pr1 (center (unique-map-is-set-quotient Uf Ug h))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : map-Eq-Rel R S) →
    coherence-square
      ( map-map-Eq-Rel R S h)
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-is-set-quotient Uf Ug h)
  coherence-square-map-is-set-quotient Uf Ug h =
    pr2 (center (unique-map-is-set-quotient Uf Ug h))
```

### Functoriality of the set quotient

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  unique-map-set-quotient :
    (h : map-Eq-Rel R S) →
    is-contr
      ( Σ ( set-quotient R → set-quotient S)
          ( coherence-square
            ( map-map-Eq-Rel R S h)
            ( quotient-map R)
            ( quotient-map S)))
  unique-map-set-quotient =
    unique-map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)

  map-set-quotient :
    (h : map-Eq-Rel R S) → set-quotient R → set-quotient S
  map-set-quotient =
    map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)

  coherence-square-map-set-quotient :
    (h : map-Eq-Rel R S) →
    coherence-square
      ( map-map-Eq-Rel R S h)
      ( quotient-map R)
      ( quotient-map S)
      ( map-set-quotient h)
  coherence-square-map-set-quotient =
    coherence-square-map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)
```

## Properties

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (g : reflecting-map-Eq-Rel S (type-Set QS))
  where

  unique-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : A ≃ B) →
    ( {x y : A} →
      sim-Eq-Rel R x y ↔ sim-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    is-contr
      ( Σ ( type-Set QR ≃ type-Set QS)
          ( λ h' →
            coherence-square
              ( map-equiv h)
              ( map-reflecting-map-Eq-Rel R f)
              ( map-reflecting-map-Eq-Rel S g)
              ( map-equiv h')))
  unique-equiv-is-set-quotient Uf Ug h H =
    uniqueness-set-quotient R QR f Uf QS
      ( comp-reflecting-map-Eq-Rel R S g (map-equiv h) (λ {x} {y} r → pr1 H r))
      ( is-set-quotient-is-surjective-and-effective R QS
        ( comp-reflecting-map-Eq-Rel R S g
          ( map-equiv h)
          ( λ {x} {y} r → pr1 H r))
        ( ( is-surjective-comp
            ( is-surjective-is-set-quotient S QS g Ug)
            ( is-surjective-is-equiv (is-equiv-map-equiv h))) ,
          ( λ x y →
            ( inv-equiv
              ( equiv-iff'
                ( prop-Eq-Rel R x y)
                ( prop-Eq-Rel S (map-equiv h x) (map-equiv h y))
                ( H {x} {y}))) ∘e
            ( is-effective-is-set-quotient S QS g Ug
              ( map-equiv h x)
              ( map-equiv h y)))))

  equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : A ≃ B) →
    ({x y : A} →
      sim-Eq-Rel R x y ↔ sim-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    type-Set QR ≃ type-Set QS
  equiv-is-set-quotient Uf Ug h H =
    pr1 (center (unique-equiv-is-set-quotient Uf Ug h H))

  coherence-square-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : A ≃ B) →
    (H : {x y : A} →
      sim-Eq-Rel R x y ↔ sim-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    coherence-square (map-equiv h)
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-equiv (equiv-is-set-quotient Uf Ug h H))
  coherence-square-equiv-is-set-quotient Uf Ug h H =
    pr2 (center (unique-equiv-is-set-quotient Uf Ug h H))
```

### Functoriality of set quotients preserves identity maps

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  where

  id-map-is-set-quotient : 
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    map-is-set-quotient R QR f R QR f Uf Uf (id-map-Eq-Rel R) ~ id
  id-map-is-set-quotient Uf x =
    ap
      ( λ c → pr1 c x)
      { x =
        center
          (unique-map-is-set-quotient R QR f R QR f Uf Uf (id-map-Eq-Rel R))}
      { y = pair id refl-htpy}
      ( eq-is-contr
        ( unique-map-is-set-quotient R QR f R QR f Uf Uf (id-map-Eq-Rel R)))

  id-equiv-is-set-quotient : 
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    htpy-equiv
      ( equiv-is-set-quotient R QR f R QR f Uf Uf id-equiv (pair id id))
      ( id-equiv)
  id-equiv-is-set-quotient Uf x =
    ap
      ( λ c → map-equiv (pr1 c) x)
      { x =
        center
          ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf id-equiv
            ( pair id id))}
      { y = pair id-equiv refl-htpy}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf id-equiv
          ( pair id id)))
```
