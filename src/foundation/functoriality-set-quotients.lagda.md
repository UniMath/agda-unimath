---
title: Functoriality of set quotients
---

```agda
module foundation.functoriality-set-quotients where

open import foundation.commuting-squares
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
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

open import univalent-combinatorics.standard-finite-types
```

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

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
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    is-contr
      ( Σ ( type-Set QR → type-Set QS)
          ( coherence-square h
            ( map-reflecting-map-Eq-Rel R f)
            ( map-reflecting-map-Eq-Rel S g)))
  unique-map-is-set-quotient Uf Ug h Hh =
    universal-property-set-quotient-is-set-quotient R QR f Uf QS
      ( pair
        ( map-reflecting-map-Eq-Rel S g ∘ h)
        ( λ r → reflects-map-reflecting-map-Eq-Rel S g (Hh r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R QR f) →
    ({l : Level} → is-set-quotient l S QS g) →
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    type-Set QR → type-Set QS
  map-is-set-quotient Uf Ug h H =
    pr1 (center (unique-map-is-set-quotient Uf Ug h H))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R QR f) →
    (Ug : {l : Level} → is-set-quotient l S QS g) →
    (h : A → B)
    (H : {x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    coherence-square h
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-is-set-quotient Uf Ug h H)
  coherence-square-map-is-set-quotient Uf Ug h H =
    pr2 (center (unique-map-is-set-quotient Uf Ug h H))
```

### Functoriality of the set quotient

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  unique-map-set-quotient :
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    is-contr
      ( Σ ( set-quotient R → set-quotient S)
          ( coherence-square h (quotient-map R) (quotient-map S)))
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
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    set-quotient R → set-quotient S
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
    (h : A → B)
    (H : {x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    coherence-square h
      ( quotient-map R)
      ( quotient-map S)
      ( map-set-quotient h H)
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

### Binary functoriality of types that satisfy the universal property of set quotients

### Binary functoriality of set quotients

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
        ( comp-reflecting-map-Eq-Rel R S g (map-equiv h) (λ {x} {y} r → pr1 H r))
        ( ( is-surjective-comp
            ( is-surjective-is-set-quotient S QS g Ug)
            ( is-surjective-is-equiv (is-equiv-map-equiv h))) ,
          ( λ x y →
            ( inv-equiv
              ( equiv-iff'
                ( prop-Eq-Rel R x y)
                ( prop-Eq-Rel S (map-equiv h x) (map-equiv h y))
                ( H {x} {y}))) ∘e
            ( is-effective-is-set-quotient S QS g Ug (map-equiv h x) (map-equiv h y)))))

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
    map-is-set-quotient R QR f R QR f Uf Uf id id ~ id
  id-map-is-set-quotient Uf x =
    ap
      ( λ c → pr1 c x)
      { x =
        center
          (unique-map-is-set-quotient R QR f R QR f Uf Uf id id)}
      { y = pair id refl-htpy}
      ( eq-is-contr
        (unique-map-is-set-quotient R QR f R QR f Uf Uf id id))

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

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (f : reflecting-map-Eq-Rel R (type-Set QR))
  (Uf : {l : Level} → is-set-quotient l R QR f)
  (eA : type-Set QR ≃ Fin 2) (h : A → A)
  (H : {x y : A} →
    sim-Eq-Rel R x y ↔ sim-Eq-Rel R (h x) (h y))
  (h' : type-Set QR → type-Set QR)
  (x : A)
  (P : h' (map-reflecting-map-Eq-Rel R f x) ＝
       map-reflecting-map-Eq-Rel R f (h x))
  where

  cases-coherence-square-eq-one-value-emb-is-set-quotient : is-emb h' →
    (y : A) (k k' k'' : Fin 2) → 
    map-equiv eA (h' (map-reflecting-map-Eq-Rel R f x)) ＝ k →
    map-equiv eA (h' (map-reflecting-map-Eq-Rel R f y)) ＝ k' →
    map-equiv eA (map-reflecting-map-Eq-Rel R f (h y)) ＝ k'' →
    h' (map-reflecting-map-Eq-Rel R f y) ＝ map-reflecting-map-Eq-Rel R f (h y)
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inl (inr star)) (inl (inr star)) k'' p q r =
    ( is-injective-map-equiv eA (q ∙ inv p)) ∙
      ( P ∙
        reflects-map-reflecting-map-Eq-Rel R f
          ( pr1 H
            ( map-equiv
              ( is-effective-is-set-quotient R QR f Uf x y)
              ( map-inv-is-equiv
                ( H' ( map-reflecting-map-Eq-Rel R f x)
                     ( map-reflecting-map-Eq-Rel R f y))
                ( is-injective-map-equiv eA (p ∙ inv q))))))
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inl (inr star)) (inr star) (inl (inr star)) p q r =
    ex-falso
      ( neq-inl-inr
        ( inv p ∙
          ( ( ap
            ( map-equiv eA ∘ h')
            ( reflects-map-reflecting-map-Eq-Rel R f
              ( pr2 H
                (map-equiv
                  ( is-effective-is-set-quotient R QR f Uf (h x) (h y))
                  ( inv P ∙ is-injective-map-equiv eA (p ∙ inv r)))))) ∙
            ( q))))
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inl (inr star)) (inr star) (inr star) p q r =
    is-injective-map-equiv eA (q ∙ inv r)
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inr star) (inl (inr star)) (inl (inr star)) p q r = 
    is-injective-map-equiv eA (q ∙ inv r)
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inr star) (inl (inr star)) (inr star) p q r =
    ex-falso
      ( neq-inr-inl
        ( inv p ∙
          ( ( ap
            ( map-equiv eA ∘ h')
            ( reflects-map-reflecting-map-Eq-Rel R f
              ( pr2 H
                (map-equiv
                  ( is-effective-is-set-quotient R QR f Uf (h x) (h y))
                  ( inv P ∙ is-injective-map-equiv eA (p ∙ inv r)))))) ∙
            ( q))))
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inr star) (inr star) k'' p q r =
    ( is-injective-map-equiv eA (q ∙ inv p)) ∙
      ( P ∙
        reflects-map-reflecting-map-Eq-Rel R f
          ( pr1 H
            ( map-equiv
              ( is-effective-is-set-quotient R QR f Uf x y)
              ( map-inv-is-equiv
                ( H' ( map-reflecting-map-Eq-Rel R f x)
                     ( map-reflecting-map-Eq-Rel R f y))
                ( is-injective-map-equiv eA (p ∙ inv q))))))

  coherence-square-eq-one-value-emb-is-set-quotient : is-emb h' →
    coherence-square
      ( h)
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel R f)
      ( h')
  coherence-square-eq-one-value-emb-is-set-quotient H' y =
    cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
      ( map-equiv eA (h' (map-reflecting-map-Eq-Rel R f x)))
      ( map-equiv eA (h' (map-reflecting-map-Eq-Rel R f y)))
      ( map-equiv eA (map-reflecting-map-Eq-Rel R f (h y)))
      ( refl)
      ( refl)
      ( refl)

  eq-equiv-eq-one-value-equiv-is-set-quotient :
    (P : is-equiv h) (Q : is-equiv h') →
    pair h' Q ＝ equiv-is-set-quotient R QR f R QR f Uf Uf (pair h P) H
  eq-equiv-eq-one-value-equiv-is-set-quotient P Q =
    ap pr1
      { x =
        pair
          ( pair h' Q)
          ( coherence-square-eq-one-value-emb-is-set-quotient
            ( is-emb-is-equiv Q))}
      { y =
        center
          ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf (pair h P) H)}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R QR f R QR f Uf Uf (pair h P) H))
```
