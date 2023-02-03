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
open import foundation.sets
open import foundation.unit-type
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.equivalence-relations

open import univalent-combinatorics.standard-finite-types
```

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (A/R : Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  {B : UU l4} (S : Eq-Rel l5 B)
  (B/S : Set l6) (g : reflecting-map-Eq-Rel S (type-Set B/S))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    is-contr
      ( Σ ( type-Set A/R → type-Set B/S)
          ( coherence-square h
            ( map-reflecting-map-Eq-Rel R f)
            ( map-reflecting-map-Eq-Rel S g)))
  unique-map-is-set-quotient Uf Ug h Hh =
    universal-property-set-quotient-is-set-quotient R A/R f Uf B/S
      ( pair
        ( map-reflecting-map-Eq-Rel S g ∘ h)
        ( λ r → reflects-map-reflecting-map-Eq-Rel S g (Hh r)))

  map-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A → B) → ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    type-Set A/R → type-Set B/S
  map-is-set-quotient Uf Ug h H =
    pr1 (center (unique-map-is-set-quotient Uf Ug h H))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    (Ug : {l : Level} → is-set-quotient l S B/S g) →
    (h : A → B)
    (H : {x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (h x) (h y)) →
    coherence-square h
      ( map-reflecting-map-Eq-Rel R f)
      ( map-reflecting-map-Eq-Rel S g)
      ( map-is-set-quotient Uf Ug h H)
  coherence-square-map-is-set-quotient Uf Ug h H =
    pr2 (center (unique-map-is-set-quotient Uf Ug h H))
```

## Properties

### Functoriality of set quotients preserves equivalences

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (A/R : Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  {B : UU l4} (S : Eq-Rel l5 B)
  (B/S : Set l6) (g : reflecting-map-Eq-Rel S (type-Set B/S))
  where

  unique-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A ≃ B) →
    ( {x y : A} → sim-Eq-Rel R x y ↔
      sim-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    is-contr
      ( Σ ( type-Set A/R ≃ type-Set B/S)
          ( λ h' →
            coherence-square
              ( map-equiv h)
              ( map-reflecting-map-Eq-Rel R f)
              ( map-reflecting-map-Eq-Rel S g)
              ( map-equiv h')))
  pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))) =
    map-is-set-quotient R A/R f S B/S g Uf Ug (map-equiv h) (pr1 Hh)
  pr2 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))) =
    is-equiv-has-inverse
      ( inv-h')
      ( λ x →
        ap
          ( λ c → pr1 c x)
          { x =
            pair
              ( ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)))) ∘
                ( inv-h'))
              ( tr
                ( λ e →
                  coherence-square
                    ( map-equiv e)
                    ( map-reflecting-map-Eq-Rel S g)
                    ( map-reflecting-map-Eq-Rel S g)
                    ( ( pr1
                        ( pr1
                          ( pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)))) ∘
                      ( inv-h')))
                ( right-inverse-law-equiv h)
                ( coherence-square-comp-horizontal
                  ( map-inv-equiv h)
                  ( map-equiv h)
                  ( map-reflecting-map-Eq-Rel S g)
                  ( map-reflecting-map-Eq-Rel R f)
                  ( map-reflecting-map-Eq-Rel S g)
                  ( inv-h')
                  ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))
                  ( coherence-square-map-is-set-quotient S B/S g R A/R f Ug Uf
                    ( map-inv-equiv h)
                    ( λ {x} {y} P →
                      pr2
                        ( Hh { x = map-inv-equiv h x} { y = map-inv-equiv h y})
                        ( tr
                          ( λ e → sim-Eq-Rel S (map-equiv e x) (map-equiv e y))
                          ( inv (right-inverse-law-equiv h))
                          ( P))))
                  ( coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug
                    ( map-equiv h)
                    ( pr1 Hh))))}
          { y = pair id refl-htpy}
          ( eq-is-contr
            ( unique-map-is-set-quotient S B/S g S B/S g Ug Ug id id)))
      ( λ x →
        ap
          ( λ c → pr1 c x)
          { x =
            pair
              ( ( inv-h') ∘
                ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)))))
              ( tr
                ( λ e →
                  coherence-square
                    ( map-equiv e)
                    ( map-reflecting-map-Eq-Rel R f)
                    ( map-reflecting-map-Eq-Rel R f)
                    ( ( inv-h') ∘
                      ( pr1
                        ( pr1
                          ( pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))))
                ( left-inverse-law-equiv h)
                ( coherence-square-comp-horizontal
                  ( map-equiv h)
                  ( map-inv-equiv h)
                  ( map-reflecting-map-Eq-Rel R f)
                  ( map-reflecting-map-Eq-Rel S g)
                  ( map-reflecting-map-Eq-Rel R f)
                  ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))
                  ( inv-h')
                  ( coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug
                    ( map-equiv h)
                    ( pr1 Hh))
                  ( coherence-square-map-is-set-quotient S B/S g R A/R f Ug Uf
                    ( map-inv-equiv h)
                    ( λ {x} {y} P →
                      pr2
                        ( Hh { x = map-inv-equiv h x} { y = map-inv-equiv h y})
                        ( tr
                          ( λ e → sim-Eq-Rel S (map-equiv e x) (map-equiv e y))
                          ( inv (right-inverse-law-equiv h))
                          ( P))))))}
          { y = pair id refl-htpy}
          ( eq-is-contr
            ( unique-map-is-set-quotient R A/R f R A/R f Uf Uf id id)))
    where
    inv-h' : type-Set B/S → type-Set A/R
    inv-h' =
      map-is-set-quotient S B/S g R A/R f Ug Uf
        ( map-inv-equiv h)
        ( λ {x} {y} P →
          pr2
            ( Hh { x = map-inv-equiv h x} { y = map-inv-equiv h y})
            ( tr
              ( λ e → sim-Eq-Rel S (map-equiv e x) (map-equiv e y))
              ( inv (right-inverse-law-equiv h))
              ( P)))
  pr2 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)) =
    coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug
      ( map-equiv h)
      ( pr1 Hh)
  pr2 (unique-equiv-is-set-quotient Uf Ug h Hh) (pair e CS) =
    eq-pair-Σ
      ( eq-pair-Σ
        ( ap pr1
          { x =
            pair
              ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))
              ( pr2 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)))}
          { y =
            pair
              ( pr1 e)
              ( CS)}
          ( eq-is-contr
            ( unique-map-is-set-quotient R A/R f S B/S g Uf Ug
              ( map-equiv h)
              ( pr1 Hh))))
        ( eq-is-prop (is-property-is-equiv (pr1 e))))
      ( eq-is-prop
        ( is-prop-Π
          ( λ x →
            is-set-type-Set B/S
              ( (map-equiv e ∘ map-reflecting-map-Eq-Rel R f) x)
              ( (map-reflecting-map-Eq-Rel S g ∘ map-equiv h) x))))

  equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A ≃ B) →
    ({x y : A} →
      sim-Eq-Rel R x y ↔ sim-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    type-Set A/R ≃ type-Set B/S
  equiv-is-set-quotient Uf Ug h H =
    pr1 (center (unique-equiv-is-set-quotient Uf Ug h H))

  coherence-square-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    (Ug : {l : Level} → is-set-quotient l S B/S g) →
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
  (A/R : Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  where

  id-map-is-set-quotient : 
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    map-is-set-quotient R A/R f R A/R f Uf Uf id id ~ id
  id-map-is-set-quotient Uf x =
    ap
      ( λ c → pr1 c x)
      { x =
        center
          (unique-map-is-set-quotient R A/R f R A/R f Uf Uf id id)}
      { y = pair id refl-htpy}
      ( eq-is-contr
        (unique-map-is-set-quotient R A/R f R A/R f Uf Uf id id))

  id-equiv-is-set-quotient : 
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    htpy-equiv
      ( equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv (pair id id))
      ( id-equiv)
  id-equiv-is-set-quotient Uf x =
    ap
      ( λ c → map-equiv (pr1 c) x)
      { x =
        center
          ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv
            ( pair id id))}
      { y = pair id-equiv refl-htpy}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv
          ( pair id id)))
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (A/R : Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  (Uf : {l : Level} → is-set-quotient l R A/R f)
  (eA : type-Set A/R ≃ Fin 2) (h : A → A)
  (H : {x y : A} →
    sim-Eq-Rel R x y ↔ sim-Eq-Rel R (h x) (h y))
  (h' : type-Set A/R → type-Set A/R)
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
              ( is-effective-is-set-quotient R A/R
                ( map-reflecting-map-Eq-Rel R f)
                ( reflects-map-reflecting-map-Eq-Rel R f)
                ( Uf)
                ( x)
                ( y))
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
                  ( is-effective-is-set-quotient R A/R
                    ( map-reflecting-map-Eq-Rel R f)
                    ( reflects-map-reflecting-map-Eq-Rel R f)
                    ( Uf)
                    ( h x)
                    ( h y))
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
                  ( is-effective-is-set-quotient R A/R
                    ( map-reflecting-map-Eq-Rel R f)
                    ( reflects-map-reflecting-map-Eq-Rel R f)
                    ( Uf)
                    ( h x)
                    ( h y))
                  ( inv P ∙ is-injective-map-equiv eA (p ∙ inv r)))))) ∙
            ( q))))
  cases-coherence-square-eq-one-value-emb-is-set-quotient H' y
    ( inr star) (inr star) k'' p q r =
    ( is-injective-map-equiv eA (q ∙ inv p)) ∙
      ( P ∙
        reflects-map-reflecting-map-Eq-Rel R f
          ( pr1 H
            ( map-equiv
              ( is-effective-is-set-quotient R A/R
                ( map-reflecting-map-Eq-Rel R f)
                ( reflects-map-reflecting-map-Eq-Rel R f)
                ( Uf)
                ( x)
                ( y))
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
    pair h' Q ＝ equiv-is-set-quotient R A/R f R A/R f Uf Uf (pair h P) H
  eq-equiv-eq-one-value-equiv-is-set-quotient P Q =
    ap pr1
      { x =
        pair
          ( pair h' Q)
          ( coherence-square-eq-one-value-emb-is-set-quotient
            ( is-emb-is-equiv Q))}
      { y =
        center
          ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf (pair h P) H)}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf (pair h P) H))
```
