# Functoriality of set quotients

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.functoriality-set-quotients where

open import foundation.commuting-squares using
  ( coherence-square; coherence-square-comp-horizontal)
open import foundation.contractible-types using
  ( is-contr; center; eq-is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; map-equiv; is-equiv-has-inverse; map-inv-equiv; right-inverse-law-equiv;
    left-inverse-law-equiv; is-property-is-equiv; htpy-equiv; id-equiv)
open import foundation.equivalence-relations using (Eq-Rel; type-Eq-Rel)
open import foundation.functions using (_∘_; id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; tr; ap; _∙_)
open import foundation.logical-equivalences using (_↔_)
open import foundation.propositions using (eq-is-prop; is-prop-Π)
open import foundation.reflecting-maps-equivalence-relations using
  ( reflecting-map-Eq-Rel; map-reflecting-map-Eq-Rel;
    reflects-map-reflecting-map-Eq-Rel)
open import foundation.sets using (UU-Set; type-Set; is-set-type-Set)
open import foundation.universal-property-set-quotients using
  ( is-set-quotient; universal-property-set-quotient-is-set-quotient)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Set quotients act functorially on types equipped with equivalence relations.

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (A/R : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  {B : UU l4} (S : Eq-Rel l5 B)
  (B/S : UU-Set l6) (g : reflecting-map-Eq-Rel S (type-Set B/S))
  where

  unique-map-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A → B) → ({x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
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
    (h : A → B) → ({x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
    type-Set A/R → type-Set B/S
  map-is-set-quotient Uf Ug h H =
    pr1 (center (unique-map-is-set-quotient Uf Ug h H))

  coherence-square-map-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    (Ug : {l : Level} → is-set-quotient l S B/S g) →
    (h : A → B)
    (H : {x y : A} → type-Eq-Rel R x y → type-Eq-Rel S (h x) (h y)) →
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
  (A/R : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
  {B : UU l4} (S : Eq-Rel l5 B)
  (B/S : UU-Set l6) (g : reflecting-map-Eq-Rel S (type-Set B/S))
  where

  unique-equiv-is-set-quotient :
    ({l : Level} → is-set-quotient l R A/R f) →
    ({l : Level} → is-set-quotient l S B/S g) →
    (h : A ≃ B) →
    ( {x y : A} → type-Eq-Rel R x y ↔
      type-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
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
              ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))) ∘ inv-h')
              ( tr
                ( λ e →
                  coherence-square
                    ( map-equiv e)
                    ( map-reflecting-map-Eq-Rel S g)
                    ( map-reflecting-map-Eq-Rel S g)
                    ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))) ∘ inv-h'))
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
                          ( λ e → type-Eq-Rel S (map-equiv e x) (map-equiv e y))
                          ( inv (right-inverse-law-equiv h))
                          ( P))))
                  ( coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug (map-equiv h) (pr1 Hh))))}
          { y = pair id refl-htpy}
          ( eq-is-contr
            ( unique-map-is-set-quotient S B/S g S B/S g Ug Ug id id)))
      ( λ x →
        ap
          ( λ c → pr1 c x)
          { x =
            pair
              (inv-h' ∘ pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))
              ( tr
                ( λ e →
                  coherence-square
                    ( map-equiv e)
                    ( map-reflecting-map-Eq-Rel R f)
                    ( map-reflecting-map-Eq-Rel R f)
                    ( inv-h' ∘ pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)))))
                ( left-inverse-law-equiv h)
                ( coherence-square-comp-horizontal
                  ( map-equiv h)
                  ( map-inv-equiv h)
                  ( map-reflecting-map-Eq-Rel R f)
                  ( map-reflecting-map-Eq-Rel S g)
                  ( map-reflecting-map-Eq-Rel R f)
                  ( pr1 (pr1 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh))))
                  ( inv-h')
                  ( coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug (map-equiv h) (pr1 Hh))
                  ( coherence-square-map-is-set-quotient S B/S g R A/R f Ug Uf
                    ( map-inv-equiv h)
                    ( λ {x} {y} P →
                      pr2
                        ( Hh { x = map-inv-equiv h x} { y = map-inv-equiv h y})
                        ( tr
                          ( λ e → type-Eq-Rel S (map-equiv e x) (map-equiv e y))
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
              ( λ e → type-Eq-Rel S (map-equiv e x) (map-equiv e y))
              ( inv (right-inverse-law-equiv h))
              ( P)))
  pr2 (pr1 (unique-equiv-is-set-quotient Uf Ug h Hh)) =
    coherence-square-map-is-set-quotient R A/R f S B/S g Uf Ug (map-equiv h) (pr1 Hh)
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
            ( unique-map-is-set-quotient R A/R f S B/S g Uf Ug (map-equiv h) (pr1 Hh))))
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
      type-Eq-Rel R x y ↔ type-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
    type-Set A/R ≃ type-Set B/S
  equiv-is-set-quotient Uf Ug h H =
    pr1 (center (unique-equiv-is-set-quotient Uf Ug h H))

  coherence-square-equiv-is-set-quotient :
    (Uf : {l : Level} → is-set-quotient l R A/R f) →
    (Ug : {l : Level} → is-set-quotient l S B/S g) →
    (h : A ≃ B) →
    (H : {x y : A} →
      type-Eq-Rel R x y ↔ type-Eq-Rel S (map-equiv h x) (map-equiv h y)) →
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
  (A/R : UU-Set l3) (f : reflecting-map-Eq-Rel R (type-Set A/R))
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
    htpy-equiv (equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv (pair id id)) id-equiv
  id-equiv-is-set-quotient Uf x =
    ap
      ( λ c → map-equiv (pr1 c) x)
      { x =
        center
          ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv (pair id id))}
      { y = pair id-equiv refl-htpy}
      ( eq-is-contr
        ( unique-equiv-is-set-quotient R A/R f R A/R f Uf Uf id-equiv (pair id id)))
```
