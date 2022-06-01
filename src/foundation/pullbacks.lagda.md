# Pullbacks

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.pullbacks where

open import foundation-core.pullbacks public

open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import
  foundation.type-theoretic-principle-of-choice using
  ( map-distributive-Π-Σ; mapping-into-Σ; is-equiv-mapping-into-Σ;
    is-equiv-map-distributive-Π-Σ)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_; refl-htpy; right-unit-htpy)
open import foundation.identity-types using
  ( Id; refl; ap; _∙_; inv; right-unit; equiv-concat'; equiv-inv)
open import foundation.structure-identity-principle using (extensionality-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import foundation-core.cones-pullbacks
open import foundation-core.equivalences using
  ( is-equiv-comp; _∘e_; is-equiv; map-inv-is-equiv; _≃_; id-equiv;
    map-inv-equiv)
open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv; equiv-tot)
open import foundation-core.universal-property-pullbacks using
  ( universal-property-pullback;
    is-equiv-up-pullback-up-pullback; up-pullback-up-pullback-is-equiv)
```

## Idea

We construct canonical pullbacks of cospans

## Properties

### We characterize the identity type of the canonical pullback

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  Eq-canonical-pullback : (t t' : canonical-pullback f g) → UU (l1 ⊔ (l2 ⊔ l3))
  Eq-canonical-pullback (pair a bp) t' =
    let b = pr1 bp
        p = pr2 bp
        a' = pr1 t'
        b' = pr1 (pr2 t')
        p' = pr2 (pr2 t')
    in
    Σ (Id a a') (λ α → Σ (Id b b') (λ β → Id ((ap f α) ∙ p') (p ∙ (ap g β))))

  refl-Eq-canonical-pullback :
    (t : canonical-pullback f g) → Eq-canonical-pullback t t
  pr1 (refl-Eq-canonical-pullback (pair a (pair b p))) = refl
  pr1 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = refl
  pr2 (pr2 (refl-Eq-canonical-pullback (pair a (pair b p)))) = inv right-unit

  Eq-eq-canonical-pullback :
    (s t : canonical-pullback f g) → Id s t → Eq-canonical-pullback s t
  Eq-eq-canonical-pullback s .s refl = refl-Eq-canonical-pullback s

  extensionality-canonical-pullback :
    (t t' : canonical-pullback f g) → Id t t' ≃ Eq-canonical-pullback t t'
  extensionality-canonical-pullback (pair a (pair b p)) =
    extensionality-Σ
      ( λ {a'} bp' α →
        Σ (Id b (pr1 bp')) (λ β → Id (ap f α ∙ pr2 bp') (p ∙ ap g β)))
      ( refl)
      ( pair refl (inv right-unit))
      ( λ x → id-equiv)
      ( extensionality-Σ
        ( λ {b'} p' β → Id p' (p ∙ ap g β))
        ( refl)
        ( inv right-unit)
        ( λ y → id-equiv)
        ( λ p' → equiv-concat' p' (inv right-unit) ∘e equiv-inv p p'))

  map-extensionality-canonical-pullback :
    { s t : canonical-pullback f g} →
    ( α : Id (pr1 s) (pr1 t)) (β : Id (pr1 (pr2 s)) (pr1 (pr2 t))) →
    ( Id ((ap f α) ∙ (pr2 (pr2 t))) ((pr2 (pr2 s)) ∙ (ap g β))) → Id s t
  map-extensionality-canonical-pullback {s} {t} α β γ =
    map-inv-equiv
      ( extensionality-canonical-pullback s t)
      ( triple α β γ)
```
