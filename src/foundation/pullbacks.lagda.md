# Pullbacks

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.pullbacks where

open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import
  foundation.distributivity-of-dependent-functions-over-dependent-pairs using
  ( map-distributive-Π-Σ; mapping-into-Σ; is-equiv-mapping-into-Σ;
    is-equiv-map-distributive-Π-Σ)
open import foundation.equivalences using
  ( is-equiv-comp; _∘e_; is-equiv; map-inv-is-equiv; _≃_; id-equiv;
    map-inv-equiv)
open import foundation.functions using (_∘_)
open import foundation.homotopies using (_~_; refl-htpy; right-unit-htpy)
open import foundation.identity-types using
  ( Id; refl; ap; _∙_; inv; right-unit; equiv-concat'; equiv-inv)
open import foundation.structure-identity-principle using (extensionality-Σ)
open import foundation.universal-property-pullbacks using
  ( cone; universal-property-pullback; cone-map; htpy-cone;
    is-equiv-up-pullback-up-pullback; up-pullback-up-pullback-is-equiv)
open import foundation.universe-levels using (Level; UU; _⊔_)

open import foundation-core.functoriality-dependent-pair-types using
  ( tot; is-equiv-tot-is-fiberwise-equiv; equiv-tot)
```

## Idea

We construct canonical pullbacks of cospans

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  canonical-pullback : UU ((l1 ⊔ l2) ⊔ l3)
  canonical-pullback = Σ A (λ x → Σ B (λ y → Id (f x) (g y)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {f : A → X} {g : B → X}
  where
   
  π₁ : canonical-pullback f g → A
  π₁ = pr1

  π₂ : canonical-pullback f g → B
  π₂ t = pr1 (pr2 t)

  π₃ : (f ∘ π₁) ~ (g ∘ π₂)
  π₃ t = pr2 (pr2 t)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where
  
  cone-canonical-pullback : cone f g (canonical-pullback f g)
  pr1 cone-canonical-pullback = π₁
  pr1 (pr2 cone-canonical-pullback) = π₂
  pr2 (pr2 cone-canonical-pullback) = π₃
```

## Properties

### The canonical pullback satisfies the universal property of pullbacks

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → X) (g : B → X)
  where

  abstract
    universal-property-pullback-canonical-pullback : 
      {l : Level} →
      universal-property-pullback l f g (cone-canonical-pullback f g)
    universal-property-pullback-canonical-pullback C =
      is-equiv-comp
        ( cone-map f g (cone-canonical-pullback f g))
        ( tot (λ p → map-distributive-Π-Σ))
        ( mapping-into-Σ)
        ( refl-htpy)
        ( is-equiv-mapping-into-Σ)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ p → is-equiv-map-distributive-Π-Σ))

  {- We characterize the identity type of the canonical pullback. -}
  
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

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) 
  where

  {- The gap map of a square is the map fron the vertex of the cone into the
     canonical pullback. -}

  gap : cone f g C → C → canonical-pullback f g
  pr1 (gap (pair p (pair q H)) z) = p z
  pr1 (pr2 (gap (pair p (pair q H)) z)) = q z
  pr2 (pr2 (gap (pair p (pair q H)) z)) = H z

  {- The proposition is-pullback is the assertion that the gap map is an 
     equivalence. Note that this proposition is small, whereas the universal 
     property is a large proposition. Of course, we will show below that the
     proposition is-pullback is equivalent to the universal property of
     pullbacks. -}

  is-pullback : cone f g C → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-pullback c = is-equiv (gap c)

  {- A cone is equal to the value of cone-map at its own gap map. -}

  htpy-cone-up-pullback-canonical-pullback :
    (c : cone f g C) →
    htpy-cone f g (cone-map f g (cone-canonical-pullback f g) (gap c)) c
  pr1 (htpy-cone-up-pullback-canonical-pullback c) = refl-htpy
  pr1 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = refl-htpy
  pr2 (pr2 (htpy-cone-up-pullback-canonical-pullback c)) = right-unit-htpy

  {- We show that the universal property of the pullback implies that the gap
     map is an equivalence. -}

  abstract
    is-pullback-universal-property-pullback :
      (c : cone f g C) →
      ({l : Level} → universal-property-pullback l f g c) → is-pullback c
    is-pullback-universal-property-pullback c up =
      is-equiv-up-pullback-up-pullback
        ( cone-canonical-pullback f g)
        ( c)
        ( gap c)
        ( htpy-cone-up-pullback-canonical-pullback c)
        ( universal-property-pullback-canonical-pullback f g)
        ( up)

  {- We show that the universal property follows from the assumption that the
     the gap map is an equivalence. -}

  abstract
    universal-property-pullback-is-pullback :
      (c : cone f g C) → is-pullback c →
      {l : Level} → universal-property-pullback l f g c
    universal-property-pullback-is-pullback c is-pullback-c =
      up-pullback-up-pullback-is-equiv
        ( cone-canonical-pullback f g)
        ( c)
        ( gap c)
        ( htpy-cone-up-pullback-canonical-pullback c)
        ( is-pullback-c)
        ( universal-property-pullback-canonical-pullback f g)
```
