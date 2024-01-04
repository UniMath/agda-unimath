# The dependent pullback property of pushouts

```agda
module synthetic-homotopy-theory.dependent-pullback-property-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospans
open import foundation.constant-type-families
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.precomposition-functions
open import foundation.pullbacks
open import foundation.transport-along-identifications
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.lifts-families-of-elements
open import orthogonal-factorization-systems.precomposition-lifts-families-of-elements

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pullback-property-pushouts
```

</details>

## Idea

The **dependent pullback property** of
[pushouts](synthetic-homotopy-theory.pushouts.md) asserts that the type of
sections of a type family over a pushout can be expressed as a
[pullback](foundation.pullbacks.md).

The fact that the dependent pullback property of pushouts is
[logically equivalent](foundation.logical-equivalences.md) to the
[dependent universal property](synthetic-homotopy-theory.dependent-universal-property-pushouts.md)
of pushouts is shown in
[`dependent-universal-property-pushouts`](synthetic-homotopy-theory.dependent-universal-property-pushouts.md).

## Definition

```agda
cone-dependent-pullback-property-pushout :
  {l1 l2 l3 l4 l5 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) (P : X → UU l5) →
  let i = pr1 c
      j = pr1 (pr2 c)
      H = pr2 (pr2 c)
  in
  cone
    ( λ (h : (a : A) → P (i a)) → λ (s : S) → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( (x : X) → P x)
pr1 (cone-dependent-pullback-property-pushout f g (i , j , H) P) h a =
  h (i a)
pr1 (pr2 (cone-dependent-pullback-property-pushout f g (i , j , H) P)) h b =
  h (j b)
pr2 (pr2 (cone-dependent-pullback-property-pushout f g (i , j , H) P)) h =
  eq-htpy (λ s → apd h (H s))

dependent-pullback-property-pushout :
  {l1 l2 l3 l4 : Level} (l : Level) {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
dependent-pullback-property-pushout l {S} {A} {B} f g {X} (i , j , H) =
  (P : X → UU l) →
  is-pullback
    ( λ (h : (a : A) → P (i a)) → λ s → tr P (H s) (h (f s)))
    ( λ (h : (b : B) → P (j b)) → λ s → h (g s))
    ( cone-dependent-pullback-property-pushout f g (i , j , H) P)
```

## Properties

### The dependent pullback property is logically equivalent to the pullback property

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  (f : S → A) (g : S → B) {X : UU l4} (c : cocone f g X)
  where

  pullback-property-dependent-pullback-property-pushout :
    ({l : Level} → dependent-pullback-property-pushout l f g c) →
    ({l : Level} → pullback-property-pushout l f g c)
  pullback-property-dependent-pullback-property-pushout dpp-c Y =
    is-pullback-htpy
      ( λ h →
        eq-htpy
          ( λ s →
            inv
              ( tr-constant-type-family
                ( coherence-square-cocone f g c s)
                ( h (f s)))))
      ( refl-htpy)
      ( cone-dependent-pullback-property-pushout f g c (λ _ → Y))
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ h →
          ( right-unit) ∙
          ( ap
            ( eq-htpy)
            ( eq-htpy
              ( λ s →
                left-transpose-eq-concat _ _ _
                  ( inv
                    ( apd-constant-type-family h
                      ( coherence-square-cocone f g c s))))) ∙
          ( eq-htpy-concat-htpy _ _))))
      ( dpp-c (λ _ → Y))

  cone-family-dependent-pullback-property :
    {l : Level} (P : X → UU l) →
    cone-family
      ( lift-family-of-elements P)
      ( precomp-lift-family-of-elements P f)
      ( precomp-lift-family-of-elements P g)
      ( cone-pullback-property-pushout f g c X)
      ( lift-family-of-elements P)
  pr1 (cone-family-dependent-pullback-property P γ) h =
    h ∘ horizontal-map-cocone f g c
  pr1 (pr2 (cone-family-dependent-pullback-property P γ)) h =
    h ∘ vertical-map-cocone f g c
  pr2 (pr2 (cone-family-dependent-pullback-property P γ)) =
    triangle-precompose-lift-family-of-elements-htpy P γ
      ( coherence-square-cocone f g c)

  is-pullback-cone-family-dependent-pullback-family :
    {l : Level} (P : X → UU l) →
    ({l : Level} → pullback-property-pushout l f g c) →
    (γ : X → X) →
    is-pullback
      ( ( tr
          ( lift-family-of-elements P)
          ( htpy-precomp (coherence-square-cocone f g c) X γ)) ∘
        ( precomp-lift-family-of-elements P f
          ( γ ∘ horizontal-map-cocone f g c)))
      ( precomp-lift-family-of-elements P g
        ( γ ∘ vertical-map-cocone f g c))
      ( cone-family-dependent-pullback-property P γ)
  is-pullback-cone-family-dependent-pullback-family P pp-c =
    is-pullback-family-is-pullback-tot
      ( lift-family-of-elements P)
      ( precomp-lift-family-of-elements P f)
      ( precomp-lift-family-of-elements P g)
      ( cone-pullback-property-pushout f g c X)
      ( cone-family-dependent-pullback-property P)
      ( pp-c X)
      ( is-pullback-top-is-pullback-bottom-cube-is-equiv
        ( precomp (horizontal-map-cocone f g c) (Σ X P))
        ( precomp (vertical-map-cocone f g c) (Σ X P))
        ( precomp f (Σ X P))
        ( precomp g (Σ X P))
        ( precomp-total-lift-family-of-elements P (horizontal-map-cocone f g c))
        ( precomp-total-lift-family-of-elements P (vertical-map-cocone f g c))
        ( precomp-total-lift-family-of-elements P f)
        ( precomp-total-lift-family-of-elements P g)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( map-inv-distributive-Π-Σ)
        ( htpy-precomp-total-lift-family-of-elements-htpy P
          ( coherence-square-cocone f g c))
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( refl-htpy)
        ( htpy-precomp (coherence-square-cocone f g c) (Σ X P))
        ( coherence-blabla P (coherence-square-cocone f g c))
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( pp-c (Σ X P)))

  dependent-pullback-property-pullback-property-pushout :
    ({l : Level} → pullback-property-pushout l f g c) →
    ({l : Level} → dependent-pullback-property-pushout l f g c)
  dependent-pullback-property-pullback-property-pushout pp-c P =
    is-pullback-htpy'
      ( ( tr-lift-family-of-elements P id (coherence-square-cocone f g c)) ·r
        ( precomp-lift-family-of-elements P f (horizontal-map-cocone f g c)))
      ( refl-htpy)
      ( cone-family-dependent-pullback-property P id)
      { c' = cone-dependent-pullback-property-pushout f g c P}
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( ( right-unit-htpy) ∙h
          ( coherence-triangle-precompose-lift-family-of-elements-htpy P id
            ( coherence-square-cocone f g c))))
      ( is-pullback-cone-family-dependent-pullback-family P pp-c id)
```
