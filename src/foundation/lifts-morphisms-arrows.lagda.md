# Lifts of morphisms of arrows

```agda
module foundation.lifts-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import orthogonal-factorization-systems.lifts-maps
```

</details>

## Idea

Given two [morphisms of arrows](foundation.morphisms-arrows.md) `α : f ⇒ h` and
`β : g ⇒ h`, then a
{{#concept "lift" Disambiguation="morphisms of arrows" Agda=lift-hom-arrow}} of
`α` along `β` is a morphism of arrows `γ : f ⇒ g` such that the triangle
`β ∘ γ ~ α` commutes.

## Definition

```agda
lift-hom-arrow :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : hom-arrow g h) (α : hom-arrow f h) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
lift-hom-arrow f g h α β =
  Σ (hom-arrow f g) (coherence-triangle-hom-arrow f g h β α)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (β : hom-arrow g h) (α : hom-arrow f h)
  (γ : lift-hom-arrow f g h β α)
  where

  hom-arrow-lift-hom-arrow : hom-arrow f g
  hom-arrow-lift-hom-arrow = pr1 γ

  coherence-triangle-lift-hom-arrow :
    coherence-triangle-hom-arrow f g h α β hom-arrow-lift-hom-arrow
  coherence-triangle-lift-hom-arrow = pr2 γ

  map-domain-lift-hom-arrow : A → B
  map-domain-lift-hom-arrow =
    map-domain-hom-arrow f g hom-arrow-lift-hom-arrow

  map-codomain-lift-hom-arrow : A' → B'
  map-codomain-lift-hom-arrow =
    map-codomain-hom-arrow f g hom-arrow-lift-hom-arrow

  coh-hom-arrow-lift-hom-arrow :
    coherence-hom-arrow f g
      ( map-domain-lift-hom-arrow)
      ( map-codomain-lift-hom-arrow)
  coh-hom-arrow-lift-hom-arrow =
    coh-hom-arrow f g hom-arrow-lift-hom-arrow

  coh-domain-lift-hom-arrow :
    coherence-triangle-maps
      ( map-domain-hom-arrow f h α)
      ( map-domain-hom-arrow g h β)
      ( map-domain-lift-hom-arrow)
  coh-domain-lift-hom-arrow =
    pr1 coherence-triangle-lift-hom-arrow

  coh-codomain-lift-hom-arrow :
    coherence-triangle-maps
      ( map-codomain-hom-arrow f h α)
      ( map-codomain-hom-arrow g h β)
      ( map-codomain-lift-hom-arrow)
  coh-codomain-lift-hom-arrow =
    pr1 (pr2 coherence-triangle-lift-hom-arrow)

  coh-lift-hom-arrow :
    coherence-htpy-hom-arrow f h α
      ( comp-hom-arrow f g h β hom-arrow-lift-hom-arrow)
      ( coh-domain-lift-hom-arrow)
      ( coh-codomain-lift-hom-arrow)
  coh-lift-hom-arrow =
    pr2 (pr2 coherence-triangle-lift-hom-arrow)

  lift-codomain-lift-hom-arrow :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α)
  lift-codomain-lift-hom-arrow =
    ( map-codomain-lift-hom-arrow , coh-codomain-lift-hom-arrow)
```

### The type of lifts extending a lift of the codomain

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  (let β₁ = map-codomain-hom-arrow g h β)
  where

  is-lift-hom-arrow-of-lift-codomain-hom-arrow :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α) →
    (A → B) → UU (l1 ⊔ l4 ⊔ l5 ⊔ l6)
  is-lift-hom-arrow-of-lift-codomain-hom-arrow (i , I) j =
    Σ ( coherence-hom-arrow f g j i)
      ( λ H →
        Σ ( coherence-triangle-maps
            ( map-domain-hom-arrow f h α)
            ( map-domain-hom-arrow g h β)
            ( j))
          ( λ J →
            coherence-htpy-hom-arrow f h α
              ( comp-hom-arrow f g h β (j , i , H))
              ( J)
              ( I)))

  lift-hom-arrow-of-lift-codomain-hom-arrow :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α) →
    UU (l1 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  lift-hom-arrow-of-lift-codomain-hom-arrow i =
    Σ (A → B) (is-lift-hom-arrow-of-lift-codomain-hom-arrow i)
```

## Properties

### Computing the fibers of `lift-codomain-lift-hom-arrow`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  (let β₁ = map-codomain-hom-arrow g h β)
  where

  compute-fiber-lift-codomain-lift-hom-arrow :
    (δ : lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α)) →
    fiber (lift-codomain-lift-hom-arrow f g h β α) δ ≃
    lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β δ
  compute-fiber-lift-codomain-lift-hom-arrow (δ , Hδ) =
    equivalence-reasoning
    Σ ( lift-hom-arrow f g h β α)
      ( λ γ → lift-codomain-lift-hom-arrow f g h β α γ ＝ (δ , Hδ))
    ≃ Σ ( lift-hom-arrow f g h β α)
        ( λ γ →
          Σ ( map-codomain-lift-hom-arrow f g h β α γ ~ δ)
            ( λ Hi → coh-codomain-lift-hom-arrow f g h β α γ ∙h β₁ ·l Hi ~ Hδ))
      by
      equiv-tot
        ( λ γ →
          extensionality-lift
            ( map-codomain-hom-arrow g h β)
            ( map-codomain-hom-arrow f h α)
            ( lift-codomain-lift-hom-arrow f g h β α γ)
            ( δ , Hδ))
    ≃ Σ ( Σ (A' → B') (_~ δ))
        ( λ (i , Hi) →
          Σ ( Σ ( coherence-triangle-maps
                  ( map-codomain-hom-arrow f h α)
                  ( map-codomain-hom-arrow g h β)
                  ( i))
                ( λ I → I ∙h β₁ ·l Hi ~ Hδ))
            ( λ (I , HI) →
              lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (i , I)))
      by reassociate
    ≃ Σ ( Σ ( coherence-triangle-maps
              ( map-codomain-hom-arrow f h α)
              ( map-codomain-hom-arrow g h β)
              ( δ))
            ( λ I → I ∙h β₁ ·l refl-htpy ~ Hδ))
        ( λ (I , HI) →
          lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (δ , I))
      by left-unit-law-Σ-is-contr (is-torsorial-htpy' δ) (δ , refl-htpy)
    ≃ Σ ( Σ ( coherence-triangle-maps
              ( map-codomain-hom-arrow f h α)
              ( map-codomain-hom-arrow g h β)
              ( δ))
            ( _~ Hδ))
        ( λ (I , HI) →
          lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (δ , I))
      by
      equiv-Σ-equiv-base
        ( λ (I , HI) →
          lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (δ , I))
        ( equiv-tot (λ I → equiv-concat-htpy inv-htpy-right-unit-htpy Hδ))
    ≃ lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (δ , Hδ)
      by left-unit-law-Σ-is-contr (is-torsorial-htpy' Hδ) (Hδ , refl-htpy)
    where
      reassociate :
        Σ ( lift-hom-arrow f g h β α)
          ( λ γ →
            Σ ( map-codomain-lift-hom-arrow f g h β α γ ~ δ)
              ( λ Hi →
                coh-codomain-lift-hom-arrow f g h β α γ ∙h β₁ ·l Hi ~ Hδ)) ≃
        Σ ( Σ (A' → B') (_~ δ))
          ( λ (i , Hi) →
            Σ ( Σ ( coherence-triangle-maps
                    ( map-codomain-hom-arrow f h α)
                    ( map-codomain-hom-arrow g h β)
                    ( i))
                  ( λ I → I ∙h β₁ ·l Hi ~ Hδ))
                ( λ (I , HI) →
                  lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β (i , I)))
      reassociate =
        ( ( λ (((γ₀ , γ₁ , Hγ) , (Γ₀ , Γ₁ , HΓ)) , (Hi , HI)) →
            ( (γ₁ , Hi) , (Γ₁ , HI) , γ₀ , Hγ , Γ₀ , HΓ)) ,
          ( is-equiv-is-invertible
            ( λ ((γ₁ , Hi) , (Γ₁ , HI) , γ₀ , Hγ , Γ₀ , HΓ) →
              ((γ₀ , γ₁ , Hγ) , (Γ₀ , Γ₁ , HΓ)) , (Hi , HI))
            ( refl-htpy)
            ( refl-htpy)))
```

### Computing the predicate of being a lift in terms of homotopies of cones

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  (let β₁ = map-codomain-hom-arrow g h β)
  (let Hβ = coh-hom-arrow g h β)
  (let Hα = coh-hom-arrow f h α)
  (iI@(i , I) :
    lift (map-codomain-hom-arrow g h β) (map-codomain-hom-arrow f h α))
  where

  equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow :
    (j : A → B) →
    is-lift-hom-arrow-of-lift-codomain-hom-arrow f g h α β iI j ≃
    htpy-cone β₁ h
      ( g ∘ j , map-domain-hom-arrow g h β ∘ j , Hβ ·r j)
      ( i ∘ f , map-domain-hom-arrow f h α , inv-htpy I ·r f ∙h Hα)
  equiv-htpy-cone-is-lift-hom-arrow-of-lift-codomain-hom-arrow j =
    equiv-Σ _
      ( equiv-inv-htpy (i ∘ f) (g ∘ j))
      ( λ H →
        equiv-Σ _
          ( equiv-inv-htpy
            ( map-domain-hom-arrow f h α)
            ( map-domain-hom-arrow g h β ∘ j))
          ( λ J →
            equivalence-reasoning
            ( Hα ∙h h ·l J ~ I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j))
            ≃ ( I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j) ~ Hα ∙h h ·l J)
              by equiv-inv-htpy (Hα ∙h h ·l J) (I ·r f ∙h (β₁ ·l H ∙h Hβ ·r j))
            ≃ ( β₁ ·l H ∙h Hβ ·r j ~ inv-htpy I ·r f ∙h (Hα ∙h h ·l J))
              by
              equiv-left-transpose-htpy-concat
                ( I ·r f)
                ( β₁ ·l H ∙h Hβ ·r j)
                ( Hα ∙h h ·l J)
            ≃ ( Hβ ·r j ~
                inv-htpy (β₁ ·l H) ∙h (inv-htpy I ·r f ∙h (Hα ∙h h ·l J)))
              by
              equiv-left-transpose-htpy-concat
                ( β₁ ·l H)
                ( Hβ ·r j)
                ( inv-htpy I ·r f ∙h (Hα ∙h h ·l J))
            ≃ ( Hβ ·r j ~
                ( β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα)) ∙h h ·l J)
              by
              equiv-concat-htpy'
                ( Hβ ·r j)
                ( ( right-whisker-concat-htpy
                    ( inv-htpy (left-whisker-inv-htpy β₁ H))
                    ( inv-htpy I ·r f ∙h (Hα ∙h h ·l J))) ∙h
                  ( left-whisker-concat-htpy
                    ( β₁ ·l (inv-htpy H))
                    ( inv-htpy-assoc-htpy (inv-htpy I ·r f) Hα (h ·l J))) ∙h
                  ( inv-htpy-assoc-htpy
                    ( β₁ ·l (inv-htpy H))
                    ( inv-htpy I ·r f ∙h Hα)
                    ( h ·l J)))
            ≃ ( Hβ ·r j ∙h inv-htpy (h ·l J) ~
                β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
              by
              equiv-right-transpose-htpy-concat'
                ( Hβ ·r j)
                ( β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
                ( h ·l J)
            ≃ ( Hβ ·r j ∙h h ·l inv-htpy J ~
                β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))
              by
              equiv-concat-htpy
                ( left-whisker-concat-htpy
                  ( Hβ ·r j)
                  ( left-whisker-inv-htpy h J))
                ( β₁ ·l inv-htpy H ∙h (inv-htpy I ·r f ∙h Hα))))
```
