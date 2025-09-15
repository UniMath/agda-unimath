# Lifts of morphisms of arrows

```agda
module foundation.lifts-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-morphisms-arrows
open import foundation.dependent-pair-types
open import foundation.morphisms-arrows
open import foundation.homotopies-morphisms-arrows
open import foundation.universe-levels
open import foundation.commuting-triangles-of-maps
```

</details>

## Idea

Given two [morphism of arrows](foundation.morphisms-arrows.md) `α : f ⇒ h` and
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
  (α : hom-arrow f h) (β : hom-arrow g h) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
lift-hom-arrow f g h α β =
  Σ (hom-arrow f g) (coherence-triangle-hom-arrow f g h α β)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {A' : UU l2} {B : UU l3} {B' : UU l4} {C : UU l5} {C' : UU l6}
  (f : A → A') (g : B → B') (h : C → C')
  (α : hom-arrow f h) (β : hom-arrow g h)
  (γ : lift-hom-arrow f g h α β)
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
      map-domain-lift-hom-arrow
      map-codomain-lift-hom-arrow
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
```
