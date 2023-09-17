# Commuting hexagons of identifications

```agda
module foundation.commuting-hexagons-of-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

A hexagon of identifications is an identification
`((α ∙ β) ∙ γ) ＝ (δ ∙ (ε ∙ ζ))`.

## Definition

### Hexagons of identifications

```agda
coherence-hexagon :
  {l : Level} {A : UU l} {x u u' v v' y : A}
  (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
  (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) → UU l
coherence-hexagon α β γ δ ε ζ = ((α ∙ β) ∙ γ) ＝ (δ ∙ (ε ∙ ζ))
```

### Symmetries of hexagons of identifications

```agda
module _
  {l : Level} {A : UU l} {x u u' v v' y : A}
  where

  hexagon-rotate-120 :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv ε) (inv δ) α ζ (inv γ) (inv β)
  hexagon-rotate-120 refl refl refl refl refl .refl refl = refl

  hexagon-rotate-240 :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon γ (inv ζ) (inv ε) (inv β) (inv α) δ
  hexagon-rotate-240 refl refl refl refl refl .refl refl = refl

  hexagon-mirror-A :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon ε ζ (inv γ) (inv δ) α β
  hexagon-mirror-A refl refl refl refl refl .refl refl = refl

  hexagon-mirror-B :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv α) δ ε β γ (inv ζ)
  hexagon-mirror-B refl refl refl refl refl .refl refl = refl

  hexagon-mirror-C :
    (α : x ＝ u) (β : u ＝ u') (γ : u' ＝ y)
    (δ : x ＝ v) (ε : v ＝ v') (ζ : v' ＝ y) →
    coherence-hexagon α β γ δ ε ζ →
    coherence-hexagon (inv γ) (inv β) (inv α) (inv ζ) (inv ε) (inv δ)
  hexagon-mirror-C refl refl refl refl refl .refl refl = refl
```
