# Pullback squares

```agda
module foundation.pullback-squares where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

A **pullback square**, or **cartesian square**, is a
[commuting square of maps](foundation.commuting-squares-of-maps.md) that
satisfies the
[universal property of being a pullback](foundation.universal-property-pullbacks.md).

## Definitions

### Pullback cones

```agda
module _
  {l1 l2 l3 l4 : Level} (l : Level) {A : UU l1} {B : UU l2} {C : UU l3}
  (f : A → C) (g : B → C) (X : UU l4)
  where

  pullback-cone : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  pullback-cone = Σ (cone f g X) (universal-property-pullback l f g)
```

### Pullback squares

```agda
module _
  {l1 l2 l3 l4 : Level} (l : Level) (A : UU l1) (B : UU l2) (C : UU l3)
  (X : UU l4)
  where

  pullback-square : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  pullback-square =
    Σ ( A → C)
      ( λ f →
        Σ ( B → C)
          ( λ g →
            Σ ( cone f g X)
              ( universal-property-pullback l f g)))
```

### Components of a pullback cone

```agda
module _
  {l1 l2 l3 l4 l : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (f : A → C) (g : B → C) (c : pullback-cone l f g X)
  where

  cone-pullback-cone : cone f g X
  cone-pullback-cone = pr1 c

  vertical-map-pullback-cone : X → A
  vertical-map-pullback-cone = vertical-map-cone f g cone-pullback-cone

  horizontal-map-pullback-cone : X → B
  horizontal-map-pullback-cone = horizontal-map-cone f g cone-pullback-cone

  coherence-square-pullback-cone :
    coherence-square-maps horizontal-map-pullback-cone
      ( vertical-map-pullback-cone)
      ( g)
      ( f)
  coherence-square-pullback-cone = coherence-square-cone f g cone-pullback-cone

  universal-property-pullback-cone : universal-property-pullback l f g (pr1 c)
  universal-property-pullback-cone = pr2 c
```
