# Truncated maps

```agda
module foundation.truncated-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation-core.truncated-maps public

open import foundation-core.cones-pullbacks
open import foundation-core.dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-fibers-of-maps
open import foundation-core.propositions
open import foundation-core.pullbacks
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels
```

</details>

## Properties

### Being a truncated map is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-is-trunc-map : (k : 𝕋) (f : A → B) → is-prop (is-trunc-map k f)
  is-prop-is-trunc-map k f = is-prop-Π (λ x → is-prop-is-trunc k (fib f x))

  is-trunc-map-Prop : (k : 𝕋) → (A → B) → Prop (l1 ⊔ l2)
  pr1 (is-trunc-map-Prop k f) = is-trunc-map k f
  pr2 (is-trunc-map-Prop k f) = is-prop-is-trunc-map k f
```

### Pullbacks of truncated maps are truncated maps

```agda
module _
  {l1 l2 l3 l4 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  abstract
    is-trunc-is-pullback :
      is-pullback f g c → is-trunc-map k g → is-trunc-map k (pr1 c)
    is-trunc-is-pullback pb is-trunc-g a =
      is-trunc-is-equiv k
        ( fib g (f a))
        ( map-fib-cone f g c a)
        ( is-fiberwise-equiv-map-fib-cone-is-pullback f g c pb a)
        ( is-trunc-g (f a))

abstract
  is-trunc-is-pullback' :
    {l1 l2 l3 l4 : Level} (k : 𝕋)
    {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
    (f : A → X) (g : B → X) (c : cone f g C) →
    is-pullback f g c → is-trunc-map k f → is-trunc-map k (pr1 (pr2 c))
  is-trunc-is-pullback' k f g (pair p (pair q H)) pb is-trunc-f =
    is-trunc-is-pullback k g f
      ( swap-cone f g (triple p q H))
      ( is-pullback-swap-cone f g (triple p q H) pb)
      is-trunc-f
```
