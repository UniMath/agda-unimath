# Descent for the empty type

```agda
module foundation.descent-empty-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.pullbacks
```

</details>

## Theorem

```agda
module _
  {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} (g : B → X)
  where

  cone-empty : is-empty C → (C → B) → cone ex-falso g C
  cone-empty p q = triple p q (λ c → ex-falso (p c))

  abstract
    descent-empty : (c : cone ex-falso g C) → is-pullback ex-falso g c
    descent-empty c =
      is-pullback-is-fiberwise-equiv-map-fiber-cone _ g c ind-empty

  abstract
    descent-empty' :
      (p : C → empty) (q : C → B) → is-pullback ex-falso g (cone-empty p q)
    descent-empty' p q = descent-empty (cone-empty p q)
```
