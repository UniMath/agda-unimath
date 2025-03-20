# Descent for the empty type

```agda
open import foundation.function-extensionality-axiom

module
  foundation.descent-empty-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.pullbacks funext
```

</details>

## Theorem

```agda
module _
  {l1 l2 l3 : Level} {B : UU l1} {X : UU l2} {C : UU l3} (g : B → X)
  where

  cone-empty : is-empty C → (C → B) → cone ex-falso g C
  pr1 (cone-empty p q) = p
  pr1 (pr2 (cone-empty p q)) = q
  pr2 (pr2 (cone-empty p q)) c = ex-falso (p c)

  abstract
    descent-empty : (c : cone ex-falso g C) → is-pullback ex-falso g c
    descent-empty c =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone _ g c ind-empty

  abstract
    descent-empty' :
      (p : C → empty) (q : C → B) → is-pullback ex-falso g (cone-empty p q)
    descent-empty' p q = descent-empty (cone-empty p q)
```
