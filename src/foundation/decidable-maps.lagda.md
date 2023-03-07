# Decidable maps

```agda
module foundation.decidable-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.retractions
open import foundation.universe-levels
```

</details>

## Definition

A map is said to be decidable if its fibers are decidable types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)
```

```agda
is-decidable-map-retr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retr i → is-decidable-map i
is-decidable-map-retr d i (pair r R) b =
  is-decidable-iff
    ( λ (p : i (r b) ＝ b) → pair (r b) p)
    ( λ t → ap (i ∘ r) (inv (pr2 t)) ∙ (ap i (R (pr1 t)) ∙ pr2 t))
    ( d (i (r b)) b)
```
