# Factorizations of maps

```agda
module orthogonal-factorization-systems.factorizations-of-maps where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.small-types
open import foundation.structure-identity-principle
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

## Idea

A _factorization_ of a map `f : A → B` is a pair of maps `g : X → B` and
`h : A → X` such that their composite `g ∘ h` is `f`.

```md
       X
      ^ \
   h /   \ g
    /     v
  A -----> B
      f
```

We use diagrammatic order and say the map `h` is the _left_ and `g` the _right_
map of the factorization.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-factorization :
    {l3 : Level} {X : UU l3} →
    (g : X → B) (h : A → X) → UU (l1 ⊔ l2)
  is-factorization g h = f ~ (g ∘ h)

  factorization-through : {l3 : Level} (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  factorization-through X =
    Σ ( X → B)
      ( λ g →
        Σ ( A → X)
          ( is-factorization g))

  factorization : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  factorization l3 = Σ (UU l3) (factorization-through)
```

### Destructors for factorizations

```agda
  right-map-factorization-through :
    {l3 : Level} {X : UU l3} → factorization-through X → X → B
  right-map-factorization-through = pr1

  left-map-factorization-through :
    {l3 : Level} {X : UU l3} → factorization-through X → A → X
  left-map-factorization-through = pr1 ∘ pr2

  is-factorization-factorization-through :
    {l3 : Level} {X : UU l3} (F : factorization-through X) →
      is-factorization
        ( right-map-factorization-through F)
        ( left-map-factorization-through F)
  is-factorization-factorization-through = pr2 ∘ pr2

  type-factorization : {l3 : Level} (F : factorization l3) → UU l3
  type-factorization = pr1

  factorization-through-factorization :
    {l3 : Level} (F : factorization l3) →
    factorization-through (type-factorization F)
  factorization-through-factorization = pr2

  right-map-factorization :
    {l3 : Level} (F : factorization l3) → type-factorization F → B
  right-map-factorization =
    right-map-factorization-through ∘ factorization-through-factorization

  left-map-factorization : 
    {l3 : Level} (F : factorization l3) → A → type-factorization F
  left-map-factorization =
    left-map-factorization-through ∘ factorization-through-factorization

  is-factorization-factorization :
    {l3 : Level} (F : factorization l3) →
    is-factorization (right-map-factorization F) (left-map-factorization F)
  is-factorization-factorization =
    is-factorization-factorization-through ∘ factorization-through-factorization
```
