# Factorizations of maps

```agda
module orthogonal-factorization-systems.factorizations-of-maps where

open import foundation.contractible-types
open import foundation.contractible-maps
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

open import orthogonal-factorization-systems.local-types
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

  factorization : (l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  factorization l3 =
    Σ ( UU l3)
      ( λ X →
        Σ ( X → B)
          ( λ g →
            Σ ( A → X)
              ( is-factorization g)))

  type-factorization : {l3 : Level} (F : factorization l3) → UU l3
  type-factorization = pr1

  right-map-factorization :
    {l3 : Level} (F : factorization l3) → type-factorization F → B
  right-map-factorization = pr1 ∘ pr2

  left-map-factorization : 
    {l3 : Level} (F : factorization l3) → A → type-factorization F
  left-map-factorization = pr1 ∘ (pr2 ∘ pr2)

  is-factorization-factorization :
    {l3 : Level} (F : factorization l3) →
    is-factorization (right-map-factorization F) (left-map-factorization F)
  is-factorization-factorization = pr2 ∘ (pr2 ∘ pr2) 
```
