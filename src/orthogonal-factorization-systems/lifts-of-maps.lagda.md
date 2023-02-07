---
title: Lifts of maps
---

```agda
module orthogonal-factorization-systems.lifts-of-maps where

open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
open import foundation-core.universe-levels

open import foundation.extensions-of-maps
```

## Idea

A _lift_ of a map `f : X → B` along a map `i : A → B`
is a map `g : X → A` such that the composition `i ∘ g` is `f`.

```md
           A
          ^|
        /  i
      g    |
    /      v
  X - f -> B
```

## Definition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-lift-of : {X : UU l3} → (X → B) → (X → A) → UU (l2 ⊔ l3)
  is-lift-of f g = f ~ (i ∘ g)

  lift-of : {X : UU l3} → (X → B) → UU (l1 ⊔ l2 ⊔ l3)
  lift-of {X = X} f = Σ (X → A) (is-lift-of f)

  lift : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  lift X = Σ (X → B) (lift-of)
```

### If `P` is `k`-truncated then the type of lifts is `k`-truncated

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-lift :
    (k : 𝕋) → is-trunc (succ-𝕋 k) B →
    {X : UU l3} (f : X → B) (g : X → A) → is-trunc k (is-lift-of i f g)
  is-trunc-is-lift k is-trunc-B f g =
    is-trunc-Π k (λ x → is-trunc-B (f x) (i (g x)))

  is-trunc-lift-of :
    (k : 𝕋) → is-trunc k A → is-trunc (succ-𝕋 k) B →
    {X : UU l3} (f : X → B) → is-trunc k (lift-of i f)
  is-trunc-lift-of k is-trunc-A is-trunc-B f =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-A)
      ( is-trunc-is-lift k is-trunc-B f)
  
  is-trunc-lift :
    (k : 𝕋) → is-trunc k A → is-trunc k B →
    (X : UU l3) → is-trunc k (lift i X)
  is-trunc-lift k is-trunc-A is-trunc-B X =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-B)
      ( is-trunc-lift-of k
        ( is-trunc-A)
        ( is-trunc-succ-is-trunc k is-trunc-B))
```

## See also

- [foundation.extensions-of-maps](foundation.extensions-of-maps.html) for the dual notion.
