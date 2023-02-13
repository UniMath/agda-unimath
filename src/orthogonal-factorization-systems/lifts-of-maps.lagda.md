{{#title  Lifts of maps}}

```agda
module orthogonal-factorization-systems.lifts-of-maps where

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels


open import orthogonal-factorization-systems.extensions-of-maps
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

  is-lift : {X : UU l3} → (X → B) → (X → A) → UU (l2 ⊔ l3)
  is-lift f g = f ~ (i ∘ g)

  lift : {X : UU l3} → (X → B) → UU (l1 ⊔ l2 ⊔ l3)
  lift {X = X} f = Σ (X → A) (is-lift f)

  total-lift : (X : UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  total-lift X = Σ (X → B) lift
```

## Properties

### The total type of lifts is equivalent to `X → A`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (i : A → B) (X : UU l3)
  where

  inv-compute-total-lift : total-lift i X ≃ (X → A)
  inv-compute-total-lift =
    ( right-unit-law-Σ-is-contr ((λ f → is-contr-total-htpy' (i ∘ f)))) ∘e
    ( equiv-left-swap-Σ)

  compute-total-lift : (X → A) ≃ total-lift i X
  compute-total-lift = inv-equiv inv-compute-total-lift
```

## Properties

### If `P` is `k`-truncated then the type of lifts is `k`-truncated

```agda
module _
  {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (i : A → B)
  where

  is-trunc-is-lift :
    {X : UU l3} (f : X → B) →
    is-trunc (succ-𝕋 k) B → (g : X → A) → is-trunc k (is-lift i f g)
  is-trunc-is-lift f is-trunc-B g =
    is-trunc-Π k (λ x → is-trunc-B (f x) (i (g x)))

  is-trunc-lift :
    {X : UU l3} (f : X → B) →
    is-trunc k A → is-trunc (succ-𝕋 k) B → is-trunc k (lift i f)
  is-trunc-lift f is-trunc-A is-trunc-B =
    is-trunc-Σ
      ( is-trunc-function-type k is-trunc-A)
      ( is-trunc-is-lift f is-trunc-B)
  
  is-trunc-total-lift :
    (X : UU l3) → is-trunc k A → is-trunc k (total-lift i X)
  is-trunc-total-lift X is-trunc-A =
    is-trunc-equiv' k
      ( X → A)
      ( compute-total-lift i X)
      ( is-trunc-function-type k is-trunc-A)
```

## See also

- [`orthogonal-factorization-systems.extensions-of-maps`](orthogonal-factorization-systems.extensions-of-maps.html) for the dual notion.
