---
title: Type duality
---

```agda
module foundation.type-duality where

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.polynomial-endofunctors
open import foundation.small-types
open import foundation.universe-levels
```

## Idea

Given a univalent universe `𝒰`, we can define two closely related functors acting on all types. First there is the covariant functor given by

```md
  P_𝒰(A) := Σ (X : 𝒰), X → A.
```

This is a polynomial endofunctor. Second, there is the contravariant functor given by

```md
  P^𝒰(A) := A → 𝒰.
```

If the type `A` is locally 𝒰-small, then there is a map `φ_A : P_𝒰(A) → P^𝒰(A)`. This map is natural in `A`, and it is always an embedding. Furthermore, the map `φ_A` is an equivalence if and only if `A` is 𝒰-small.

## Definitions

### The polynomial endofunctor of a universe

```agda
type-polynomial-endofunctor-UU :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
type-polynomial-endofunctor-UU l = type-polynomial-endofunctor (UU l) (λ X → X)

map-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-polynomial-endofunctor-UU l A → type-polynomial-endofunctor-UU l B
map-polynomial-endofunctor-UU l = map-polynomial-endofunctor (UU l) (λ X → X)
```

### Type families

```agda
type-exp-UU : (l : Level) {l1 : Level} → UU l1 → UU (lsuc l ⊔ l1)
type-exp-UU l A = A → UU l

map-exp-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-exp-UU l B → type-exp-UU l A
map-exp-UU l f P = P ∘ f
```

## Properties

### If `A` is locally `l`-small, then we can construct a map `type-polynomial-endofunctor l A → type-exp-UU A`

```agda
transformation-is-locally-small-polynomial-endofunctor-UU :
  {l l1 : Level} {A : UU l1} → is-locally-small l A →
  type-polynomial-endofunctor-UU l A → type-exp-UU l A
transformation-is-locally-small-polynomial-endofunctor-UU H (X , f) a =
  Σ X (λ x → type-is-small (H (f x) a))

is-emb-transformation-is-locally-small-polynomial-endofunctor-UU :
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A) →
  is-emb (transformation-is-locally-small-polynomial-endofunctor-UU H)
is-emb-transformation-is-locally-small-polynomial-endofunctor-UU {l} {l1} {A} H (X , f) =
  fundamental-theorem-id
    {!!}
    ( λ Y → ap (transformation-is-locally-small-polynomial-endofunctor-UU H))
```
