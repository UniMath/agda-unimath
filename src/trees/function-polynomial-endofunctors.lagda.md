# Function polynomial endofunctors

```agda
module trees.function-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given a [polynomial endofunctor](trees.polynomial-endofunctors.md) `𝑃` and a
type `I` then there is a
{{#concept "function polynomial endofunctor" Disambiguation="on types" Agda=function-polynomial-endofunctor}}
`𝑃ᴵ` given on shapes by `(𝑃ᴵ)₀ := I → 𝑃₀` and on positions by
`(𝑃ᴵ)₁(f) := Σ (i : I), 𝑃₁(f(i))`. This polynomial endofunctor satisfies the
[equivalence](foundation-core.equivalences.md)

```text
  𝑃ᴵ(X) ≃ (I → 𝑃(X)).
```

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (I : UU l1)
  (P@(A , B) : polynomial-endofunctor l2 l3)
  where

  shape-function-polynomial-endofunctor : UU (l1 ⊔ l2)
  shape-function-polynomial-endofunctor = I → A

  position-function-polynomial-endofunctor :
    shape-function-polynomial-endofunctor → UU (l1 ⊔ l3)
  position-function-polynomial-endofunctor f = Σ I (B ∘ f)

  function-polynomial-endofunctor : polynomial-endofunctor (l1 ⊔ l2) (l1 ⊔ l3)
  function-polynomial-endofunctor =
    ( shape-function-polynomial-endofunctor ,
      position-function-polynomial-endofunctor)

  compute-type-function-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    type-polynomial-endofunctor function-polynomial-endofunctor X ≃
    (I → type-polynomial-endofunctor P X)
  compute-type-function-polynomial-endofunctor =
    inv-distributive-Π-Σ ∘e equiv-tot (λ f → equiv-ev-pair)
```
