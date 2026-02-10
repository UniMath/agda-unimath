# Coproduct polynomial endofunctors

```agda
module trees.coproduct-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

For every pair of [polynomial endofunctors](trees.polynomial-endofunctors.md)
`𝑃` and `𝑄` there is a
{{#concept "coproduct polynomial endofunctor" Disambiguation="on types" Agda=coproduct-polynomial-endofunctor}}
`𝑃 + 𝑄` given on shapes by `(𝑃 + 𝑄)₀ := 𝑃₀ + 𝑄₀` and on positions by
`(𝑃 + 𝑄)₁(inl a) := 𝑃₁(a)` and `(𝑃 + 𝑄)₁(inr c) := 𝑄₁(c)`. This polynomial
endofunctor satisfies the [equivalence](foundation-core.equivalences.md)

```text
  (𝑃 + 𝑄)(X) ≃ 𝑃(X) + 𝑄(X).
```

Note that for this definition to make sense, the positions of `𝑃` and `𝑄` have
to live in the same universe.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  (P@(A , B) : polynomial-endofunctor l1 l3)
  (Q@(C , D) : polynomial-endofunctor l2 l3)
  where

  shape-coproduct-polynomial-endofunctor : UU (l1 ⊔ l2)
  shape-coproduct-polynomial-endofunctor = A + C

  position-coproduct-polynomial-endofunctor :
    shape-coproduct-polynomial-endofunctor → UU l3
  position-coproduct-polynomial-endofunctor (inl a) = B a
  position-coproduct-polynomial-endofunctor (inr c) = D c

  coproduct-polynomial-endofunctor : polynomial-endofunctor (l1 ⊔ l2) l3
  coproduct-polynomial-endofunctor =
    ( shape-coproduct-polynomial-endofunctor ,
      position-coproduct-polynomial-endofunctor)

  map-compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    type-polynomial-endofunctor coproduct-polynomial-endofunctor X →
    type-polynomial-endofunctor P X + type-polynomial-endofunctor Q X
  map-compute-type-coproduct-polynomial-endofunctor (inl a , b) = inl (a , b)
  map-compute-type-coproduct-polynomial-endofunctor (inr c , d) = inr (c , d)

  map-inv-compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    type-polynomial-endofunctor P X + type-polynomial-endofunctor Q X →
    type-polynomial-endofunctor coproduct-polynomial-endofunctor X
  map-inv-compute-type-coproduct-polynomial-endofunctor (inl (a , b)) =
    (inl a , b)
  map-inv-compute-type-coproduct-polynomial-endofunctor (inr (c , d)) =
    (inr c , d)

  is-section-map-inv-compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    is-section
      ( map-compute-type-coproduct-polynomial-endofunctor {X = X})
      ( map-inv-compute-type-coproduct-polynomial-endofunctor {X = X})
  is-section-map-inv-compute-type-coproduct-polynomial-endofunctor (inl x) =
    refl
  is-section-map-inv-compute-type-coproduct-polynomial-endofunctor (inr y) =
    refl

  is-retraction-map-inv-compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    is-retraction
      ( map-compute-type-coproduct-polynomial-endofunctor {X = X})
      ( map-inv-compute-type-coproduct-polynomial-endofunctor {X = X})
  is-retraction-map-inv-compute-type-coproduct-polynomial-endofunctor
    ( inl x , _) =
    refl
  is-retraction-map-inv-compute-type-coproduct-polynomial-endofunctor
    ( inr y , _) =
    refl

  is-equiv-map-compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    is-equiv (map-compute-type-coproduct-polynomial-endofunctor {X = X})
  is-equiv-map-compute-type-coproduct-polynomial-endofunctor =
    is-equiv-is-invertible
      ( map-inv-compute-type-coproduct-polynomial-endofunctor)
      ( is-section-map-inv-compute-type-coproduct-polynomial-endofunctor)
      ( is-retraction-map-inv-compute-type-coproduct-polynomial-endofunctor)

  compute-type-coproduct-polynomial-endofunctor :
    {l : Level} {X : UU l} →
    type-polynomial-endofunctor coproduct-polynomial-endofunctor X ≃
    type-polynomial-endofunctor P X + type-polynomial-endofunctor Q X
  compute-type-coproduct-polynomial-endofunctor =
    ( map-compute-type-coproduct-polynomial-endofunctor ,
      is-equiv-map-compute-type-coproduct-polynomial-endofunctor)
```
