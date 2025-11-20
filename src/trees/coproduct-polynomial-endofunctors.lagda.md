# Coproduct polynomial endofunctors

```agda
module trees.coproduct-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

For every pair of polynomial endofunctor `𝑃` and `𝑄` there is a
{{#concept "coproduct polynomial endofunctor" Disambiguation="on types" Agda=coproduct-polynomial-endofunctor}}
`𝑃 + 𝑄` given on shapes by `(𝑃 + 𝑄)₀ := 𝑃₀ + 𝑄₀` and on positions by
`(𝑃 + 𝑄)₁(inl a) := 𝑃₁(a)` and `(𝑃 + 𝑄)₁(inr c) := 𝑄₁(c)`.

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
```
