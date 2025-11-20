# Cartesian product polynomial endofunctors

```agda
module trees.cartesian-product-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

For every pair of polynomial endofunctor `𝑃` and `𝑄` there is a
{{#concept "cartesian product polynomial endofunctor" Disambiguation="on types" Agda=product-polynomial-endofunctor}}
`𝑃 × 𝑄` given on shapes by `(𝑃 × 𝑄)₀ := 𝑃₀ × 𝑄₀` and on positions by
`(𝑃 × 𝑄)₁(a , c) := 𝑃₁(a) × 𝑄₁(c)`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P@(A , B) : polynomial-endofunctor l1 l2)
  (Q@(C , D) : polynomial-endofunctor l3 l4)
  where

  shape-product-polynomial-endofunctor : UU (l1 ⊔ l3)
  shape-product-polynomial-endofunctor = A × C

  position-product-polynomial-endofunctor :
    shape-product-polynomial-endofunctor → UU (l2 ⊔ l4)
  position-product-polynomial-endofunctor (a , c) = B a × D c

  product-polynomial-endofunctor : polynomial-endofunctor (l1 ⊔ l3) (l2 ⊔ l4)
  product-polynomial-endofunctor =
    ( shape-product-polynomial-endofunctor ,
      position-product-polynomial-endofunctor)
```
