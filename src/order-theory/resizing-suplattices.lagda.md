# Resizing suplattices

```agda
module order-theory.resizing-suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.suplattices
open import order-theory.resizing-posets
```

</details>

## Idea

Given a [suplattice](order-theory.suplattices.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized suplattice" Agda=resize-type-Suplattice}} on the small
equivalent.

## Definitions

### Resizing the underlying type of a suplattice

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1}
  (P : Suplattice l2 l3 l4) (e : A ≃ type-Suplattice P)
  where

  poset-resize-type-Suplattice : Poset l1 l3
  poset-resize-type-Suplattice =
    resize-type-Poset (poset-Suplattice P) e

  sup-resize-type-Suplattice :
    {I : UU l4} → (I → A) → A
  sup-resize-type-Suplattice x =
    map-inv-equiv e (sup-Suplattice P (map-equiv e ∘ x))

  is-least-upper-bound-sup-resize-type-Suplattice :
    {I : UU l4} (x : I → A) →
    is-least-upper-bound-family-of-elements-Poset poset-resize-type-Suplattice x
      ( sup-resize-type-Suplattice x)
  is-least-upper-bound-sup-resize-type-Suplattice x u =
      ( concatenate-eq-leq-Poset
          ( poset-Suplattice P)
          ( is-section-map-inv-equiv e (sup-Suplattice P (map-equiv e ∘ x))) ∘
        pr1
          ( is-least-upper-bound-sup-Suplattice P
            ( map-equiv e ∘ x)
            ( map-equiv e u))) ,
      ( pr2
          ( is-least-upper-bound-sup-Suplattice P
            ( map-equiv e ∘ x)
            ( map-equiv e u)) ∘
          ( concatenate-eq-leq-Poset
            ( poset-Suplattice P)
            ( inv
              ( is-section-map-inv-equiv e
                ( sup-Suplattice P (map-equiv e ∘ x))))))

  is-suplattice-resize-type-Suplattice :
    is-suplattice-Poset l4 poset-resize-type-Suplattice
  is-suplattice-resize-type-Suplattice I x =
    ( sup-resize-type-Suplattice x ,
      is-least-upper-bound-sup-resize-type-Suplattice x)

  resize-type-Suplattice : Suplattice l1 l3 l4
  resize-type-Suplattice =
    ( poset-resize-type-Suplattice ,
      is-suplattice-resize-type-Suplattice)
```
