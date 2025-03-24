# Resizing suplattices

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.resizing-suplattices
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations funext univalence truncations
open import foundation.cartesian-product-types funext univalence
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.injective-maps funext
open import foundation.negated-equality funext univalence truncations
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.small-types funext univalence truncations
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets funext univalence truncations
open import order-theory.order-preserving-maps-posets funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.resizing-posets funext univalence truncations
open import order-theory.suplattices funext univalence truncations
```

</details>

## Idea

Given a [suplattice](order-theory.suplattices.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized suplattice" Agda=resize-Suplattice}} on the small
equivalent.

## Definitions

### Resizing the underlying type of a suplattice

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Suplattice l1 l2 l3) (H : is-small l4 (type-Suplattice P))
  where

  poset-resize-Suplattice : Poset l4 l2
  poset-resize-Suplattice =
    resize-Poset (poset-Suplattice P) H

  sup-resize-Suplattice :
    {I : UU l3} → (I → type-is-small H) → type-is-small H
  sup-resize-Suplattice x =
    map-equiv-is-small H (sup-Suplattice P (map-inv-equiv-is-small H ∘ x))

  is-least-upper-bound-sup-resize-Suplattice :
    {I : UU l3} (x : I → type-is-small H) →
    is-least-upper-bound-family-of-elements-Poset poset-resize-Suplattice x
      ( sup-resize-Suplattice x)
  is-least-upper-bound-sup-resize-Suplattice x u =
      ( concatenate-eq-leq-Poset
          ( poset-Suplattice P)
          ( is-retraction-map-inv-equiv-is-small H
            ( sup-Suplattice P (map-inv-equiv-is-small H ∘ x))) ∘
        pr1
          ( is-least-upper-bound-sup-Suplattice P
            ( map-inv-equiv-is-small H ∘ x)
            ( map-inv-equiv-is-small H u))) ,
      ( pr2
          ( is-least-upper-bound-sup-Suplattice P
            ( map-inv-equiv-is-small H ∘ x)
            ( map-inv-equiv-is-small H u)) ∘
          ( concatenate-eq-leq-Poset
            ( poset-Suplattice P)
            ( inv
              ( is-retraction-map-inv-equiv-is-small H
                ( sup-Suplattice P (map-inv-equiv-is-small H ∘ x))))))

  is-suplattice-resize-Suplattice :
    is-suplattice-Poset l3 poset-resize-Suplattice
  is-suplattice-resize-Suplattice I x =
    ( sup-resize-Suplattice x ,
      is-least-upper-bound-sup-resize-Suplattice x)

  resize-Suplattice : Suplattice l4 l2 l3
  resize-Suplattice =
    ( poset-resize-Suplattice ,
      is-suplattice-resize-Suplattice)
```
