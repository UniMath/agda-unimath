# Resizing preorders

```agda
module order-theory.resizing-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.small-types
open import foundation.universe-levels

open import order-theory.order-preserving-maps-preorders
open import order-theory.preorders
```

</details>

## Idea

Given a [preorder](order-theory.preorders.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized preorder" Agda=resize-Preorder}} on the small equivalent.

## Definition

### Resizing the underlying type of a preorder

```agda
module _
  {l1 l2 l3 : Level}
  where

  resize-Preorder :
    (P : Preorder l1 l2) → is-small l3 (type-Preorder P) → Preorder l3 l2
  resize-Preorder P (A , e) =
    ( ( A) ,
      ( λ x y → leq-prop-Preorder P (map-inv-equiv e x) (map-inv-equiv e y)) ,
      ( λ x → refl-leq-Preorder P (map-inv-equiv e x)) ,
      ( λ x y z →
        transitive-leq-Preorder P
          ( map-inv-equiv e x)
          ( map-inv-equiv e y)
          ( map-inv-equiv e z)))
```

### The resizing structure equivalence

```agda
module _
  {l1 l2 l3 : Level} (P : Preorder l1 l2) (H : is-small l3 (type-Preorder P))
  where

  hom-resize-Preorder : hom-Preorder (resize-Preorder P H) P
  pr1 hom-resize-Preorder = map-inv-equiv-is-small H
  pr2 hom-resize-Preorder _ _ = id

  hom-inv-resize-Preorder : hom-Preorder P (resize-Preorder P H)
  pr1 hom-inv-resize-Preorder = map-equiv-is-small H
  pr2 hom-inv-resize-Preorder x y v =
    concatenate-leq-eq-Preorder P
      ( concatenate-eq-leq-Preorder P
        ( is-retraction-map-inv-equiv-is-small H x)
        ( v))
      ( inv (is-retraction-map-inv-equiv-is-small H y))

  is-right-inverse-hom-inv-resize-Preorder :
    htpy-hom-Preorder P P
      ( comp-hom-Preorder P (resize-Preorder P H) P
        ( hom-resize-Preorder)
        ( hom-inv-resize-Preorder))
      ( id-hom-Preorder P)
  is-right-inverse-hom-inv-resize-Preorder =
    is-retraction-map-inv-equiv-is-small H

  is-left-inverse-hom-inv-resize-Preorder :
    htpy-hom-Preorder (resize-Preorder P H) (resize-Preorder P H)
      ( comp-hom-Preorder
        ( resize-Preorder P H)
        ( P)
        ( resize-Preorder P H)
        ( hom-inv-resize-Preorder)
        ( hom-resize-Preorder))
      ( id-hom-Preorder (resize-Preorder P H))
  is-left-inverse-hom-inv-resize-Preorder =
    is-section-map-inv-equiv-is-small H
```
