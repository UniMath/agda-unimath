# Resizing preorders

```agda
module order-theory.resizing-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import order-theory.order-preserving-maps-preorders
open import order-theory.preorders
open import foundation.function-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

Given a [preorder](order-theory.preorders.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized preorder" Agda=resize-type-Preorder}} on the small
equivalent.

## Definition

### Resizing the underlying type of a preorder

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  resize-type-Preorder :
    (P : Preorder l2 l3) → A ≃ type-Preorder P → Preorder l1 l3
  resize-type-Preorder P e =
    ( ( A) ,
      ( λ x y → leq-prop-Preorder P (map-equiv e x) (map-equiv e y)) ,
      ( λ x → refl-leq-Preorder P (map-equiv e x)) ,
      ( λ x y z →
        transitive-leq-Preorder P
          ( map-equiv e x)
          ( map-equiv e y)
          ( map-equiv e z)))
```

### The resizing structure equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : Preorder l2 l3) (e : A ≃ type-Preorder P)
  where

  hom-resize-type-Preorder : hom-Preorder (resize-type-Preorder P e) P
  pr1 hom-resize-type-Preorder = map-equiv e
  pr2 hom-resize-type-Preorder _ _ = id

  hom-inv-resize-type-Preorder : hom-Preorder P (resize-type-Preorder P e)
  pr1 hom-inv-resize-type-Preorder = map-inv-equiv e
  pr2 hom-inv-resize-type-Preorder x y v =
    concatenate-leq-eq-Preorder P
      ( concatenate-eq-leq-Preorder P (is-section-map-inv-equiv e x) v)
      ( inv (is-section-map-inv-equiv e y))

  is-right-inverse-hom-inv-resize-type-Preorder :
    htpy-hom-Preorder P P
      ( comp-hom-Preorder P (resize-type-Preorder P e) P
        ( hom-resize-type-Preorder)
        ( hom-inv-resize-type-Preorder))
      ( id-hom-Preorder P)
  is-right-inverse-hom-inv-resize-type-Preorder = is-section-map-inv-equiv e

  is-left-inverse-hom-inv-resize-type-Preorder :
    htpy-hom-Preorder (resize-type-Preorder P e) (resize-type-Preorder P e)
      ( comp-hom-Preorder
        ( resize-type-Preorder P e)
        ( P)
        ( resize-type-Preorder P e)
        ( hom-inv-resize-type-Preorder)
        ( hom-resize-type-Preorder))
      ( id-hom-Preorder (resize-type-Preorder P e))
  is-left-inverse-hom-inv-resize-type-Preorder = is-retraction-map-inv-equiv e
```
