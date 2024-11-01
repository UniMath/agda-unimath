# Resizing posets

```agda
module order-theory.resizing-posets where
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
open import order-theory.posets
open import order-theory.preorders
open import order-theory.resizing-preorders
```

</details>

## Idea

Given a [poset](order-theory.posets.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized poset" Agda=resize-type-Poset}} on the small equivalent.

## Definition

### Resizing the underlying type of a poset

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  resize-type-Poset :
    (P : Poset l2 l3) → A ≃ type-Poset P → Poset l1 l3
  resize-type-Poset P e =
    ( resize-type-Preorder (preorder-Poset P) e ,
      ( λ x y p q →
      is-injective-equiv e
        ( antisymmetric-leq-Poset P (map-equiv e x) (map-equiv e y) p q)))
```

### The resizing structure equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (P : Poset l2 l3) (e : A ≃ type-Poset P)
  where

  hom-resize-type-Poset : hom-Poset (resize-type-Poset P e) P
  hom-resize-type-Poset = hom-resize-type-Preorder (preorder-Poset P) e

  hom-inv-resize-type-Poset : hom-Poset P (resize-type-Poset P e)
  hom-inv-resize-type-Poset = hom-inv-resize-type-Preorder (preorder-Poset P) e

  is-right-inverse-hom-inv-resize-type-Poset :
    htpy-hom-Poset P P
      ( comp-hom-Poset P (resize-type-Poset P e) P
        ( hom-resize-type-Poset)
        ( hom-inv-resize-type-Poset))
      ( id-hom-Poset P)
  is-right-inverse-hom-inv-resize-type-Poset =
    is-right-inverse-hom-inv-resize-type-Preorder (preorder-Poset P) e

  is-left-inverse-hom-inv-resize-type-Poset :
    htpy-hom-Poset (resize-type-Poset P e) (resize-type-Poset P e)
      ( comp-hom-Poset
        ( resize-type-Poset P e)
        ( P)
        ( resize-type-Poset P e)
        ( hom-inv-resize-type-Poset)
        ( hom-resize-type-Poset))
      ( id-hom-Poset (resize-type-Poset P e))
  is-left-inverse-hom-inv-resize-type-Poset =
    is-left-inverse-hom-inv-resize-type-Preorder (preorder-Poset P) e
```
