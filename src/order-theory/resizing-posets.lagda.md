# Resizing posets

```agda
module order-theory.resizing-posets where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

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
open import foundation.small-types
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.precategory-of-posets
open import order-theory.preorders
open import order-theory.resizing-preorders
```

</details>

## Idea

Given a [poset](order-theory.posets.md) `P` on a
[small](foundation.small-types.md) carrier type `X`, then there is an equivalent
{{#concept "resized poset" Agda=resize-Poset}} on the small equivalent.

## Definition

### Resizing the underlying type of a poset

```agda
module _
  {l1 l2 l3 : Level}
  where

  resize-Poset :
    (P : Poset l1 l2) → is-small l3 (type-Poset P) → Poset l3 l2
  resize-Poset P (A , e) =
    ( resize-Preorder (preorder-Poset P) (A , e)) ,
    ( λ x y p q →
      is-injective-map-inv-equiv e
        ( antisymmetric-leq-Poset P
          ( map-inv-equiv e x)
          ( map-inv-equiv e y)
          ( p)
          ( q)))
```

### The resizing structure equivalence

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (H : is-small l3 (type-Poset P))
  where

  hom-resize-Poset : hom-Poset (resize-Poset P H) P
  hom-resize-Poset = hom-resize-Preorder (preorder-Poset P) H

  hom-inv-resize-Poset : hom-Poset P (resize-Poset P H)
  hom-inv-resize-Poset = hom-inv-resize-Preorder (preorder-Poset P) H

  is-right-inverse-hom-inv-resize-Poset :
    htpy-hom-Poset P P
      ( comp-hom-Poset P (resize-Poset P H) P
        ( hom-resize-Poset)
        ( hom-inv-resize-Poset))
      ( id-hom-Poset P)
  is-right-inverse-hom-inv-resize-Poset =
    is-right-inverse-hom-inv-resize-Preorder (preorder-Poset P) H

  is-left-inverse-hom-inv-resize-Poset :
    htpy-hom-Poset (resize-Poset P H) (resize-Poset P H)
      ( comp-hom-Poset
        ( resize-Poset P H)
        ( P)
        ( resize-Poset P H)
        ( hom-inv-resize-Poset)
        ( hom-resize-Poset))
      ( id-hom-Poset (resize-Poset P H))
  is-left-inverse-hom-inv-resize-Poset =
    is-left-inverse-hom-inv-resize-Preorder (preorder-Poset P) H

  is-iso-hom-resize-Poset :
    is-iso-Large-Precategory
      ( parametric-Poset-Large-Precategory (λ l → l) (λ _ → l2))
      { X = resize-Poset P H}
      { P}
      ( hom-resize-Poset)
  is-iso-hom-resize-Poset =
    ( hom-inv-resize-Poset) ,
    ( eq-htpy-hom-Poset P P
      ( comp-hom-Poset P (resize-Poset P H) P
        ( hom-resize-Poset)
        ( hom-inv-resize-Poset))
      ( id-hom-Poset P)
      ( is-right-inverse-hom-inv-resize-Poset)) ,
    ( eq-htpy-hom-Poset (resize-Poset P H) (resize-Poset P H)
      ( comp-hom-Poset (resize-Poset P H) P (resize-Poset P H)
        ( hom-inv-resize-Poset)
        ( hom-resize-Poset))
      ( id-hom-Poset (resize-Poset P H))
      ( is-left-inverse-hom-inv-resize-Poset))

  iso-resize-Poset :
    iso-Large-Precategory
      ( parametric-Poset-Large-Precategory (λ l → l) (λ _ → l2))
      ( resize-Poset P H)
      ( P)
  iso-resize-Poset = hom-resize-Poset , is-iso-hom-resize-Poset
```
