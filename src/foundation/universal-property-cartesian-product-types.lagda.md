# The universal propert of cartesian product types

```agda
module foundation.universal-property-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.standard-pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

The universal property of cartesian products characterizes maps into a cartesian
product

## Theorems

### The universal property of cartesian products as pullbacks

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  map-up-product :
    ((x : X) → A x × B x) → (((x : X) → A x) × ((x : X) → B x))
  pr1 (map-up-product f) x = pr1 (f x)
  pr2 (map-up-product f) x = pr2 (f x)

  map-inv-up-product :
    (((x : X) → A x) × ((x : X) → B x)) → (x : X) → A x × B x
  pr1 (map-inv-up-product (f , g) x) = f x
  pr2 (map-inv-up-product (f , g) x) = g x

  up-product : is-equiv map-up-product
  up-product =
    is-equiv-is-invertible
      ( map-inv-up-product)
      ( refl-htpy)
      ( refl-htpy)

  is-equiv-map-inv-up-product : is-equiv map-inv-up-product
  is-equiv-map-inv-up-product = is-equiv-map-inv-is-equiv up-product

  equiv-up-product :
    ((x : X) → A x × B x) ≃ (((x : X) → A x) × ((x : X) → B x))
  pr1 equiv-up-product = map-up-product
  pr2 equiv-up-product = up-product

  inv-equiv-up-product :
    (((x : X) → A x) × ((x : X) → B x)) ≃ ((x : X) → A x × B x)
  inv-equiv-up-product = inv-equiv equiv-up-product
```

We construct the cone for two maps into the unit type.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  cone-product : cone (terminal-map A) (terminal-map B) (A × B)
  pr1 cone-product = pr1
  pr1 (pr2 cone-product) = pr2
  pr2 (pr2 cone-product) = refl-htpy
```

Cartesian products are a special case of pullbacks.

```agda
  gap-product : A × B → standard-pullback (terminal-map A) (terminal-map B)
  gap-product = gap (terminal-map A) (terminal-map B) cone-product

  inv-gap-product :
    standard-pullback (terminal-map A) (terminal-map B) → A × B
  pr1 (inv-gap-product (pair a (pair b p))) = a
  pr2 (inv-gap-product (pair a (pair b p))) = b

  abstract
    is-section-inv-gap-product : (gap-product ∘ inv-gap-product) ~ id
    is-section-inv-gap-product (pair a (pair b p)) =
      map-extensionality-standard-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( refl)
        ( refl)
        ( eq-is-contr (is-prop-is-contr is-contr-unit star star))

  is-retraction-inv-gap-product : inv-gap-product ∘ gap-product ~ id
  is-retraction-inv-gap-product (pair a b) = refl

  abstract
    is-pullback-cartesian-product :
      is-pullback (terminal-map A) (terminal-map B) cone-product
    is-pullback-cartesian-product =
      is-equiv-is-invertible
        inv-gap-product
        is-section-inv-gap-product
        is-retraction-inv-gap-product
```

We conclude that cartesian products satisfy the universal property of pullbacks.

```agda
  abstract
    universal-property-pullback-cartesian-product :
      universal-property-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( cone-product)
    universal-property-pullback-cartesian-product =
      universal-property-pullback-is-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( cone-product)
        ( is-pullback-cartesian-product)
```
