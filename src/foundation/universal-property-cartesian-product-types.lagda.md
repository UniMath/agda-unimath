# The universal properties of cartesian product types

```agda
open import foundation.function-extensionality-axiom

module
  foundation.universal-property-cartesian-product-types
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.logical-equivalences funext
open import foundation.standard-pullbacks funext
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks funext
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universal-property-pullbacks funext
```

</details>

## Idea

[Cartesian products](foundation-core.cartesian-product-types.md) have universal
properties both as limits and as colimits of types. The
{{#concept "universal property of cartesian products as limits"}} states that,
given types `A`, `B` and `X`, maps _into_ the cartesian product `X → A × B` are
in [correspondence](foundation-core.equivalences.md) with pairs of maps `X → A`
and `X → B`. The
{{#concept "universal property of cartesian products as colimits"}} states that
maps _out of_ the cartesian product `A × B → X` are in correspondence with
"curried" maps `A → B → X`.

Observe that the universal property of cartesian products as limits can be
understood as a categorified version of the familiar distributivity of exponents
over products

$$
(A × B)^X ≃ A^X × B^X,
$$

while the universal property of cartesian products as colimits are a
categorified version of the identity

$$
X^{(A × B)} ≃ {(X^B)}^A.
$$

## Theorems

### The universal property of cartesian products as limits

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3}
  where

  map-up-product :
    ((x : X) → A x × B x) → ((x : X) → A x) × ((x : X) → B x)
  pr1 (map-up-product f) x = pr1 (f x)
  pr2 (map-up-product f) x = pr2 (f x)

  map-inv-up-product :
    (((x : X) → A x) × ((x : X) → B x)) → (x : X) → A x × B x
  pr1 (map-inv-up-product (f , g) x) = f x
  pr2 (map-inv-up-product (f , g) x) = g x

  iff-up-product :
    ((x : X) → A x × B x) ↔ ((x : X) → A x) × ((x : X) → B x)
  iff-up-product = (map-up-product , map-inv-up-product)

  up-product : is-equiv map-up-product
  up-product =
    is-equiv-is-invertible (map-inv-up-product) (refl-htpy) (refl-htpy)

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

#### The universal property of cartesian products as pullbacks

A different way to state the universal property of cartesian products as limits
is to say that the canonical [cone](foundation.cones-over-cospan-diagrams.md)
over the [terminal type `unit`](foundation.unit-type.md)

```text
           pr2
   A × B ------> B
     |           |
 pr1 |           |
     ∨           ∨
     A -------> unit
```

is a [pullback](foundation-core.pullbacks.md). The
[universal property of pullbacks](foundation-core.universal-property-pullbacks.md)
states in this case that maps into `A × B` are in correspondence with pairs of
maps into `A` and `B` such that the square

```text
     X --------> B
     |           |
     |           |
     ∨           ∨
     A -------> unit
```

[commutes](foundation-core.commuting-squares-of-maps.md). However, all parallel
maps into the terminal type are [equal](foundation-core.identity-types.md),
hence the coherence requirement is redundant.

We start by constructing the cone for two maps into the unit type.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  cone-cartesian-product : cone (terminal-map A) (terminal-map B) (A × B)
  pr1 cone-cartesian-product = pr1
  pr1 (pr2 cone-cartesian-product) = pr2
  pr2 (pr2 cone-cartesian-product) = refl-htpy
```

Next, we show that cartesian products are a special case of pullbacks.

```agda
  gap-cartesian-product :
    A × B → standard-pullback (terminal-map A) (terminal-map B)
  gap-cartesian-product =
    gap (terminal-map A) (terminal-map B) cone-cartesian-product

  inv-gap-cartesian-product :
    standard-pullback (terminal-map A) (terminal-map B) → A × B
  pr1 (inv-gap-cartesian-product (a , b , p)) = a
  pr2 (inv-gap-cartesian-product (a , b , p)) = b

  abstract
    is-section-inv-gap-cartesian-product :
      is-section gap-cartesian-product inv-gap-cartesian-product
    is-section-inv-gap-cartesian-product (a , b , p) =
      eq-Eq-standard-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( refl)
        ( refl)
        ( eq-is-contr (is-prop-unit star star))

  is-retraction-inv-gap-cartesian-product :
    is-retraction gap-cartesian-product inv-gap-cartesian-product
  is-retraction-inv-gap-cartesian-product (a , b) = refl

  abstract
    is-pullback-cartesian-product :
      is-pullback (terminal-map A) (terminal-map B) cone-cartesian-product
    is-pullback-cartesian-product =
      is-equiv-is-invertible
        inv-gap-cartesian-product
        is-section-inv-gap-cartesian-product
        is-retraction-inv-gap-cartesian-product
```

We conclude that cartesian products satisfy the universal property of pullbacks.

```agda
  abstract
    universal-property-pullback-cartesian-product :
      universal-property-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( cone-cartesian-product)
    universal-property-pullback-cartesian-product =
      universal-property-pullback-is-pullback
        ( terminal-map A)
        ( terminal-map B)
        ( cone-cartesian-product)
        ( is-pullback-cartesian-product)
```

### The universal property of cartesian products as colimits

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A × B → UU l3}
  where

  equiv-ind-product : ((x : A) (y : B) → C (x , y)) ≃ ((t : A × B) → C t)
  equiv-ind-product = equiv-ind-Σ
```
