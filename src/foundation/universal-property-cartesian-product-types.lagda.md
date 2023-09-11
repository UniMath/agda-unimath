# The universal propert of cartesian product types

```agda
module foundation.universal-property-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospans
open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
open import foundation-core.universal-property-pullbacks
```

</details>

## Idea

The universal property of cartesian products characterizes maps into a cartesian
product

## Theorems

### The universal property of cartesian products as pullbacks

```agda
universal-property-product :
  {l1 l2 l3 : Level} {X : UU l1} {A : X → UU l2} {B : X → UU l3} →
  ((x : X) → A x × B x) ≃ (((x : X) → A x) × ((x : X) → B x))
pr1 universal-property-product f = (λ x → pr1 (f x)) , (λ x → pr2 (f x))
pr2 universal-property-product =
  is-equiv-is-invertible
    ( λ (f , g) → (λ x → (f x , g x)))
    ( refl-htpy)
    ( refl-htpy)

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
```

We construct the cone for two maps into the unit type.

```agda
  cone-prod : cone (const A unit star) (const B unit star) (A × B)
  pr1 cone-prod = pr1
  pr1 (pr2 cone-prod) = pr2
  pr2 (pr2 cone-prod) = refl-htpy
```

Cartesian products are a special case of pullbacks.

```agda
  gap-prod : A × B → canonical-pullback (const A unit star) (const B unit star)
  gap-prod = gap (const A unit star) (const B unit star) cone-prod

  inv-gap-prod :
    canonical-pullback (const A unit star) (const B unit star) → A × B
  pr1 (inv-gap-prod (pair a (pair b p))) = a
  pr2 (inv-gap-prod (pair a (pair b p))) = b

  abstract
    is-section-inv-gap-prod : (gap-prod ∘ inv-gap-prod) ~ id
    is-section-inv-gap-prod (pair a (pair b p)) =
      map-extensionality-canonical-pullback
        ( const A unit star)
        ( const B unit star)
        ( refl)
        ( refl)
        ( eq-is-contr (is-prop-is-contr is-contr-unit star star))

  abstract
    is-retraction-inv-gap-prod : (inv-gap-prod ∘ gap-prod) ~ id
    is-retraction-inv-gap-prod (pair a b) = eq-pair-Σ refl refl

  abstract
    is-pullback-prod :
      is-pullback (const A unit star) (const B unit star) cone-prod
    is-pullback-prod =
      is-equiv-is-invertible
        inv-gap-prod
        is-section-inv-gap-prod
        is-retraction-inv-gap-prod
```

We conclude that cartesian products satisfy the universal property of pullbacks.

```agda
  abstract
    universal-property-pullback-prod :
      {l : Level} →
      universal-property-pullback l
        ( const A unit star)
        ( const B unit star)
        ( cone-prod)
    universal-property-pullback-prod =
      universal-property-pullback-is-pullback
        ( const A unit star)
        ( const B unit star)
        ( cone-prod)
        ( is-pullback-prod)
```
