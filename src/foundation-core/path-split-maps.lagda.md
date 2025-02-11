# Path-split maps

```agda
module foundation-core.path-split-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.sections
```

</details>

## Idea

A map `f : A → B` is said to be {{#concept "path split" Agda=is-path-split}} if
it has a [section](foundation-core.sections.md) and its
[action on identifications](foundation.action-on-identifications-functions.md)
`x ＝ y → f x ＝ f y` has a section for each `x y : A`. By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
it follows that a map is path-split if and only if it is an
[equivalence](foundation-core.equivalences.md).

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-path-split : UU (l1 ⊔ l2)
  is-path-split = section f × ((x y : A) → section (ap f {x = x} {y = y}))
```

## Properties

### A map is path-split if and only if it is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-path-split-is-equiv : is-equiv f → is-path-split f
    pr1 (is-path-split-is-equiv is-equiv-f) = pr1 is-equiv-f
    pr2 (is-path-split-is-equiv is-equiv-f) x y =
      pr1 (is-emb-is-equiv is-equiv-f x y)

  abstract
    is-coherently-invertible-is-path-split :
      is-path-split f → is-coherently-invertible f
    pr1 (is-coherently-invertible-is-path-split ((g , G) , s)) =
      g
    pr1 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s))) =
      G
    pr1 (pr2 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s)))) x =
      pr1 (s (g (f x)) x) (G (f x))
    pr2 (pr2 (pr2 (is-coherently-invertible-is-path-split ((g , G) , s)))) x =
      inv (pr2 (s (g (f x)) x) (G (f x)))

  abstract
    is-equiv-is-path-split : is-path-split f → is-equiv f
    is-equiv-is-path-split =
      is-equiv-is-coherently-invertible ∘
      is-coherently-invertible-is-path-split
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).

## References

{{#bibliography}} {{#reference UF13}} {{#reference Shu14UniversalProperties}}
