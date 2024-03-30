# Preidempotent maps

```agda
module foundation.preidempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.homotopy-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sets
```

</details>

## Idea

A {{#concept "preidempotent map" Agda=is-preidempotent-map}} is a map
`f : A → A` equipped with a homotopy `f ∘ f ~ f`.

## Definitions

```agda
is-preidempotent-map : {l : Level} {A : UU l} → (A → A) → UU l
is-preidempotent-map f = (f ∘ f) ~ f

preidempotent-map : {l : Level} (A : UU l) → UU l
preidempotent-map A = Σ (A → A) (is-preidempotent-map)
```

## Properties

### Being preidempotent over a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-is-preidempotent-map-is-set : is-prop (is-preidempotent-map f)
  is-prop-is-preidempotent-map-is-set =
    is-prop-Π (λ x → is-set-A (f (f x)) (f x))

  is-preidempotent-map-is-set-Prop : Prop l
  is-preidempotent-map-is-set-Prop =
    ( is-preidempotent-map f , is-prop-is-preidempotent-map-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-preidempotent-map-Set : is-prop (is-preidempotent-map f)
  is-prop-is-preidempotent-map-Set =
    is-prop-is-preidempotent-map-is-set (is-set-type-Set A) f

  is-preidempotent-map-prop-Set : Prop l
  is-preidempotent-map-prop-Set =
    ( is-preidempotent-map f , is-prop-is-preidempotent-map-Set)
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is preidempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  is-preidempotent-inclusion-retraction : is-preidempotent-map (i ∘ r)
  is-preidempotent-inclusion-retraction = i ·l H ·r r
```

### Preidempotence is preserved by homotopies

If a map `g` is homotopic to a preidempotent map `f`, then `g` is also
preidempotent.

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-preidempotent-map f)
  where

  is-preidempotent-map-htpy : g ~ f → is-preidempotent-map g
  is-preidempotent-map-htpy H =
    horizontal-concat-htpy H H ∙h F ∙h inv-htpy H

  is-preidempotent-map-inv-htpy : f ~ g → is-preidempotent-map g
  is-preidempotent-map-inv-htpy H =
    horizontal-concat-htpy (inv-htpy H) (inv-htpy H) ∙h F ∙h H
```

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
