# Idempotent maps

```agda
module foundation.idempotent-maps where
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

An {{#concept "idempotent map" Agda=is-idempotent-map}} is a map `f : A → A`
[equipped](foundation.structure.md) with a
[homotopy](foundation-core.homotopies.md) `f ∘ f ~ f`.

## Definitions

### The structure on a map of idempotence

```agda
is-idempotent-map : {l : Level} {A : UU l} → (A → A) → UU l
is-idempotent-map f = f ∘ f ~ f
```

### The type of idempotent maps

```agda
idempotent-map : {l : Level} (A : UU l) → UU l
idempotent-map A = Σ (A → A) (is-idempotent-map)

module _
  {l : Level} {A : UU l} (f : idempotent-map A)
  where

  map-idempotent-map : A → A
  map-idempotent-map = pr1 f

  is-idempotent-idempotent-map :
    is-idempotent-map map-idempotent-map
  is-idempotent-idempotent-map = pr2 f
```

## Properties

### Being idempotent over a set is a property

```agda
module _
  {l : Level} {A : UU l} (is-set-A : is-set A) (f : A → A)
  where

  is-prop-is-idempotent-map-is-set : is-prop (is-idempotent-map f)
  is-prop-is-idempotent-map-is-set =
    is-prop-Π (λ x → is-set-A (f (f x)) (f x))

  is-idempotent-map-is-set-Prop : Prop l
  is-idempotent-map-is-set-Prop =
    ( is-idempotent-map f , is-prop-is-idempotent-map-is-set)

module _
  {l : Level} (A : Set l) (f : type-Set A → type-Set A)
  where

  is-prop-is-idempotent-map-Set : is-prop (is-idempotent-map f)
  is-prop-is-idempotent-map-Set =
    is-prop-is-idempotent-map-is-set (is-set-type-Set A) f

  is-idempotent-map-prop-Set : Prop l
  is-idempotent-map-prop-Set =
    ( is-idempotent-map f , is-prop-is-idempotent-map-Set)
```

### If `i` and `r` is an inclusion-retraction pair, then `i ∘ r` is idempotent

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (i : B → A) (r : A → B) (H : is-retraction i r)
  where

  is-idempotent-inclusion-retraction : is-idempotent-map (i ∘ r)
  is-idempotent-inclusion-retraction = i ·l H ·r r
```

### Idempotence is preserved by homotopies

If a map `g` is homotopic to a idempotent map `f`, then `g` is also idempotent.

```agda
module _
  {l : Level} {A : UU l} {f g : A → A} (F : is-idempotent-map f)
  where

  is-idempotent-map-htpy : g ~ f → is-idempotent-map g
  is-idempotent-map-htpy H =
    horizontal-concat-htpy H H ∙h F ∙h inv-htpy H

  is-idempotent-map-inv-htpy : f ~ g → is-idempotent-map g
  is-idempotent-map-inv-htpy H =
    horizontal-concat-htpy (inv-htpy H) (inv-htpy H) ∙h F ∙h H
```

## See also

- [Quasiidempotent maps](foundation.quasiidempotent-maps.md)
- [Split idempotent maps](foundation.split-idempotent-maps.md)

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
