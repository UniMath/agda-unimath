# Functoriality of truncations

```agda
module foundation.functoriality-truncation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.truncation-levels
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

The universal property of truncations can be used to define the functorial
action of truncations.

## Definition

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where

  unique-map-trunc :
    is-contr
      ( Σ ( type-trunc k A → type-trunc k B)
          ( coherence-square-maps f unit-trunc unit-trunc))
  unique-map-trunc =
    universal-property-trunc k A (trunc k B) (unit-trunc ∘ f)

  map-trunc : type-trunc k A → type-trunc k B
  map-trunc = pr1 (center unique-map-trunc)

  coherence-square-map-trunc :
    coherence-square-maps f unit-trunc unit-trunc map-trunc
  coherence-square-map-trunc = pr2 (center unique-map-trunc)
```

## Properties

### Truncations of homotopic maps are homotopic

```agda
naturality-unit-trunc :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
  ( (map-trunc k f) ∘ unit-trunc) ~ (unit-trunc ∘ f)
naturality-unit-trunc k f =
  pr2 (center (unique-map-trunc k f))

htpy-uniqueness-map-trunc :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (f : A → B) →
  ( h : type-trunc k A → type-trunc k B) →
  ( ( h ∘ unit-trunc) ~ (unit-trunc ∘ f)) →
  (map-trunc k f) ~ h
htpy-uniqueness-map-trunc k f h H =
  htpy-eq (ap pr1 (contraction (unique-map-trunc k f) (pair h H)))

htpy-trunc :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {k : 𝕋} {f g : A → B} →
  (f ~ g) → (map-trunc k f ~ map-trunc k g)
htpy-trunc {k = k} {f} {g} H =
  htpy-uniqueness-map-trunc
    ( k)
    ( f)
    ( map-trunc k g)
    ( naturality-unit-trunc k g ∙h
      inv-htpy (unit-trunc ·l H))
```

### The truncation of the identity map is the identity map

```agda
id-map-trunc :
  { l1 : Level} {A : UU l1} (k : 𝕋) → map-trunc k (id {A = A}) ~ id
id-map-trunc {l1} {A} k =
  htpy-uniqueness-map-trunc k id id refl-htpy
```

### The truncation of a composite is the composite of the truncations

```agda
preserves-comp-map-trunc :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (k : 𝕋)
  ( g : B → C) (f : A → B) →
  ( map-trunc k (g ∘ f)) ~
  ( (map-trunc k g) ∘ (map-trunc k f))
preserves-comp-map-trunc k g f =
  htpy-uniqueness-map-trunc k
    ( g ∘ f)
    ( (map-trunc k g) ∘ (map-trunc k f))
    ( ( (map-trunc k g) ·l (naturality-unit-trunc k f)) ∙h
      ( ( naturality-unit-trunc k g) ·r f))
```

### The functorial action of truncations preserves equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (k : 𝕋) (e : A ≃ B)
  where

  map-equiv-trunc : type-trunc k A → type-trunc k B
  map-equiv-trunc = map-trunc k (map-equiv e)

  map-inv-equiv-trunc : type-trunc k B → type-trunc k A
  map-inv-equiv-trunc = map-trunc k (map-inv-equiv e)

  is-equiv-map-equiv-trunc : is-equiv map-equiv-trunc
  is-equiv-map-equiv-trunc =
    pair
      ( pair
        ( map-inv-equiv-trunc)
        ( inv-htpy
          ( preserves-comp-map-trunc k (map-equiv e) (map-inv-equiv e)) ∙h
          ( htpy-trunc (is-section-map-inv-equiv e) ∙h
            id-map-trunc k)))
      ( pair
        ( map-inv-equiv-trunc)
        ( inv-htpy
          ( preserves-comp-map-trunc k (map-inv-equiv e) (map-equiv e)) ∙h
          ( htpy-trunc (is-retraction-map-inv-equiv e) ∙h
            id-map-trunc k)))

  equiv-trunc : (type-trunc k A ≃ type-trunc k B)
  pr1 equiv-trunc = map-equiv-trunc
  pr2 equiv-trunc = is-equiv-map-equiv-trunc
```
