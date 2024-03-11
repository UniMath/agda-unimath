# Pointed retractions of pointed maps

```agda
module structured-types.pointed-retractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.retractions

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

A
{{#concept "pointed retraction" Disambiguation="pointed map" Agda=pointed-retraction}}
of a [pointed map](structured-types.pointed-maps.md) `f : A →∗ B` consists of a
pointed map `g : B →∗ A` equipped with a
[pointed homotopy](structured-types.pointed-homotopies.md) `H : g ∘∗ f ~∗ id`.

## Definitions

### The predicate of being a pointed retraction of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  is-pointed-retraction : (B →∗ A) → UU l1
  is-pointed-retraction g = g ∘∗ f ~∗ id-pointed-map
```

### The type of pointed retractions of a pointed map

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  where

  pointed-retraction : UU (l1 ⊔ l2)
  pointed-retraction =
    Σ (B →∗ A) (is-pointed-retraction f)

  module _
    (r : pointed-retraction)
    where

    pointed-map-pointed-retraction : B →∗ A
    pointed-map-pointed-retraction = pr1 r

    is-pointed-retraction-pointed-retraction :
      is-pointed-retraction f pointed-map-pointed-retraction
    is-pointed-retraction-pointed-retraction = pr2 r

    map-pointed-retraction : type-Pointed-Type B → type-Pointed-Type A
    map-pointed-retraction = map-pointed-map pointed-map-pointed-retraction

    preserves-point-pointed-map-pointed-retraction :
      map-pointed-retraction (point-Pointed-Type B) ＝ point-Pointed-Type A
    preserves-point-pointed-map-pointed-retraction =
      preserves-point-pointed-map pointed-map-pointed-retraction

    is-retraction-pointed-retraction :
      is-retraction (map-pointed-map f) map-pointed-retraction
    is-retraction-pointed-retraction =
      htpy-pointed-htpy is-pointed-retraction-pointed-retraction

    retraction-pointed-retraction : retraction (map-pointed-map f)
    pr1 retraction-pointed-retraction = map-pointed-retraction
    pr2 retraction-pointed-retraction = is-retraction-pointed-retraction

    coherence-point-is-retraction-pointed-retraction :
      coherence-point-unpointed-htpy-pointed-Π
        ( pointed-map-pointed-retraction ∘∗ f)
        ( id-pointed-map)
        ( is-retraction-pointed-retraction)
    coherence-point-is-retraction-pointed-retraction =
      coherence-point-pointed-htpy is-pointed-retraction-pointed-retraction
```

## Properties

### Any retraction of a pointed map preserves the base point in a unique way making the retracting homotopy pointed

Consider a [retraction](foundation-core.retractions.md) `g : B → A` of a pointed
map `f := (f₀ , f₁) : A →∗ B`. Then `g` is base point preserving.

**Proof.** Our goal is to show that `g * ＝ *`. Since `f` is pointed, we have
`f * ＝ *` and hence

```text
       (ap g f₁)⁻¹              H *
  g * -------------> g (f₀ *) -------> *.
```

In order to show that the retracting homotopy `H : g ∘ f₀ ~ id` is pointed, we
have to show that the triangle of identifications

```text
                                   H *
                         g (f₀ *) -----> *
                                \       /
  ap g f₁ ∙ ((ap g f₁)⁻¹ ∙ H *)  \     / refl
                                  \   /
                                   ∨ ∨
                                    *
```

commutes. This follows by the fact that concatenating with an inverse
identification is inverse to concatenating with the original identification, and
the right unit law of concatenation.

Note that the pointing of `g` chosen above is the unique way making the
retracting homotopy pointed, because the map `p ↦ ap g f₁ ∙ p` is an equivalence
with a contractible fiber at `H * ∙ refl`.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2} (f : A →∗ B)
  (g : type-Pointed-Type B → type-Pointed-Type A)
  (H : is-retraction (map-pointed-map f) g)
  where

  abstract
    uniquely-preserves-point-is-retraction-pointed-map :
      is-contr
        ( Σ ( g (point-Pointed-Type B) ＝ point-Pointed-Type A)
            ( coherence-square-identifications
              ( H (point-Pointed-Type A))
              ( ap g (preserves-point-pointed-map f))
              ( refl)))
    uniquely-preserves-point-is-retraction-pointed-map =
      is-contr-map-is-equiv
        ( is-equiv-concat (ap g (preserves-point-pointed-map f)) _)
        ( H (point-Pointed-Type A) ∙ refl)

  preserves-point-is-retraction-pointed-map :
    g (point-Pointed-Type B) ＝ point-Pointed-Type A
  preserves-point-is-retraction-pointed-map =
    inv (ap g (preserves-point-pointed-map f)) ∙ H (point-Pointed-Type A)

  pointed-map-is-retraction-pointed-map :
    B →∗ A
  pr1 pointed-map-is-retraction-pointed-map = g
  pr2 pointed-map-is-retraction-pointed-map =
    preserves-point-is-retraction-pointed-map

  coherence-point-is-retraction-pointed-map :
    coherence-point-unpointed-htpy-pointed-Π
      ( pointed-map-is-retraction-pointed-map ∘∗ f)
      ( id-pointed-map)
      ( H)
  coherence-point-is-retraction-pointed-map =
    ( is-section-inv-concat (ap g (preserves-point-pointed-map f)) _) ∙
    ( inv right-unit)

  is-pointed-retraction-is-retraction-pointed-map :
    is-pointed-retraction f pointed-map-is-retraction-pointed-map
  pr1 is-pointed-retraction-is-retraction-pointed-map =
    H
  pr2 is-pointed-retraction-is-retraction-pointed-map =
    coherence-point-is-retraction-pointed-map
```
