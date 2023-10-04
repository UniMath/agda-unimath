# Sections of maps of maps

```agda
module foundation.sections-of-maps-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.sections
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A **section of a map of maps** is a map of maps that is a right inverse. Thus,
`s : (((y : C) → D y) → (x : A) → B x` is a section of
`f : ((x : A) → B x) → (y : C) → D y` if the composition `f ∘ s` is homotopic to
the identity at `D y` in both variables.

Sections of maps of maps are equivalent to usual
[sections](foundation-core.sections.md), but we record this definition
separately so we can circumvent applying
[function extensionality](foundation-core.function-extensionality.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : ((x : A) → B x) → (y : C) → D y)
  where

  section-Π : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  section-Π =
    Σ (((y : C) → D y) → (x : A) → B x) (λ s → binary-htpy (f ∘ s) id)

  map-section-Π : section-Π → ((y : C) → D y) → (x : A) → B x
  map-section-Π = pr1

  is-section-Π-map-section-Π :
    (s : section-Π) → binary-htpy (f ∘ map-section-Π s) id
  is-section-Π-map-section-Π = pr2
```

## Properties

### Section of maps of maps is equivalent to sections

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : ((x : A) → B x) → (y : C) → D y)
  where

  equiv-section-section-Π : section-Π f ≃ section f
  equiv-section-section-Π = equiv-tot (λ s → equiv-htpy-binary-htpy (f ∘ s) id)

  section-section-Π : section-Π f → section f
  section-section-Π = map-equiv equiv-section-section-Π

  section-Π-section : section f → section-Π f
  section-Π-section = map-inv-equiv equiv-section-section-Π
```
