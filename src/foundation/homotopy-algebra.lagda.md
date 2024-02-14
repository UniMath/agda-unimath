# Homotopy algebra

```agda
module foundation.homotopy-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopy-induction
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

This file has been created to collect operations on and facts about higher
[homotopies](foundation-core.homotopies.md). The scope of this file is analogous
to the scope of the file [path algebra](foundation.path-algebra.md), which is
about higher identifications.

## Definitions

### Horizontal concatenation of homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
  where

  horizontal-concat-htpy : f ~ f' → ({x : A} → g {x} ~ g' {x}) → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy F G = (g ·l F) ∙h (G ·r f')

  horizontal-concat-htpy' :
    f ~ f' → ({x : A} → g {x} ~ g' {x}) → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy' F G = (G ·r f) ∙h (g' ·l F)
```

## Properties

### The two definitions of horizontal concatenation of homotopies agree

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  coh-left-unit-horizontal-concat-htpy :
    {f : (x : A) → B x} {g g' : {x : A} → B x → C x}
    (G : {x : A} → g {x} ~ g' {x}) →
    horizontal-concat-htpy (refl-htpy' f) G ~
    horizontal-concat-htpy' (refl-htpy' f) G
  coh-left-unit-horizontal-concat-htpy G = inv-htpy-right-unit-htpy

  coh-right-unit-horizontal-concat-htpy :
    {f f' : (x : A) → B x} {g : {x : A} → B x → C x}
    (F : f ~ f') →
    horizontal-concat-htpy F (refl-htpy' g) ~
    horizontal-concat-htpy' F (refl-htpy' g)
  coh-right-unit-horizontal-concat-htpy F = right-unit-htpy

  coh-horizontal-concat-htpy :
    {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
    (F : f ~ f') (G : {x : A} → g {x} ~ g' {x}) →
    horizontal-concat-htpy F G ~ horizontal-concat-htpy' F G
  coh-horizontal-concat-htpy {f} F G =
    ind-htpy f
      ( λ f' F → horizontal-concat-htpy F G ~ horizontal-concat-htpy' F G)
      ( coh-left-unit-horizontal-concat-htpy G)
      ( F)
```
