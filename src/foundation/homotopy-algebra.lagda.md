# Homotopy algebra

```agda
module foundation.homotopy-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-homotopies-concatenation
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

  horizontal-concat-htpy : ({x : A} → g {x} ~ g' {x}) → f ~ f' → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy G F = (g ·l F) ∙h (G ·r f')

  horizontal-concat-htpy' :
    ({x : A} → g {x} ~ g' {x}) → f ~ f' → g ∘ f ~ g' ∘ f'
  horizontal-concat-htpy' G F = (G ·r f) ∙h (g' ·l F)
```

## Properties

### The two definitions of horizontal concatenation of homotopies agree

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  coh-right-unit-horizontal-concat-htpy :
    {f : (x : A) → B x} {g g' : {x : A} → B x → C x}
    (G : {x : A} → g {x} ~ g' {x}) →
    horizontal-concat-htpy G (refl-htpy' f) ~
    horizontal-concat-htpy' G (refl-htpy' f)
  coh-right-unit-horizontal-concat-htpy G = inv-htpy-right-unit-htpy

  coh-left-unit-horizontal-concat-htpy :
    {f f' : (x : A) → B x} {g : {x : A} → B x → C x}
    (F : f ~ f') →
    horizontal-concat-htpy (refl-htpy' g) F ~
    horizontal-concat-htpy' (refl-htpy' g) F
  coh-left-unit-horizontal-concat-htpy F = right-unit-htpy
```

For the general case, we must construct a coherence of the square

```text
            g ·r F
        gf -------> gf'
         |          |
  G ·r f |          | G ·r f'
         ∨          ∨
       g'f ------> g'f'
           g' ·r F
```

but this is an instance of naturality of `G` applied to `F`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f f' : (x : A) → B x} {g g' : {x : A} → B x → C x}
  (G : {x : A} → g {x} ~ g' {x}) (F : f ~ f')
  where

  coh-horizontal-concat-htpy :
    horizontal-concat-htpy' G F ~ horizontal-concat-htpy G F
  coh-horizontal-concat-htpy = nat-htpy G ·r F
```

### Eckmann-Hilton for homotopies

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {Z : UU l3}
  {f g : X → Y} {f' g' : Y → Z}
  where

  commutative-right-whisker-left-whisker-htpy :
    (H' : f' ~ g') (H : f ~ g) →
    (H' ·r f) ∙h (g' ·l H) ~
    (f' ·l H) ∙h (H' ·r g)
  commutative-right-whisker-left-whisker-htpy H' H x =
      coh-horizontal-concat-htpy H' H x

module _
  {l : Level} {X : UU l}
  where

  eckmann-hilton-htpy :
    (H K : id {A = X} ~ id) →
    (H ∙h K) ~ (K ∙h H)
  eckmann-hilton-htpy H K =
    ( inv-htpy
      ( left-whisker-concat-htpy H (left-unit-law-left-whisker-comp K))) ∙h
    ( commutative-right-whisker-left-whisker-htpy H K) ∙h
    ( right-whisker-concat-htpy (left-unit-law-left-whisker-comp K) H)
```
