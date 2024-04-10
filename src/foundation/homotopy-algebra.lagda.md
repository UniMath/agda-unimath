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

### Second-order inverse laws for left whiskered homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x}
  where

  right-right-inv-htpy : (p : f ~ g) (q : g ~ h) → (p ∙h q) ∙h inv-htpy q ~ p
  right-right-inv-htpy p q =
    ( assoc-htpy p q (inv-htpy q)) ∙h
    ( ap-concat-htpy p (right-inv-htpy q)) ∙h
    ( right-unit-htpy)

  left-right-inv-htpy : (p : f ~ g) (q : f ~ g) → p ∙h (inv-htpy p ∙h q) ~ q
  left-right-inv-htpy p q =
    ( inv-htpy (assoc-htpy p (inv-htpy p) q)) ∙h
    ( ap-concat-htpy' q (right-inv-htpy p))

  right-left-inv-htpy : (p : f ~ g) (q : h ~ g) → (p ∙h inv-htpy q) ∙h q ~ p
  right-left-inv-htpy p q =
    ( assoc-htpy p (inv-htpy q) q) ∙h
    ( ap-concat-htpy p (left-inv-htpy q)) ∙h
    ( right-unit-htpy)

  left-left-inv-htpy : (p : f ~ g) (q : g ~ h) → inv-htpy p ∙h (p ∙h q) ~ q
  left-left-inv-htpy p q =
    ( inv-htpy (assoc-htpy (inv-htpy p) p q)) ∙h
    ( ap-concat-htpy' q (left-inv-htpy p))
```
