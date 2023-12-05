# The action on homotopies of functions

```agda
module foundation.action-on-homotopies-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Applying the
[action on identifications](foundation.action-on-identifications-functions.md)
to [identifications](foundation-core.identity-types.md) arising from the
[function extensionality axiom](foundation.function-extensionality.md) gives us
the **action on homotopies**. For arbitrary functions of type

```text
  F : ((x : A) → B x) → C
```

we thus get an action of type

```text
  f ~ g → F f ＝ F g.
```

## Definition

### The functorial action of functions on homotopies

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  (F : ((x : A) → B x) → C)
  where

  abstract
    unique-action-htpy-function :
      (f : (x : A) → B x) →
      is-contr
        ( Σ ( (g : (x : A) → B x) → f ~ g → F f ＝ F g)
            ( λ α → α f refl-htpy ＝ refl))
    unique-action-htpy-function f =
      is-contr-map-ev-refl-htpy
        ( λ g α → F f ＝ F g)
        ( refl)

  action-htpy-function :
    {f g : (x : A) → B x} → f ~ g → (F f) ＝ (F g)
  action-htpy-function H = ap F (eq-htpy H)

  compute-action-htpy-function-refl-htpy :
    (f : (x : A) → B x) → action-htpy-function refl-htpy ＝ refl
  compute-action-htpy-function-refl-htpy f =
    ap (ap F) (eq-htpy-refl-htpy f)
```

## Properties

### The action on equivalences of a constant map is constant

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  {f g : (x : A) → B x}
  where

  compute-action-htpy-function-const :
    (c : C) (H : f ~ g) →
    action-htpy-function (const ((x : A) → B x) C c) H ＝ refl
  compute-action-htpy-function-const c H = ap-const c (eq-htpy H)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  (F : ((x : A) → B x) → C)
  {f g h : (x : A) → B x}
  where

  distributive-action-htpy-function-comp-htpy :
    (H : f ~ g) (H' : g ~ h) →
    action-htpy-function F (H ∙h H') ＝
    action-htpy-function F H ∙ action-htpy-function F H'
  distributive-action-htpy-function-comp-htpy H H' =
    ap (ap F) (eq-htpy-concat-htpy H H') ∙ ap-concat F (eq-htpy H) (eq-htpy H')
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-htpy-function-inv-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3}
  (F : ((x : A) → B x) → C) {f g : (x : A) → B x} (H : f ~ g) →
  action-htpy-function F (inv-htpy H) ＝ inv (action-htpy-function F H)
compute-action-htpy-function-inv-htpy F H =
  ( ap (ap F) (inv (eq-htpy-inv H))) ∙
  ( ap-inv F (eq-htpy H))
```
