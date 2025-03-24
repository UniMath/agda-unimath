# The action on homotopies of functions

```agda
open import foundation.function-extensionality-axiom

module foundation.action-on-homotopies-functions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions funext
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext
open import foundation.homotopy-induction funext
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Applying the
[action on identifications](foundation.action-on-identifications-functions.md)
to [identifications](foundation-core.identity-types.md) arising from the
[function extensionality axiom](foundation.function-extensionality.md) gives us
the
{{#concept "action on homotopies" Disambiguation="functions" Agda=action-htpy-function}}.
For arbitrary functions of type

```text
  F : ((x : A) → B x) → C.
```

We thus get an action of type

```text
  f ~ g → F f ＝ F g.
```

## Definition

### The unique functorial action of functions on homotopies

There is a unique action of functions on homotopies. Namely, by
[homotopy induction](foundation.homotopy-induction.md), function homotopies
satisfy
[the dependent universal property of being an identity system](foundation.universal-property-identity-systems.md)
on (dependent) function types. This means that for every type family

```text
  C : (g : (x : A) → B x) → f ~ g → 𝒰
```

the map `ev-refl-htpy C` is an equivalence
[equivalence](foundation-core.equivalences.md)

```text
  ev-refl-htpy C : ((g : (x : A) → B x) (H : f ~ g) → C g H) ≃ (C f refl-htpy).
```

In particular, applying this to type families of the form

```text
  g H ↦ F f ＝ F g
```

with the mapping

```text
  f refl-htpy ↦ refl
```

shows that our action on homotopies is
[unique](foundation-core.contractible-types.md).

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
      is-contr-map-ev-refl-htpy (λ g _ → F f ＝ F g) refl

  action-htpy-function :
    {f g : (x : A) → B x} → f ~ g → F f ＝ F g
  action-htpy-function H = ap F (eq-htpy H)

  compute-action-htpy-function-refl-htpy :
    (f : (x : A) → B x) → action-htpy-function refl-htpy ＝ refl
  compute-action-htpy-function-refl-htpy f =
    ap² F (eq-htpy-refl-htpy f)
```

## Properties

### The action on homotopies preserves concatenation

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  (F : ((x : A) → B x) → C)
  {f g h : (x : A) → B x}
  where

  distributive-action-htpy-function-concat-htpy :
    (H : f ~ g) (H' : g ~ h) →
    action-htpy-function F (H ∙h H') ＝
    action-htpy-function F H ∙ action-htpy-function F H'
  distributive-action-htpy-function-concat-htpy H H' =
    ap² F (eq-htpy-concat-htpy H H') ∙ ap-concat F (eq-htpy H) (eq-htpy H')
```

### The action on homotopies preserves inverses

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1} {B : A → UU l2} {C : UU l3}
  (F : ((x : A) → B x) → C)
  {f g : (x : A) → B x}
  where

  compute-action-htpy-function-inv-htpy :
    (H : f ~ g) →
    action-htpy-function F (inv-htpy H) ＝ inv (action-htpy-function F H)
  compute-action-htpy-function-inv-htpy H =
    ap² F (compute-inv-eq-htpy H) ∙ ap-inv F (eq-htpy H)
```
