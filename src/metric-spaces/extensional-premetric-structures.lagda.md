# Extensional premetric structures on types

```agda
module metric-spaces.extensional-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.premetric-structures
open import metric-spaces.reflexive-premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) is
{{#concept "local" Disambiguation="premetric" agda=is-local-Premetric}} if
indistinguishability has propositional fibers.

A reflexive local premetric is called
{{#concept "extensional" Disambiguation="premetric on a type" Agda=is-extensional-Premetric}}.

Indistiguishability in an extensional premetric structure characterizes equality
in the carrier type. In particular, any type equipped with an extensional
premetric is a [set](foundation.sets.md).

## Definitions

### The property of being a local premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-local-prop-Premetric : Prop (l1 ⊔ l2)
  is-local-prop-Premetric =
    Π-Prop A (is-prop-Prop ∘ Σ A ∘ is-indistinguishable-Premetric B)

  is-local-Premetric : UU (l1 ⊔ l2)
  is-local-Premetric = type-Prop is-local-prop-Premetric

  is-prop-is-local-Premetric : is-prop is-local-Premetric
  is-prop-is-local-Premetric = is-prop-type-Prop is-local-prop-Premetric
```

### Tightness of a premetric structure

A premetric is
{{#concept "tight" Disambiguation="premetric" Agda=is-tight-Premetric}} if any
two indistinguishable elements are [equal](foundation-core.identity-types.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-tight-Premetric : UU (l1 ⊔ l2)
  is-tight-Premetric =
    (x y : A) → is-indistinguishable-Premetric B x y → x ＝ y
```

### The property of being an extensional premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-extensional-prop-Premetric : Prop (l1 ⊔ l2)
  is-extensional-prop-Premetric =
    product-Prop
      ( is-reflexive-prop-Premetric B)
      ( is-local-prop-Premetric B)

  is-extensional-Premetric : UU (l1 ⊔ l2)
  is-extensional-Premetric = type-Prop is-extensional-prop-Premetric

  is-prop-is-extensional-Premetric : is-prop is-extensional-Premetric
  is-prop-is-extensional-Premetric =
    is-prop-type-Prop is-extensional-prop-Premetric
```

## Properties

### Any tight premetric is local

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-tight-Premetric B)
  where

  is-local-is-tight-Premetric : is-local-Premetric B
  is-local-is-tight-Premetric x =
    is-prop-all-elements-equal
      ( λ (u , I) (v , J) →
        eq-type-subtype
          ( is-indistinguishable-prop-Premetric B x)
          ( inv (T x u I) ∙ T x v J))
```

### Characterization of equality in an extensional premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (E : is-extensional-Premetric B)
  where

  is-torsorial-indistinguishable-is-extensional-Premetric :
    (x : A) → is-torsorial (is-indistinguishable-Premetric B x)
  is-torsorial-indistinguishable-is-extensional-Premetric x =
    is-proof-irrelevant-is-prop (pr2 E x) (x , λ d → pr1 E d x)

  indistinguishable-eq-is-extensional-Premetric :
    {x y : A} → (x ＝ y) → is-indistinguishable-Premetric B x y
  indistinguishable-eq-is-extensional-Premetric =
    indistinguishable-eq-reflexive-Premetric B (pr1 E)

  is-fiberwise-equiv-indistinguishable-is-extensional-Premetric :
    (x y : A) → is-equiv (indistinguishable-eq-is-extensional-Premetric {x} {y})
  is-fiberwise-equiv-indistinguishable-is-extensional-Premetric x =
    fundamental-theorem-id
      ( is-torsorial-indistinguishable-is-extensional-Premetric x)
      ( λ y → indistinguishable-eq-reflexive-Premetric B (pr1 E))

  equiv-eq-is-indistinguishable-is-extensional-Premetric :
    {x y : A} → (x ＝ y) ≃ (is-indistinguishable-Premetric B x y)
  equiv-eq-is-indistinguishable-is-extensional-Premetric {x} {y} =
    ( indistinguishable-eq-reflexive-Premetric B (pr1 E)) ,
    ( is-fiberwise-equiv-indistinguishable-is-extensional-Premetric x y)

  eq-indistinguishable-is-extensional-Premetric :
    {x y : A} → (is-indistinguishable-Premetric B x y) → (x ＝ y)
  eq-indistinguishable-is-extensional-Premetric =
    map-inv-equiv equiv-eq-is-indistinguishable-is-extensional-Premetric
```

### Any extensional premetric is tight

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (E : is-extensional-Premetric B)
  where

  is-tight-is-extensional-Premetric : is-tight-Premetric B
  is-tight-is-extensional-Premetric x =
    ( map-inv-is-equiv) ∘
    ( is-fiberwise-equiv-indistinguishable-is-extensional-Premetric B E x)
```

### Any type equipped with an extensional premetric is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (E : is-extensional-Premetric B)
  where

  is-set-has-extensional-Premetric : is-set A
  is-set-has-extensional-Premetric x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-indistinguishable-is-extensional-Premetric
        ( B)
        ( E)
        ( x)
        ( y))
      ( is-prop-is-indistinguishable-Premetric B x y)
```
