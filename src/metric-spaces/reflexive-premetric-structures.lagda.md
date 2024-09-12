# Reflexive premetric structures on types

```agda
module metric-spaces.reflexive-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric structure](metric-spaces.premetric-structures.md) is
{{#concept "reflexive" Disambiguation="premetric" Agda=is-reflexive-Premetric}}
if any element is indistinguishable from itself.

## Definitions

### The property of being a reflexive premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-reflexive-prop-Premetric : Prop (l1 ⊔ l2)
  is-reflexive-prop-Premetric =
    Π-Prop ℚ⁺ (is-reflexive-prop-Relation-Prop ∘ B)

  is-reflexive-Premetric : UU (l1 ⊔ l2)
  is-reflexive-Premetric = type-Prop is-reflexive-prop-Premetric

  is-prop-is-reflexive-Premetric : is-prop is-reflexive-Premetric
  is-prop-is-reflexive-Premetric =
    is-prop-type-Prop is-reflexive-prop-Premetric
```

## Properties

### Indistiguishability in a reflexive premetric is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B)
  where

  is-reflexive-is-indistinguishable-reflexive-Premetric :
    is-reflexive (is-indistinguishable-Premetric B)
  is-reflexive-is-indistinguishable-reflexive-Premetric x d = R d x
```

### In a reflexive premetric, equal elements are indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (H : is-reflexive-Premetric B)
  where

  indistinguishable-eq-reflexive-Premetric :
    {x y : A} → x ＝ y → is-indistinguishable-Premetric B x y
  indistinguishable-eq-reflexive-Premetric {x} {.x} refl d = H d x
```

### Being separated in a reflexive premetric is irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B)
  where

  is-irreflexive-is-separated-pt-is-reflexive-Premetric :
    (x : A) → ¬ (is-separated-pt-Premetric B x x)
  is-irreflexive-is-separated-pt-is-reflexive-Premetric x =
    elim-exists
      ( empty-Prop)
      ( λ d H → H (R d x))
```
