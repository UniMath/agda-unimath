# Reflexive premetric structures on types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module metric-spaces.reflexive-premetric-structures
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers funext univalence truncations

open import foundation.binary-relations funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.empty-types funext univalence truncations
open import foundation.equivalences funext
open import foundation.existential-quantification funext univalence truncations
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.negation funext
open import foundation.propositions funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import metric-spaces.premetric-structures funext univalence truncations
```

</details>

## Idea

A [premetric structure](metric-spaces.premetric-structures.md) is
{{#concept "reflexive" Disambiguation="premetric" Agda=is-reflexive-Premetric}}
if any element is indistinguishable from itself. I.e., a premetric structure is
reflexive if all positive rational numbers are upper bounds of the distance
between an element and itself.

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

### Indistinguishability in a reflexive premetric is reflexive

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
