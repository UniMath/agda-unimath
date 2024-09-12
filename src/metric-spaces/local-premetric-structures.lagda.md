# Local premetric structures on types

```agda
module metric-spaces.local-premetric-structures where
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

A premetric is {{#concept "tight" Disambiguation="premetric" Agda=is-tight-Premetric}} if any two indistinguishable elements are [equal](foundation-core.identity-types.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-tight-Premetric : UU (l1 ⊔ l2)
  is-tight-Premetric =
    (x y : A) → is-indistinguishable-Premetric B x y → x ＝ y
```

## Properties

### Characterization of equality in a local reflexive premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B) (x : A)
  where

  is-torsorial-indistinguishable-local-reflexive-Premetric :
    is-torsorial (is-indistinguishable-Premetric B x)
  is-torsorial-indistinguishable-local-reflexive-Premetric =
    is-proof-irrelevant-is-prop (L x) (x , λ d → R d x)

  is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric :
    (y : A) → is-equiv (indistinguishable-eq-reflexive-Premetric B R)
  is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric =
    fundamental-theorem-id
      ( is-torsorial-indistinguishable-local-reflexive-Premetric)
      ( λ y → indistinguishable-eq-reflexive-Premetric B R {x} {y})
```

### Any type equipped with a reflexive local premetric is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B)
  where

  is-set-has-local-reflexive-Premetric : is-set A
  is-set-has-local-reflexive-Premetric x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric
        B
        R
        L
        x
        y)
      ( is-prop-is-indistinguishable-Premetric B x y)
```

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

### Any reflexive local premetric is tight

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B)
  where

  is-tight-is-local-reflexive-Premetric : is-tight-Premetric B
  is-tight-is-local-reflexive-Premetric x =
    ( map-inv-is-equiv) ∘
    ( is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric B R L x)
```
