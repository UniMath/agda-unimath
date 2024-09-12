# Symmetric premetric structures on types

```agda
module metric-spaces.symmetric-premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.premetric-structures
```

</details>

## Idea

A [premetric](metric-spaces.premetric-structures.md) is
{{#concept "symmetric" Disambiguation="premetric" agda=is-symmetric-Premetric}}
if `d`-neighborhoods are symmetric for all
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
`d`.

## Definitions

### The property of being a symmetric premetric structure

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-symmetric-prop-Premetric : Prop (l1 ⊔ l2)
  is-symmetric-prop-Premetric =
    Π-Prop ℚ⁺ (is-symmetric-prop-Relation-Prop ∘ B)

  is-symmetric-Premetric : UU (l1 ⊔ l2)
  is-symmetric-Premetric = type-Prop is-symmetric-prop-Premetric

  is-prop-is-symmetric-Premetric : is-prop is-symmetric-Premetric
  is-prop-is-symmetric-Premetric =
    is-prop-type-Prop is-symmetric-prop-Premetric
```

## Properties

### Indistiguishability in a symmetric premetric is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (S : is-symmetric-Premetric B)
  where

  is-symmetric-is-indistinguishable-is-symmetric-Premetric :
    is-symmetric (is-indistinguishable-Premetric B)
  is-symmetric-is-indistinguishable-is-symmetric-Premetric x y H d =
    S d x y (H d)
```

### Being separated in a symmetric premetric is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (S : is-symmetric-Premetric B)
  where

  is-symmetric-is-separated-pt-is-symmetric-Premetric :
    is-symmetric (is-separated-pt-Premetric B)
  is-symmetric-is-separated-pt-is-symmetric-Premetric x y =
    elim-exists
      ( is-separated-pt-prop-Premetric B y x)
      ( λ d I → intro-exists d (I ∘ S d y x))
```
