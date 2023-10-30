# Codiscrete types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.codiscrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-equivalences
open import foundation.universe-levels

open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.higher-modalities
```

</details>

## Idea

A type is said to be **codiscrete** if it is
[sharp](modal-type-theory.sharp-modality.md) modal, i.e. if the sharp unit `η_♯`
is an [equivalence](foundation-core.equivalences.md) at that type.

We postulate that codiscrete types are closed under

- the formation of identity types
- the formation of dependent function types
- the formation of the subuniverse of codiscrete types.

Please note that there is some redundancy between the axioms that are assumed
here and in the files on
[the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), and the
file on the [sharp modality](modal-type-theory.sharp-modality.md), and they may
be subject to change in the future.

## Definition

```agda
is-codiscrete : {l : Level} (A : UU l) → UU l
is-codiscrete {l} A = is-equiv (unit-♯ {l} {A})

is-codiscrete-family :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-codiscrete-family {A = A} B = (x : A) → is-codiscrete (B x)

Codiscrete : (l : Level) → UU (lsuc l)
Codiscrete l = Σ (UU l) (is-codiscrete)
```

## Postulates

### The identity types of `♯` are codiscrete

```agda
postulate
  is-codiscrete-Id-♯ :
    {l1 : Level} {A : UU l1} (x y : ♯ A) → is-codiscrete (x ＝ y)

is-codiscrete-Id :
  {l1 : Level} {A : UU l1} (x y : A) → is-codiscrete A → is-codiscrete (x ＝ y)
is-codiscrete-Id x y is-codiscrete-A =
  map-tr-equiv
    ( is-codiscrete)
    ( inv-equiv-ap-is-emb (is-emb-is-equiv is-codiscrete-A))
    ( is-codiscrete-Id-♯ (unit-♯ x) (unit-♯ y))
```

### A `Π`-type is codiscrete if its codomain is

```agda
postulate
  is-codiscrete-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-codiscrete (B x)) →
    is-codiscrete ((x : A) → B x)
```

### The universe of codiscrete types is codiscrete

```agda
postulate
  is-codiscrete-Codiscrete : (l : Level) → is-codiscrete (Codiscrete l)
```

## Properties

### Being codiscrete is a property

```agda
module _
  {l : Level} (A : UU l)
  where

  is-codiscrete-Prop : Prop l
  is-codiscrete-Prop = is-equiv-Prop (unit-♯ {l} {A})

  is-property-is-codiscrete : is-prop (is-codiscrete A)
  is-property-is-codiscrete = is-prop-type-Prop is-codiscrete-Prop

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  is-codiscrete-family-Prop : Prop (l1 ⊔ l2)
  is-codiscrete-family-Prop = Π-Prop A (is-codiscrete-Prop ∘ B)

  is-property-is-codiscrete-family : is-prop (is-codiscrete-family B)
  is-property-is-codiscrete-family = is-prop-type-Prop is-codiscrete-family-Prop
```

### Codiscreteness is a higher modality

```agda
module _
  (l : Level)
  where

  is-higher-modality-♯ :
    is-higher-modality (♯-locally-small-operator-modality l) (unit-♯)
  pr1 is-higher-modality-♯ = induction-principle-♯
  pr2 is-higher-modality-♯ X = is-codiscrete-Id-♯

  ♯-higher-modality : higher-modality l l
  pr1 ♯-higher-modality = ♯-locally-small-operator-modality l
  pr1 (pr2 ♯-higher-modality) = unit-♯
  pr2 (pr2 ♯-higher-modality) = is-higher-modality-♯
```

### Types in the image of `♯` are codiscrete

```agda
is-codiscrete-♯ : {l : Level} (X : UU l) → is-codiscrete (♯ X)
is-codiscrete-♯ {l} =
  is-modal-operator-type-higher-modality (♯-higher-modality l)
```
