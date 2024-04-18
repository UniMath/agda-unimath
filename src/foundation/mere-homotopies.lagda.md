# Mere homotopies

```agda
module foundation.mere-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels
```

<details>

## Idea

A {{#concept "mere homotopy" Agda=mere-htpy}} between two dependent functions `f g : (a : A) → B a` is an element of the [propositional truncation](foundation.propositional-truncations.md)

```text
  ║ f ~ g ║₋₁
```

of the type of [homotopies](foundation-core.homotopies.md) between `f` and `g`.

## Definitions

### Mere homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  mere-htpy-Prop : Prop (l1 ⊔ l2)
  mere-htpy-Prop = trunc-Prop (f ~ g)

  mere-htpy : UU (l1 ⊔ l2)
  mere-htpy = type-trunc-Prop (f ~ g)

  is-prop-mere-htpy : is-prop mere-htpy
  is-prop-mere-htpy = is-prop-type-trunc-Prop
```

## Properties

### Two functions are merely homotopic if and only if they are merely equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x)
  where

  mere-eq-mere-htpy : mere-htpy f g → mere-eq f g
  mere-eq-mere-htpy = map-trunc-Prop eq-htpy

  mere-htpy-mere-eq : mere-eq f g → mere-htpy f g
  mere-htpy-mere-eq = map-trunc-Prop htpy-eq

  equiv-mere-htpy-mere-eq : mere-eq f g ≃ mere-htpy f g
  equiv-mere-htpy-mere-eq = equiv-trunc-Prop equiv-funext
```
