# Discrete types

```agda
module foundation-core.discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.identity-types
open import foundation-core.sets
```

</details>

## Idea

A {{#concept "discrete type" Agda=Discrete-Type}} is a type that has
[decidable equality](foundation.decidable-equality.md). Consequently, discrete
types are [sets](foundation-core.sets.md) by Hedberg's theorem.

## Definition

```agda
Discrete-Type : (l : Level) → UU (lsuc l)
Discrete-Type l = Σ (UU l) has-decidable-equality

module _
  {l : Level} (X : Discrete-Type l)
  where

  type-Discrete-Type : UU l
  type-Discrete-Type = pr1 X

  has-decidable-equality-type-Discrete-Type :
    has-decidable-equality type-Discrete-Type
  has-decidable-equality-type-Discrete-Type = pr2 X

  is-set-type-Discrete-Type : is-set type-Discrete-Type
  is-set-type-Discrete-Type =
    is-set-has-decidable-equality has-decidable-equality-type-Discrete-Type

  set-Discrete-Type : Set l
  pr1 set-Discrete-Type = type-Discrete-Type
  pr2 set-Discrete-Type = is-set-type-Discrete-Type

  Id-Decidable-Prop :
    (x y : type-Discrete-Type) → Decidable-Prop l
  Id-Decidable-Prop x y =
    ( x ＝ y ,
      is-set-type-Discrete-Type x y ,
      has-decidable-equality-type-Discrete-Type x y)
```

## External links

- [classical set](https://ncatlab.org/nlab/show/classical+set) at $n$Lab
- [decidable object](https://ncatlab.org/nlab/show/decidable+object) at $n$Lab
