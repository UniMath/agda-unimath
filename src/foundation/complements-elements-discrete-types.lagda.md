# Complements of elements of discrete types

```agda
module foundation.complements-elements-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Consider an element `a` in a [discrete type](foundation.discrete-types.md) `A`.
The
{{#concept "complement" Disambiguation="of an element" Agda=complement-element-Discrete-Type}}
is the type

```text
  {x : A ∣ a ≠ x}.
```

## Definitions

### The complement of an element

```agda
module _
  {l1 : Level} (A : Discrete-Type l1) (a : type-Discrete-Type A)
  where

  is-in-complement-element-Discrete-Type :
    type-Discrete-Type A → UU l1
  is-in-complement-element-Discrete-Type x =
    a ≠ x

  is-prop-is-in-complement-element-Discrete-Type :
    (x : type-Discrete-Type A) →
    is-prop (is-in-complement-element-Discrete-Type x)
  is-prop-is-in-complement-element-Discrete-Type x =
    is-prop-neg

  is-in-complement-element-prop-Discrete-Type :
    subtype l1 (type-Discrete-Type A)
  pr1 (is-in-complement-element-prop-Discrete-Type x) =
    is-in-complement-element-Discrete-Type x
  pr2 (is-in-complement-element-prop-Discrete-Type x) =
    is-prop-is-in-complement-element-Discrete-Type x

  complement-element-Discrete-Type :
    UU l1
  complement-element-Discrete-Type =
    type-subtype is-in-complement-element-prop-Discrete-Type
```
