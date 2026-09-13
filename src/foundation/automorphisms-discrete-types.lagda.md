# Automorphisms on discrete types

```agda
module foundation.automorphisms-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphism-decompositions-isolated-elements
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.complements-elements-discrete-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.equivalences
open import foundation.equivalences-types-with-isolated-elements
open import foundation.full-subtypes
open import foundation.functoriality-cartesian-product-types
open import foundation.isolated-elements
open import foundation.universe-levels
```

</details>

## Idea

Given an element `a` of a [discrete type](foundation.discrete-types.md) `A`,
write `C` for the type `{x : A ∣ a ≠ x}`. Then there is an equivalence

```text
  Aut A ≃ Aut C × A.
```

This equivalence follows from a similar equivalence regarding
[automorphisms on types equipped with an isolated element](foundation.automorphism-decompositions-isolated-elements.md).

## Definitions

### The type of automorphisms on a discrete type

```agda
module _
  {l1 : Level} (A : Discrete-Type l1)
  where

  aut-Discrete-Type : UU l1
  aut-Discrete-Type = Aut (type-Discrete-Type A)
```

## Properties

### Computing the type of automorphisms on a discrete type

```agda
module _
  {l1 : Level} (A : Discrete-Type l1) (a : type-Discrete-Type A)
  where

  compute-aut-Discrete-Type :
    aut-Discrete-Type A ≃
    Aut (complement-element-Discrete-Type A a) × type-Discrete-Type A
  compute-aut-Discrete-Type =
    equiv-product
      ( compute-pointed-equiv-isolated-element
        ( a , has-decidable-equality-type-Discrete-Type A a)
        ( a , has-decidable-equality-type-Discrete-Type A a))
      ( equiv-inclusion-is-full-subtype
        ( is-isolated-Prop)
        ( has-decidable-equality-type-Discrete-Type A)) ∘e
    equiv-decomposition-aut-isolated-element
      ( a , has-decidable-equality-type-Discrete-Type A a)
```
