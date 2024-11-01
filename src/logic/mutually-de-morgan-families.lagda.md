# Mutually De Morgan families

```agda
module logic.mutually-de-morgan-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.double-negation
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions

open import logic.de-morgans-law

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

A family of types `P : A → 𝒰` is
{{#concept "mutually de morgan" Disambiguation="family of types" Agda=is-mutually-de-morgan-family}}

if the logical implication

```text
  ∃x, ¬(P x) ⇒ ¬ (∀x, P x)
```

has a converse.

## Definition

### Mutually De Morgan families

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2)
  where

  is-mutually-de-morgan-family : UU (l1 ⊔ l2)
  is-mutually-de-morgan-family =
    ¬ ((x : A) → P x) → exists-structure A (λ x → ¬ P x)

  is-prop-is-mutually-de-morgan-family : is-prop is-mutually-de-morgan-family
  is-prop-is-mutually-de-morgan-family =
    is-prop-function-type (is-prop-exists-structure A (λ x → ¬ P x))

  is-mutually-de-morgan-family-Prop : Prop (l1 ⊔ l2)
  is-mutually-de-morgan-family-Prop =
    ( is-mutually-de-morgan-family , is-prop-is-mutually-de-morgan-family)
```

## External links

- [De Morgan laws, in constructive mathematics](https://ncatlab.org/nlab/show/De+Morgan+laws#in_constructive_mathematics)
  at $n$Lab
