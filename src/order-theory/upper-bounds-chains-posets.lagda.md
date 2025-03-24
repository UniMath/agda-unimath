# Upper bounds of chains in posets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module order-theory.upper-bounds-chains-posets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification funext univalence truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions

open import order-theory.chains-posets funext univalence truncations
open import order-theory.posets funext univalence truncations
open import order-theory.upper-bounds-posets funext univalence truncations
```

</details>

## Idea

An
{{#concept "upper bound" Disambiguation="on a chain in a poset" Agda=is-upper-bound-chain-Poset}}
on a [chain](order-theory.chains-posets.md) `C` in a
[poset](order-theory.posets.md) `P` is an element `x` such that for every
element `y` in `C`, `y ≤ x` holds.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (X : Poset l1 l2) (C : chain-Poset l3 X)
  where

  is-upper-bound-chain-prop-Poset : type-Poset X → Prop (l1 ⊔ l2 ⊔ l3)
  is-upper-bound-chain-prop-Poset =
    is-upper-bound-family-of-elements-prop-Poset X
      ( inclusion-type-chain-Poset X C)

  is-upper-bound-chain-Poset : type-Poset X → UU (l1 ⊔ l2 ⊔ l3)
  is-upper-bound-chain-Poset = type-Prop ∘ is-upper-bound-chain-prop-Poset

  has-upper-bound-chain-prop-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  has-upper-bound-chain-prop-Poset =
    ∃ (type-Poset X) is-upper-bound-chain-prop-Poset

  has-upper-bound-chain-Poset : UU (l1 ⊔ l2 ⊔ l3)
  has-upper-bound-chain-Poset = type-Prop has-upper-bound-chain-prop-Poset
```
