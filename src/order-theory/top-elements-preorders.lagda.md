# Top elements in preorders

```agda
module order-theory.top-elements-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.preorders
```

</details>

## Idea

A
{{#concept "largest element" Disambiguation="in a preorder" WD="maximal and minimal elements" WDID=Q1475294 Agda=is-top-element-Preorder}}
in a [preorder](order-theory.preorders.md) `P` is an element `t` such that
`x ≤ t` holds for every `x : P`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Preorder l1 l2)
  where

  is-top-element-prop-Preorder : type-Preorder X → Prop (l1 ⊔ l2)
  is-top-element-prop-Preorder x =
    Π-Prop (type-Preorder X) (λ y → leq-Preorder-Prop X y x)

  is-top-element-Preorder : type-Preorder X → UU (l1 ⊔ l2)
  is-top-element-Preorder x = type-Prop (is-top-element-prop-Preorder x)

  is-prop-is-top-element-Preorder :
    (x : type-Preorder X) → is-prop (is-top-element-Preorder x)
  is-prop-is-top-element-Preorder x =
    is-prop-type-Prop (is-top-element-prop-Preorder x)

  has-top-element-Preorder : UU (l1 ⊔ l2)
  has-top-element-Preorder = Σ (type-Preorder X) is-top-element-Preorder
```

## External links

- [Maximal and minimal elements](https://en.wikipedia.org/wiki/Maximal_and_minimal_elements)
  at Wikipedia
- [maximal element](https://ncatlab.org/nlab/show/maximal+element) at $n$Lab
