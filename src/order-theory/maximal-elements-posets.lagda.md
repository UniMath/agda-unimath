# Maximal elements in posets

```agda
module order-theory.maximal-elements-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions

open import order-theory.posets
```

</details>

## Idea

A
{{#concept "maximal" Disambiguation="element in a poset" WD="maximal and minimal elements" WDID=Q1475294 Agda=is-maximal-element-Poset}}
element in a [poset](order-theory.posets.md) is an element `y` such that every
other element `x` that is greater than it `y ≤ x` is
[equal](foundation-core.identity-types.md) to it `y = x`.

## Definition

```agda
module _
  {l1 l2 : Level} (X : Poset l1 l2)
  where

  is-maximal-element-prop-Poset : type-Poset X → Prop (l1 ⊔ l2)
  is-maximal-element-prop-Poset x =
    Π-Prop
      ( type-Poset X)
      ( λ y → function-Prop (leq-Poset X x y) (y ＝ x , is-set-type-Poset X y x))

  is-maximal-element-Poset : type-Poset X → UU (l1 ⊔ l2)
  is-maximal-element-Poset x = type-Prop (is-maximal-element-prop-Poset x)

  is-prop-is-maximal-element-Poset :
    (x : type-Poset X) → is-prop (is-maximal-element-Poset x)
  is-prop-is-maximal-element-Poset x =
    is-prop-type-Prop (is-maximal-element-prop-Poset x)
```

## External links

- [Maximal and minimal elements](https://en.wikipedia.org/wiki/Maximal_and_minimal_elements)
  at Wikipedia
- [maximal element](https://ncatlab.org/nlab/show/maximal+element) at $n$Lab
