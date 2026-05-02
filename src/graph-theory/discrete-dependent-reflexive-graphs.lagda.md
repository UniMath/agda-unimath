# Discrete dependent reflexive graphs

```agda
module graph-theory.discrete-dependent-reflexive-graphs where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions
open import foundation.propositions
open import foundation.universe-levels

open import graph-theory.dependent-reflexive-graphs
open import graph-theory.discrete-reflexive-graphs
open import graph-theory.reflexive-graphs
```

</details>

## Idea

A [dependent reflexive graph](graph-theory.dependent-reflexive-graphs.md) `H`
over a [reflexive graph](graph-theory.reflexive-graphs.md) is said to be
{{#concept "discrete" Disambiguation="dependent reflexive graph" Agda=is-discrete-Dependent-Reflexive-Graph}}
if the dependent edge relation

```text
  H₁ (refl G x) y : H₀ x → Type
```

is [torsorial](foundation-core.torsorial-type-families.md) for every element
`y : H₀ x`. That is, the dependent reflexive graph `H` is discrete precisely
when the reflexive graph

```text
  ev-point H x
```

is [discrete](graph-theory.discrete-reflexive-graphs.md) for every vertex
`x : G₀`. Furthermore, a dependent reflexive graph is discrete precisely when
the dependent edge relation

```text
  H₁ e y : H₀ x' → Type
```

is torsorial for every edge `e : G₁ x x'` and every element `y : H₀ x`.

## Definitions

### The predicate of being a discrete dependent reflexive graph

```agda
module _
  {l1 l2 l3 l4 : Level} {G : Reflexive-Graph l1 l2}
  (H : Dependent-Reflexive-Graph l3 l4 G)
  where

  is-discrete-prop-Dependent-Reflexive-Graph : Prop (l1 ⊔ l3 ⊔ l4)
  is-discrete-prop-Dependent-Reflexive-Graph =
    Π-Prop
      ( vertex-Reflexive-Graph G)
      ( λ x →
        is-discrete-prop-Reflexive-Graph
          ( ev-point-Dependent-Reflexive-Graph H x))

  is-discrete-Dependent-Reflexive-Graph : UU (l1 ⊔ l3 ⊔ l4)
  is-discrete-Dependent-Reflexive-Graph =
    type-Prop is-discrete-prop-Dependent-Reflexive-Graph

  is-prop-is-discrete-Dependent-Reflexive-Graph :
    is-prop is-discrete-Dependent-Reflexive-Graph
  is-prop-is-discrete-Dependent-Reflexive-Graph =
    is-prop-type-Prop is-discrete-prop-Dependent-Reflexive-Graph
```
