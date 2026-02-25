# The elementhood relation on coalgebras of polynomial endofunctors

```agda
module trees.elementhood-relation-coalgebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.universe-levels

open import graph-theory.directed-graphs
open import graph-theory.walks-directed-graphs

open import trees.coalgebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Given two elements `x y : X` in the underlying type of a
[coalgebra](trees.coalgebras-polynomial-endofunctors.md) of a
[polynomial endofunctor](trees.polynomial-endofunctors.md), We say that `x`
{{#concept "is an element of" Disambiguation="coalgebras of a polynomial endofunctor" Agda=is-element-of-coalgebra-polynomial-endofunctor}}
`y`, i.e., `x ∈ y`, if there is an element `b : B (shape y)` equipped with an
identification `component y b ＝ x`. Note that this elementhood relation of an
arbitrary coalgebra need not be irreflexive.

By the elementhood relation on coalgebras we obtain for each coalgebra a
[directed graph](graph-theory.directed-graphs.md).

## Definition

```agda
infixl 6 is-element-of-coalgebra-polynomial-endofunctor

is-element-of-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  (x y : type-coalgebra-polynomial-endofunctor X) → UU (l2 ⊔ l3)
is-element-of-coalgebra-polynomial-endofunctor X x y =
  fiber (component-coalgebra-polynomial-endofunctor X y) x

syntax
  is-element-of-coalgebra-polynomial-endofunctor X x y = x ∈ y in-coalgebra X
```

### The graph of a coalgebra for a polynomial endofunctor

```agda
module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  graph-coalgebra-polynomial-endofunctor :
    Directed-Graph l3 (l2 ⊔ l3)
  pr1 graph-coalgebra-polynomial-endofunctor =
    type-coalgebra-polynomial-endofunctor X
  pr2 graph-coalgebra-polynomial-endofunctor x y =
    x ∈ y in-coalgebra X

  walk-coalgebra-polynomial-endofunctor :
    (x y : type-coalgebra-polynomial-endofunctor X) → UU (l2 ⊔ l3)
  walk-coalgebra-polynomial-endofunctor =
    walk-Directed-Graph graph-coalgebra-polynomial-endofunctor

  concat-walk-coalgebra-polynomial-endofunctor :
    {x y z : type-coalgebra-polynomial-endofunctor X} →
    walk-coalgebra-polynomial-endofunctor x y →
    walk-coalgebra-polynomial-endofunctor y z →
    walk-coalgebra-polynomial-endofunctor x z
  concat-walk-coalgebra-polynomial-endofunctor =
    concat-walk-Directed-Graph graph-coalgebra-polynomial-endofunctor
```
