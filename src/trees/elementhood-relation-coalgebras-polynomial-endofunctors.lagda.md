# The elementhood relation on coalgebras of polynomial endofunctors

```agda
open import foundation.function-extensionality-axiom

module
  trees.elementhood-relation-coalgebras-polynomial-endofunctors
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps funext
open import foundation.universe-levels

open import graph-theory.directed-graphs funext
open import graph-theory.walks-directed-graphs funext

open import trees.coalgebras-polynomial-endofunctors funext
```

</details>

## Idea

Given two elements `x y : X` in the underlying type of a coalgebra of a
polynomial endofunctor, We say that **`x` is an element of `y`**, i.e., `x ∈ y`,
if there is an element `b : B (shape y)` equipped with an identification
`component y b ＝ x`. Note that this elementhood relation of an arbitrary
coalgebra need not be irreflexive.

By the elementhood relation on coalgebras we obtain for each coalgebra a
directed graph.

## Definition

```agda
infixl 6 is-element-of-coalgebra-polynomial-endofunctor

is-element-of-coalgebra-polynomial-endofunctor :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B)
  (x y : type-coalgebra-polynomial-endofunctor X) → UU (l2 ⊔ l3)
is-element-of-coalgebra-polynomial-endofunctor X x y =
  fiber (component-coalgebra-polynomial-endofunctor X y) x

syntax
  is-element-of-coalgebra-polynomial-endofunctor X x y = x ∈ y in-coalgebra X
```

### The graph of a coalgebra for a polynomial endofunctor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B)
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
