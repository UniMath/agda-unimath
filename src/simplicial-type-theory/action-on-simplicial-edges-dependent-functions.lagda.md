# The action on simplicial edges of dependent functions

```agda
module simplicial-type-theory.action-on-simplicial-edges-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import simplicial-type-theory.simplicial-edges
open import simplicial-type-theory.dependent-simplicial-edges
```

</details>

## Idea

Any dependent function `f : (x : A) → B x` preserves
[simplicial edges](simplicial-type-theory.simplicial-edges.md), in the sense
that it maps any edge `p : x →₂ y` in `A` to a dependent edge
`action-simplicial-hom-dependent-function f p` from `f x` to `f y` over `p` in
`B`. This action on simplicial edges can be thought of as functoriality of
functions in simplicial type theory.

## Definition

### The functorial action of dependent functions on simplicial edges

```agda
action-simplicial-hom-dependent-function :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) {x y : A} →
  (α : x →₂ y) → dependent-simplicial-hom B α (f x) (f y)
action-simplicial-hom-dependent-function f (α , s , t) =
  ( f ∘ α , apd f s , apd f t)
```
