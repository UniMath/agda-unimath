# The action on simplicial edges of functions

```agda
module simplicial-type-theory.action-on-simplicial-edges-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

Any function `f : A → B` preserves
[simplicial edges](simplicial-type-theory.simplicial-edges.md), in the sense
that it maps any edge `p : x →₂ y` in `A` to an edge
`action-simplicial-hom f p : f x →₂ f y` in `B`. This action on simplicial edges
can be thought of as functoriality of functions in simplicial type theory.

## Definition

### The functorial action of functions on simplicial edges

```agda
action-simplicial-hom-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A} →
  x →₂ y → f x →₂ f y
action-simplicial-hom-function f (α , s , t) = (f ∘ α , ap f s , ap f t)
```

## Properties

### The identity function acts trivially on simplicial edges

```agda
compute-action-simplicial-hom-id-function :
  {l : Level} {A : UU l} {x y : A} (p : x →₂ y) →
  (action-simplicial-hom-function id p) ＝ p
compute-action-simplicial-hom-id-function (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-id s) (ap-id t))
```

### The action on simplicial edges of a composite function is the composite of the actions

```agda
compute-action-simplicial-hom-comp-function :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C)
  (f : A → B) {x y : A} (p : x →₂ y) →
  (action-simplicial-hom-function (g ∘ f) p) ＝
  ((action-simplicial-hom-function g ∘ action-simplicial-hom-function f) p)
compute-action-simplicial-hom-comp-function g f (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-comp g f s) (ap-comp g f t))

associative-action-simplicial-hom-comp-function :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (h : C → D) (g : B → C) (f : A → B) {x y : A} (p : x →₂ y) →
  action-simplicial-hom-function (h ∘ g) (action-simplicial-hom-function f p) ＝
  action-simplicial-hom-function h (action-simplicial-hom-function (g ∘ f) p)
associative-action-simplicial-hom-comp-function h g f (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-comp-assoc h g f s) (ap-comp-assoc h g f t))
```

### The action on simplicial edges of any map preserves the identity edges

In fact, the identity edges are preserved strictly.

```agda
compute-action-id-simplicial-hom-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : A) →
  action-simplicial-hom-function f (id-simplicial-hom x) ＝
  id-simplicial-hom (f x)
compute-action-id-simplicial-hom-function f x = refl
```

### The action on identifications of a constant map is constant

```agda
compute-action-simplicial-hom-const-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) {x y : A} (p : x →₂ y) →
  action-simplicial-hom-function (const A b) p ＝ id-simplicial-hom b
compute-action-simplicial-hom-const-function b (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-const b s) (ap-const b t))
```
