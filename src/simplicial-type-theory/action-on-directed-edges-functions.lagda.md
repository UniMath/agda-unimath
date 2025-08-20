# The action on directed edges of functions

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.action-on-directed-edges-functions
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import simplicial-type-theory.directed-edges I
```

</details>

## Idea

Any [function](foundation-core.function-types.md) `f : A → B` preserves
[directed edges](simplicial-type-theory.directed-edges.md), in the sense that it
maps any edge `p : x →▵ y` in `A` to a directed edge
`action-hom▵ f p : f x →▵ f y` in `B`. This action on directed edges can be
understood as
{{#concept "functoriality" Disambiguation="of functions in simplicial type theory" Agda=action-hom▵-function}}
of functions in simplicial type theory.

## Definition

### The functorial action of functions on directed edges

```agda
action-hom▵-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A} →
  (x →▵ y) → (f x →▵ f y)
action-hom▵-function f (α , s , t) = (f ∘ α , ap f s , ap f t)
```

## Properties

### The identity function acts trivially on directed edges

```agda
compute-action-hom▵-id-function :
  {l : Level} {A : UU l} {x y : A} (p : x →▵ y) →
  (action-hom▵-function id p) ＝ p
compute-action-hom▵-id-function (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-id s) (ap-id t))
```

### The action on directed edges of a composite function is the composite of the actions

```agda
compute-action-hom▵-comp-function :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C)
  (f : A → B) {x y : A} (p : x →▵ y) →
  (action-hom▵-function (g ∘ f) p) ＝
  ((action-hom▵-function g ∘ action-hom▵-function f) p)
compute-action-hom▵-comp-function g f (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-comp g f s) (ap-comp g f t))

associative-action-hom▵-comp-function :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (h : C → D) (g : B → C) (f : A → B) {x y : A} (p : x →▵ y) →
  action-hom▵-function (h ∘ g) (action-hom▵-function f p) ＝
  action-hom▵-function h (action-hom▵-function (g ∘ f) p)
associative-action-hom▵-comp-function h g f (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-comp-assoc h g f s) (ap-comp-assoc h g f t))
```

### The action on directed edges of any map preserves the identity edges

In fact, the identity edges are preserved strictly.

```agda
compute-action-id-hom▵-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : A) →
  action-hom▵-function f (id-hom▵ x) ＝
  id-hom▵ (f x)
compute-action-id-hom▵-function f x = refl
```

### The action on identifications of a constant map is constant

```agda
compute-action-hom▵-const-function :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) {x y : A} (p : x →▵ y) →
  action-hom▵-function (const A b) p ＝ id-hom▵ b
compute-action-hom▵-const-function b (α , s , t) =
  eq-pair-eq-fiber (eq-pair (ap-const b s) (ap-const b t))
```
