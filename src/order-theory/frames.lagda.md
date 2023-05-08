# Frames

```agda
module order-theory.frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.infinite-distributive-law
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

A **frame** is a meet-semilattice with arbitrary joins, such that meets
distribute over arbitrary joins.

There are many equivalent ways to formulate this definition. Our choice here is
simply motivated by a desire to avoid iterated sigma types.

```agda
Frame : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Frame l1 l2 =
  Σ (Meet-Suplattice l1 l2) (distributive-law-meet-suplattice l1 l2)
```

## Now we retrieve all the information from a frame (i.e. break up all of it's components, etc.)

```agda
module _
  {l1 l2 : Level} (A : Frame l1 l2)
  where

  poset-Frame : Poset l1 l1
  poset-Frame = poset-Meet-Suplattice (pr1 A)

  type-Frame : UU l1
  type-Frame = type-Poset poset-Frame

  leq-Frame-Prop : (x y : type-Frame) → Prop l1
  leq-Frame-Prop = leq-Poset-Prop poset-Frame

  leq-Frame : (x y : type-Frame) → UU l1
  leq-Frame = leq-Poset poset-Frame

  is-prop-leq-Frame :
    (x y : type-Frame) → is-prop (leq-Frame x y)
  is-prop-leq-Frame = is-prop-leq-Poset poset-Frame
  refl-leq-Frame :
    (x : type-Frame) → leq-Frame x x
  refl-leq-Frame = refl-leq-Poset poset-Frame

  antisymmetric-leq-Frame :
    (x y : type-Frame) →
    leq-Frame x y → leq-Frame y x → x ＝ y
  antisymmetric-leq-Frame =
    antisymmetric-leq-Poset poset-Frame

  transitive-leq-Frame :
    (x y z : type-Frame) →
    leq-Frame y z → leq-Frame x y →
    leq-Frame x z
  transitive-leq-Frame = transitive-leq-Poset poset-Frame

  is-set-type-Frame : is-set type-Frame
  is-set-type-Frame = is-set-type-Poset poset-Frame

  set-Frame : Set l1
  set-Frame = set-Poset poset-Frame

  meet-semilattice-Frame : Meet-Semilattice l1
  meet-semilattice-Frame = meet-semilattice-Meet-Suplattice (pr1 A)

  is-suplattice-Frame :
    is-suplattice-Poset l2 poset-Frame
  is-suplattice-Frame = is-suplattice-Meet-Suplattice (pr1 A)

  suplattice-Frame : Suplattice l1 l1 l2
  suplattice-Frame = ( poset-Frame , is-suplattice-Frame)

  meet-suplattice-Frame :
    Meet-Suplattice l1 l2
  meet-suplattice-Frame = pr1 A

  meet-Frame :
    (x y : type-Frame) →
    type-Frame
  meet-Frame = meet-Meet-Semilattice meet-semilattice-Frame

  sup-Frame :
    (I : UU l2) → (I → type-Frame) →
    type-Frame
  sup-Frame I b = pr1 (is-suplattice-Frame I b)

  distributive-law-Frame :
    distributive-law-meet-suplattice l1 l2 meet-suplattice-Frame
  distributive-law-Frame = pr2 A

  frame-Frame : Frame l1 l2
  pr1 frame-Frame = meet-suplattice-Frame
  pr2 frame-Frame = distributive-law-Frame
```
