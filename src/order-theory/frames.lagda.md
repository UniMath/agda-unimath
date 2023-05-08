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

open import order-theory.greatest-lower-bounds-posets
open import order-theory.infinite-distributive-law
open import order-theory.least-upper-bounds-posets
open import order-theory.meet-semilattices
open import order-theory.meet-suplattices
open import order-theory.posets
open import order-theory.suplattices
```

</details>

## Idea

A **frame** is a meet-semilattice with arbitrary joins, such that meets
distribute over arbitrary joins.

There are many equivalent ways to formulate this definition. Our choice here is
simply motivated by a desire to avoid iterated sigma types.

## Definitions

### The predicate on meet-suplattices to be a frame

```agda
module _
  {l1 l2 : Level} (L : Meet-Suplattice l1 l2)
  where

  is-frame-Meet-Suplattice-Prop : Prop (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice-Prop = distributive-law-Meet-Suplattice-Prop L

  is-frame-Meet-Suplattice : UU (l1 ⊔ lsuc l2)
  is-frame-Meet-Suplattice = type-Prop is-frame-Meet-Suplattice-Prop

  is-prop-is-frame-Meet-Suplattice : is-prop is-frame-Meet-Suplattice
  is-prop-is-frame-Meet-Suplattice =
    is-prop-type-Prop is-frame-Meet-Suplattice-Prop
```

### Frames

```agda
Frame : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Frame l1 l2 = Σ (Meet-Suplattice l1 l2) is-frame-Meet-Suplattice

module _
  {l1 l2 : Level} (A : Frame l1 l2)
  where

  meet-suplattice-Frame : Meet-Suplattice l1 l2
  meet-suplattice-Frame = pr1 A

  meet-semilattice-Frame : Meet-Semilattice l1
  meet-semilattice-Frame =
    meet-semilattice-Meet-Suplattice meet-suplattice-Frame

  suplattice-Frame : Suplattice l1 l1 l2
  suplattice-Frame = suplattice-Meet-Suplattice meet-suplattice-Frame

  poset-Frame : Poset l1 l1
  poset-Frame = poset-Meet-Suplattice meet-suplattice-Frame

  set-Frame : Set l1
  set-Frame = set-Poset poset-Frame

  type-Frame : UU l1
  type-Frame = type-Poset poset-Frame

  is-set-type-Frame : is-set type-Frame
  is-set-type-Frame = is-set-type-Poset poset-Frame

  leq-Frame-Prop : (x y : type-Frame) → Prop l1
  leq-Frame-Prop = leq-Poset-Prop poset-Frame

  leq-Frame : (x y : type-Frame) → UU l1
  leq-Frame = leq-Poset poset-Frame

  is-prop-leq-Frame : (x y : type-Frame) → is-prop (leq-Frame x y)
  is-prop-leq-Frame = is-prop-leq-Poset poset-Frame

  refl-leq-Frame : (x : type-Frame) → leq-Frame x x
  refl-leq-Frame = refl-leq-Poset poset-Frame

  antisymmetric-leq-Frame :
    (x y : type-Frame) → leq-Frame x y → leq-Frame y x → x ＝ y
  antisymmetric-leq-Frame = antisymmetric-leq-Poset poset-Frame

  transitive-leq-Frame :
    (x y z : type-Frame) → leq-Frame y z → leq-Frame x y → leq-Frame x z
  transitive-leq-Frame = transitive-leq-Poset poset-Frame

  meet-Frame : type-Frame → type-Frame → type-Frame
  meet-Frame = meet-Meet-Semilattice meet-semilattice-Frame

  is-greatest-binary-lower-bound-meet-Frame :
    (x y : type-Frame) →
    is-greatest-binary-lower-bound-Poset poset-Frame x y (meet-Frame x y)
  is-greatest-binary-lower-bound-meet-Frame =
    is-greatest-binary-lower-bound-meet-Meet-Semilattice meet-semilattice-Frame

  associative-meet-Frame :
    (x y z : type-Frame) →
    meet-Frame (meet-Frame x y) z ＝ meet-Frame x (meet-Frame y z)
  associative-meet-Frame =
    associative-meet-Meet-Semilattice meet-semilattice-Frame

  commutative-meet-Frame :
    (x y : type-Frame) → meet-Frame x y ＝ meet-Frame y x
  commutative-meet-Frame =
    commutative-meet-Meet-Semilattice meet-semilattice-Frame

  idempotent-meet-Frame :
    (x : type-Frame) → meet-Frame x x ＝ x
  idempotent-meet-Frame =
    idempotent-meet-Meet-Semilattice meet-semilattice-Frame

  is-suplattice-Frame :
    is-suplattice-Poset l2 poset-Frame
  is-suplattice-Frame = is-suplattice-Suplattice suplattice-Frame

  sup-Frame : {I : UU l2} → (I → type-Frame) → type-Frame
  sup-Frame = sup-Suplattice suplattice-Frame

  is-least-upper-bound-sup-Frame :
    {I : UU l2} (x : I → type-Frame) →
    is-least-upper-bound-family-of-elements-Poset poset-Frame x (sup-Frame x)
  is-least-upper-bound-sup-Frame =
    is-least-upper-bound-sup-Suplattice suplattice-Frame

  distributive-meet-sup-Frame :
    distributive-law-Meet-Suplattice meet-suplattice-Frame
  distributive-meet-sup-Frame = pr2 A
```
