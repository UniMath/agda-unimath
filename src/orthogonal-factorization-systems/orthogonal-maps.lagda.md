# Orthogonal maps

```agda
module orthogonal-factorization-systems.orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.homotopies
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.lifting-operations
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → X` is said to be _orthogonal to_ `g : B → Y` if the
pullback-hom is an equivalence. This means that there is a unique lifting operation between `f` and `g`.

In this case we say that `f` is _left orthogonal_ to `g` and `g` is _right orthogonal_ to `f`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-orthogonal : (A → X) → (B → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal f g = is-equiv (pullback-hom f g)

  _⊥_ = is-orthogonal

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  -- `is-right-orthogonal f g` asserts that `g` is right orthogonal to `f`
  is-right-orthogonal : (A → X) → (B → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-right-orthogonal = is-orthogonal

  -- `is-left-orthogonal f g` asserts that `g` is left orthogonal to `f`
  is-left-orthogonal : (A → X) → (B → Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-left-orthogonal g f = is-orthogonal f g
```

## Properties

### Orthogonality of maps is a property

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  is-property-is-orthogonal : is-prop (is-orthogonal f g)
  is-property-is-orthogonal = is-property-is-equiv (pullback-hom f g)

  is-orthogonal-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-orthogonal-Prop = is-orthogonal f g
  pr2 is-orthogonal-Prop = is-property-is-orthogonal
```
