# Whiskering directed edges by identifications

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.whiskering-directed-edges-identifications
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.strictly-right-unital-concatenation-identifications
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
```

</details>

## Idea

Given a [directed edge](simplicial-type-theory.directed-edges.md) `α : x →▵ y`
in `A` then we may
{{#concept "right whisker" Disambiguation="directed edge by identification" Agda=whisker-target-hom▵}}
`α` by any [identification](foundation-core.identity-types.md) `p : y ＝ z`, and
we may to obtain a directed edge `αp : x →▵ z`, or we may
{{#concept "right whisker" Disambiguation="directed edge by identification" Agda=whisker-source-hom▵}}
`α` by any [identification](foundation-core.identity-types.md) `q : z ＝ x` to
obtain a directed edge `qα : z →▵ y`.

## Definitions

### Whiskering at the target of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  whisker-target-hom▵ :
    {x y z : A} → (y ＝ z) → (x →▵ y) → (x →▵ z)
  whisker-target-hom▵ p α =
    ( arrow-hom▵ α ,
      eq-source-hom▵ α ,
      eq-target-hom▵ α ∙ᵣ p)
```

### Whiskering at the source of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  whisker-source-hom▵ :
    {x y z : A} → (x ＝ z) → (x →▵ y) → (z →▵ y)
  whisker-source-hom▵ p α =
    ( arrow-hom▵ α ,
      eq-source-hom▵ α ∙ᵣ p ,
      eq-target-hom▵ α)
```

### Whiskering both end points of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  double-whisker-hom▵ :
    {x y x' y' : A} → (x ＝ x') → (y ＝ y') → (x →▵ y) → (x' →▵ y')
  double-whisker-hom▵ p q α =
    ( arrow-hom▵ α ,
      eq-source-hom▵ α ∙ᵣ p ,
      eq-target-hom▵ α ∙ᵣ q)
```

## Properties

### Whiskering directed edges is an equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-double-whisker-hom▵ :
    {x y x' y' : A} (p : x ＝ x') (q : y ＝ y') →
    is-equiv (double-whisker-hom▵ p q)
  is-equiv-double-whisker-hom▵ refl refl = is-equiv-id

  is-equiv-whisker-target-hom▵ :
    {x y z : A} (p : y ＝ z) →
    is-equiv (whisker-target-hom▵ {x = x} p)
  is-equiv-whisker-target-hom▵ p =
    is-equiv-double-whisker-hom▵ refl p

  is-equiv-whisker-source-hom▵ :
    {x y z : A} (p : x ＝ z) →
    is-equiv (whisker-source-hom▵ {y = y} p)
  is-equiv-whisker-source-hom▵ p =
    is-equiv-double-whisker-hom▵ p refl
```

### Naturality of homotopies with respect to directed edges

Given two maps `f g : A → B` and a homotopy `H : f ~ g`, then for every directed
edge `p : x →▵ y` in `A`, we have a commuting square

```text
          ap▵ f p
     f x --------> f y
      ║             ║
  H x ║             ║ H y
      ║             ║
     g x --------> g y.
          ap▵ g p
```

```agda
nat-htpy▵ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  {x y : A} (α : x →▵ y) →
  action-hom▵-function g α ＝
  double-whisker-hom▵ (H x) (H y) (action-hom▵-function f α)
nat-htpy▵ {f = f} {g} H {x} {y} α =
  ind-htpy f
    ( λ g H →
      action-hom▵-function g α ＝
      double-whisker-hom▵ (H x) (H y)
        ( action-hom▵-function f α))
    ( refl)
    ( H)
```

Note that this proof only relies on
[function extensionality](foundation.function-extensionality.md) to get
extensionality for [simplicial arrows](simplicial-type-theory.arrows.md).

### For any map `i : A → B`, a retraction of `i` induces a retraction of the action on identifications of `i`

**Proof:** Suppose that `H : r ∘ i ~ id` and `p : i x ＝ i y` is an
identification in `B`. Then we get the directed edge

```text
     H x           ap▵ r p           H y
  x ===== r (i x) --------> r (i y) ===== y
```

This defines a map `s : (i x →▵ i y) → (x →▵ y)`. To see that `s ∘ ap▵ i ~ id`,
i.e., that the whiskering

```text
     H x           ap▵ r (ap▵ i p)           H y
  x ===== r (i x) ----------------> r (i y) ===== y
```

is identical to `p : x ＝ y` for all `p : x ＝ y`, we proceed by identification
elimination. Then it suffices to show that `(H x)⁻¹ ∙ (H x)` is identical to
`refl`, which is indeed the case by the left inverse law of concatenation of
identifications.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  (r : B → A) (H : r ∘ i ~ id)
  where

  is-hom-injective-has-retraction : {x y : A} → (i x →▵ i y) → (x →▵ y)
  is-hom-injective-has-retraction {x} {y} p =
    double-whisker-hom▵
      ( H x)
      ( H y)
      ( action-hom▵-function r p)

  is-retraction-is-hom-injective-has-retraction' :
    {x y : A} (α : x →▵ y) →
    htpy-hom▵
      ( is-hom-injective-has-retraction (action-hom▵-function i α))
      ( α)
  pr1 (is-retraction-is-hom-injective-has-retraction' (α , p , q)) =
    H ·r α
  pr1 (pr2 (is-retraction-is-hom-injective-has-retraction' (α , refl , q))) =
    left-unit-right-strict-concat ∙ inv right-unit
  pr2 (pr2 (is-retraction-is-hom-injective-has-retraction' (α , p , refl))) =
    left-unit-right-strict-concat ∙ inv right-unit

  is-retraction-is-hom-injective-has-retraction :
    {x y : A} →
    is-retraction
      ( action-hom▵-function i {x} {y})
      ( is-hom-injective-has-retraction)
  is-retraction-is-hom-injective-has-retraction α =
    eq-htpy-hom▵
      ( is-hom-injective-has-retraction (action-hom▵-function i α))
      ( α)
      ( is-retraction-is-hom-injective-has-retraction' α)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B) (R : retraction i)
  where

  is-hom-injective-retraction :
    {x y : A} → (i x →▵ i y) → (x →▵ y)
  is-hom-injective-retraction =
    is-hom-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  is-retraction-is-hom-injective-retraction :
    {x y : A} →
    is-hom-injective-retraction ∘ action-hom▵-function i {x} {y} ~ id
  is-retraction-is-hom-injective-retraction =
    is-retraction-is-hom-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  retraction-ap▵ :
    {x y : A} → retraction (action-hom▵-function i {x} {y})
  pr1 retraction-ap▵ = is-hom-injective-retraction
  pr2 retraction-ap▵ = is-retraction-is-hom-injective-retraction
```

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x →▵ y` is a retract of `i x →▵ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) (x y : A)
  where

  retract-hom▵ :
    (x →▵ y) retract-of (inclusion-retract R x →▵ inclusion-retract R y)
  pr1 retract-hom▵ =
    action-hom▵-function (inclusion-retract R)
  pr2 retract-hom▵ =
    retraction-ap▵ (inclusion-retract R) (retraction-retract R)
```
