# Whiskering directed edges

```agda
module simplicial-type-theory.whiskering-directed-edges where
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

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.action-on-directed-edges-functions
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

Given a [directed edge](simplicial-type-theory.directed-edges.md) `α : x →₂ y`
in `A` and an [identification](foundation-core.identity-types.md) `p : y ＝ z`,
we may {#concept "whisker" Disambiguation="directed edge by identification"} `α`
by `p` to obtain a directed edge `x →₂ z`.

## Definitions

### Whiskering at the target of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  whisker-target-simplicial-hom :
    {x y z : A} → y ＝ z → x →₂ y → x →₂ z
  whisker-target-simplicial-hom p α =
    ( simplicial-arrow-simplicial-hom α ,
      eq-source-simplicial-hom α ,
      eq-target-simplicial-hom α ∙ᵣ p)
```

### Whiskering at the source of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  whisker-source-simplicial-hom :
    {x y z : A} → x ＝ z → x →₂ y → z →₂ y
  whisker-source-simplicial-hom p α =
    ( simplicial-arrow-simplicial-hom α ,
      eq-source-simplicial-hom α ∙ᵣ p ,
      eq-target-simplicial-hom α)
```

### Whiskering both end points of a directed edge

```agda
module _
  {l : Level} {A : UU l}
  where

  double-whisker-simplicial-hom :
    {x y x' y' : A} → x ＝ x' → y ＝ y' → x →₂ y → x' →₂ y'
  double-whisker-simplicial-hom p q α =
    ( simplicial-arrow-simplicial-hom α ,
      eq-source-simplicial-hom α ∙ᵣ p ,
      eq-target-simplicial-hom α ∙ᵣ q)
```

## Properties

### Whiskering directed edges is an equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-double-whisker-simplicial-hom :
    {x y x' y' : A} (p : x ＝ x') (q : y ＝ y') →
    is-equiv (double-whisker-simplicial-hom p q)
  is-equiv-double-whisker-simplicial-hom refl refl = is-equiv-id

  is-equiv-whisker-target-simplicial-hom :
    {x y z : A} (p : y ＝ z) →
    is-equiv (whisker-target-simplicial-hom {x = x} p)
  is-equiv-whisker-target-simplicial-hom p =
    is-equiv-double-whisker-simplicial-hom refl p

  is-equiv-whisker-source-simplicial-hom :
    {x y z : A} (p : x ＝ z) →
    is-equiv (whisker-source-simplicial-hom {y = y} p)
  is-equiv-whisker-source-simplicial-hom p =
    is-equiv-double-whisker-simplicial-hom p refl
```

### Naturality of homotopies with respect to directed edges

Given two maps `f g : A → B` and a homotopy `H : f ~ g`, then for every directed
edge `p : x →₂ y` in `A`, we have a commuting square

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
  {x y : A} (α : x →₂ y) →
  action-simplicial-hom-function g α ＝
  double-whisker-simplicial-hom (H x) (H y) (action-simplicial-hom-function f α)
nat-htpy▵ {A = A} {f = f} {g} H {x} {y} α =
  ind-htpy f
    ( λ g H →
      action-simplicial-hom-function g α ＝
      double-whisker-simplicial-hom (H x) (H y)
        ( action-simplicial-hom-function f α))
    ( refl)
    ( H)
```

Note that this proof only relies on
[function extensionality](foundation.function-extensionality.md) to get
extensionality for
[simplicial arrows](simplicial-type-theory.simplicial-arrows.md).

### For any map `i : A → B`, a retraction of `i` induces a retraction of the action on identifications of `i`

**Proof:** Suppose that `H : r ∘ i ~ id` and `p : i x ＝ i y` is an
identification in `B`. Then we get the directed edge

```text
     H x           ap▵ r p           H y
  x ===== r (i x) --------> r (i y) ===== y
```

This defines a map `s : (i x →₂ i y) → (x →₂ y)`. To see that `s ∘ ap▵ i ~ id`,
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

  is-hom-injective-has-retraction : {x y : A} → (i x →₂ i y) → (x →₂ y)
  is-hom-injective-has-retraction {x} {y} p =
    double-whisker-simplicial-hom
      ( H x)
      ( H y)
      ( action-simplicial-hom-function r p)

  is-retraction-is-hom-injective-has-retraction' :
    {x y : A} (α : x →₂ y) →
    htpy-simplicial-hom
      ( is-hom-injective-has-retraction (action-simplicial-hom-function i α))
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
      ( action-simplicial-hom-function i {x} {y})
      ( is-hom-injective-has-retraction)
  is-retraction-is-hom-injective-has-retraction α =
    eq-htpy-simplicial-hom
      ( is-hom-injective-has-retraction (action-simplicial-hom-function i α))
      ( α)
      ( is-retraction-is-hom-injective-has-retraction' α)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B) (R : retraction i)
  where

  is-hom-injective-retraction :
    {x y : A} → i x →₂ i y → x →₂ y
  is-hom-injective-retraction =
    is-hom-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  is-retraction-is-hom-injective-retraction :
    {x y : A} →
    is-hom-injective-retraction ∘ action-simplicial-hom-function i {x} {y} ~ id
  is-retraction-is-hom-injective-retraction =
    is-retraction-is-hom-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  retraction-ap▵ :
    {x y : A} → retraction (action-simplicial-hom-function i {x} {y})
  pr1 retraction-ap▵ = is-hom-injective-retraction
  pr2 retraction-ap▵ = is-retraction-is-hom-injective-retraction
```

### If `A` is a retract of `B` with inclusion `i : A → B`, then `x →₂ y` is a retract of `i x →₂ i y` for any two elements `x y : A`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) (x y : A)
  where

  retract-simplicial-hom :
    (x →₂ y) retract-of (inclusion-retract R x →₂ inclusion-retract R y)
  pr1 retract-simplicial-hom =
    action-simplicial-hom-function (inclusion-retract R)
  pr2 retract-simplicial-hom =
    retraction-ap▵ (inclusion-retract R) (retraction-retract R)
```
