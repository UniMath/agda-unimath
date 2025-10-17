# The universal property of the circle

```agda
module synthetic-homotopy-theory.universal-property-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.constant-type-families
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-loops
```

</details>

## Definitions

### Evaluating an ordinary function at a free loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  ev-free-loop : (X → Y) → free-loop Y
  pr1 (ev-free-loop f) = f (base-free-loop α)
  pr2 (ev-free-loop f) = ap f (loop-free-loop α)
```

### The universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  universal-property-circle : UUω
  universal-property-circle =
    {l : Level} (Y : UU l) → is-equiv (ev-free-loop α Y)
```

### Evaluating a dependent function at a free loop

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (P : X → UU l2)
  where

  ev-free-loop-Π : ((x : X) → P x) → free-dependent-loop α P
  pr1 (ev-free-loop-Π f) = f (base-free-loop α)
  pr2 (ev-free-loop-Π f) = apd f (loop-free-loop α)
```

### The induction principle of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  induction-principle-circle : UUω
  induction-principle-circle =
    {l2 : Level} (P : X → UU l2) → section (ev-free-loop-Π α P)

module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X)
  (H : induction-principle-circle α) (P : X → UU l2)
  (β : free-dependent-loop α P)
  where

  function-induction-principle-circle : (x : X) → P x
  function-induction-principle-circle = pr1 (H P) β

  compute-induction-principle-circle :
    (ev-free-loop-Π α P function-induction-principle-circle) ＝ β
  compute-induction-principle-circle = pr2 (H P) β
```

### The dependent universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  dependent-universal-property-circle : UUω
  dependent-universal-property-circle =
    {l2 : Level} (P : X → UU l2) → is-equiv (ev-free-loop-Π α P)
```

## Properties

### The induction principle of the circle implies the dependent universal property of the circle

To prove this, we have to show that the section of ev-free-loop-Π is also a
retraction. This construction is also by the induction principle of the circle,
but it requires (a minimal amount of) preparations.

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  free-dependent-loop-htpy :
    {l2 : Level} {P : X → UU l2} {f g : (x : X) → P x} →
    ( Eq-free-dependent-loop α P
      ( ev-free-loop-Π α P f)
      ( ev-free-loop-Π α P g)) →
    ( free-dependent-loop α (λ x → f x ＝ g x))
  pr1 (free-dependent-loop-htpy {l2} {P} {f} {g} (p , q)) = p
  pr2 (free-dependent-loop-htpy {l2} {P} {f} {g} (p , q)) =
    map-compute-dependent-identification-eq-value f g (loop-free-loop α) p p q

  is-retraction-ind-circle :
    ( ind-circle : induction-principle-circle α)
    { l2 : Level} (P : X → UU l2) →
    ( ( function-induction-principle-circle α ind-circle P) ∘
      ( ev-free-loop-Π α P)) ~
    ( id)
  is-retraction-ind-circle ind-circle P f =
    eq-htpy
      ( function-induction-principle-circle α ind-circle
        ( eq-value
          ( function-induction-principle-circle α ind-circle P
            ( ev-free-loop-Π α P f))
          ( f))
        ( free-dependent-loop-htpy
          ( Eq-free-dependent-loop-eq α P _ _
            ( compute-induction-principle-circle α ind-circle P
              ( ev-free-loop-Π α P f)))))

  abstract
    dependent-universal-property-induction-principle-circle :
      induction-principle-circle α →
      dependent-universal-property-circle α
    dependent-universal-property-induction-principle-circle ind-circle P =
      is-equiv-is-invertible
        ( function-induction-principle-circle α ind-circle P)
        ( compute-induction-principle-circle α ind-circle P)
        ( is-retraction-ind-circle ind-circle P)
```

### Uniqueness of the maps obtained from the universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    uniqueness-universal-property-circle :
      universal-property-circle α →
      {l2 : Level} (Y : UU l2) (α' : free-loop Y) →
      is-contr (Σ (X → Y) (λ f → Eq-free-loop (ev-free-loop α Y f) α'))
    uniqueness-universal-property-circle up-circle Y α' =
      is-contr-is-equiv'
        ( fiber (ev-free-loop α Y) α')
        ( tot (λ f → Eq-eq-free-loop (ev-free-loop α Y f) α'))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ f → is-equiv-Eq-eq-free-loop (ev-free-loop α Y f) α'))
        ( is-contr-map-is-equiv (up-circle Y) α')
```

### Uniqueness of the dependent functions obtained from the dependent universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  uniqueness-dependent-universal-property-circle :
    dependent-universal-property-circle α →
    {l2 : Level} {P : X → UU l2} (k : free-dependent-loop α P) →
    is-contr
      ( Σ ( (x : X) → P x)
          ( λ h → Eq-free-dependent-loop α P (ev-free-loop-Π α P h) k))
  uniqueness-dependent-universal-property-circle dup-circle {l2} {P} k =
    is-contr-is-equiv'
      ( fiber (ev-free-loop-Π α P) k)
      ( tot (λ h → Eq-free-dependent-loop-eq α P (ev-free-loop-Π α P h) k))
      ( is-equiv-tot-is-fiberwise-equiv
        (λ h → is-equiv-Eq-free-dependent-loop-eq α P (ev-free-loop-Π α P h) k))
      ( is-contr-map-is-equiv (dup-circle P) k)
```

### The dependent universal property of the circle implies the universal property of the circle

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-loop X) (Y : UU l2)
  where

  triangle-comparison-free-loop :
    map-compute-free-dependent-loop-constant-type-family α Y ∘
    ev-free-loop α Y ~
    ev-free-loop-Π α (λ _ → Y)
  triangle-comparison-free-loop f =
    eq-Eq-free-dependent-loop α
      ( λ x → Y)
      ( map-compute-free-dependent-loop-constant-type-family α Y
        ( ev-free-loop α Y f))
      ( ev-free-loop-Π α (λ x → Y) f)
      ( refl ,
        right-unit ∙ (inv (apd-constant-type-family f (loop-free-loop α))))

module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    universal-property-dependent-universal-property-circle :
      dependent-universal-property-circle α →
      universal-property-circle α
    universal-property-dependent-universal-property-circle dup-circle Y =
      is-equiv-top-map-triangle
        ( ev-free-loop-Π α (λ x → Y))
        ( map-compute-free-dependent-loop-constant-type-family α Y)
        ( ev-free-loop α Y)
        ( inv-htpy (triangle-comparison-free-loop α Y))
        ( is-equiv-map-equiv
          ( compute-free-dependent-loop-constant-type-family α Y))
        ( dup-circle (λ x → Y))
```

### The induction principle of the circle implies the universal property of the circle

```agda
module _
  {l1 : Level} {X : UU l1} (α : free-loop X)
  where

  abstract
    universal-property-induction-principle-circle :
      induction-principle-circle α →
      universal-property-circle α
    universal-property-induction-principle-circle X =
      universal-property-dependent-universal-property-circle α
        ( dependent-universal-property-induction-principle-circle α X)
```

### The dependent universal property of the circle with respect to propositions

```agda
abstract
  is-connected-circle' :
    { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l)
    ( P : X → UU l2) (is-prop-P : (x : X) → is-prop (P x)) →
    P (base-free-loop l) → (x : X) → P x
  is-connected-circle' l dup-circle P is-prop-P p =
    map-inv-is-equiv
      ( dup-circle P)
      ( pair p (center (is-prop-P _ (tr P (loop-free-loop l) p) p)))
```
