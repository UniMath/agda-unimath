# Null maps

```agda
module orthogonal-factorization-systems.null-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.families-of-equivalences
open import foundation.fibers-of-maps
open import foundation.functoriality-cartesian-product-types
open import foundation.function-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.type-arithmetic-unit-type
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-family-of-fibers-of-maps
open import foundation.universe-levels

open import orthogonal-factorization-systems.maps-local-at-maps
open import orthogonal-factorization-systems.null-families-of-types
open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.types-local-at-maps
```

</details>

## Idea

A map `f : A → B` is said to be
{{#concept "null" Disambiguation="function at a type" Agda=is-null-map}} at `Y`,
or {{#concept "`Y`-null" Disambiguation="function at a type" Agda=is-null-map}}
if its [fibers](foundation-core.fibers-of-maps.md) are
`Y`-[null](orthogonal-factorization-systems.null-types.md), or equivalently, if
the square

```text
         Δ
    A ------> (Y → A)
    |            |
  f |            | f ∘ -
    ∨            ∨
    B ------> (Y → B)
         Δ
```

is a [pullback](foundation-core.pullbacks.md).

## Definitions

### The fiber condition for `Y`-null maps

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (f : A → B)
  where

  is-null-map : UU (l1 ⊔ l2 ⊔ l3)
  is-null-map = is-null-family Y (fiber f)

  is-property-is-null-map : is-prop is-null-map
  is-property-is-null-map = is-property-is-null-family Y (fiber f)

  is-null-map-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  is-null-map-Prop = (is-null-map , is-property-is-null-map)
```

### The pullback condition for `Y`-null maps

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (f : A → B)
  where

  cone-is-null-map-pullback-condition :
    cone (diagonal-exponential B Y) (postcomp Y f) A
  cone-is-null-map-pullback-condition =
    (f , diagonal-exponential A Y , refl-htpy)

  is-null-map-pullback-condition : UU (l1 ⊔ l2 ⊔ l3)
  is-null-map-pullback-condition =
    is-pullback
      ( diagonal-exponential B Y)
      ( postcomp Y f)
      ( cone-is-null-map-pullback-condition)

  is-prop-is-null-map-pullback-condition :
    is-prop is-null-map-pullback-condition
  is-prop-is-null-map-pullback-condition =
    is-prop-is-pullback
      ( diagonal-exponential B Y)
      ( postcomp Y f)
      ( cone-is-null-map-pullback-condition)
```

## Properties

### A type family is `Y`-null if and only if its total space projection is

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} (B : A → UU l3)
  where

  is-null-family-is-null-map-pr1 :
    is-null-map Y (pr1 {B = B}) → is-null-family Y B
  is-null-family-is-null-map-pr1 =
    is-null-family-equiv-family (inv-equiv-fiber-pr1 B)

  is-null-map-pr1-is-null-family :
    is-null-family Y B → is-null-map Y (pr1 {B = B})
  is-null-map-pr1-is-null-family =
    is-null-family-equiv-family (equiv-fiber-pr1 B)
```

### The pullback and fiber condition for `Y`-null maps are equivalent

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (f : A → B)
  where

  abstract
    compute-map-fiber-vertical-map-cone-is-null-map-pullback-condition :
      (b : B) →
      equiv-arrow
        ( map-fiber-vertical-map-cone
          ( diagonal-exponential B Y)
          ( postcomp Y f)
          ( cone-is-null-map-pullback-condition Y f)
          ( b))
        ( diagonal-exponential (fiber f b) Y)
    compute-map-fiber-vertical-map-cone-is-null-map-pullback-condition b =
      ( id-equiv ,
        inv-compute-Π-fiber-postcomp Y f (diagonal-exponential B Y b) ,
        ( λ where (x , refl) → refl))

  is-null-map-pullback-condition-is-null-map :
    is-null-map Y f → is-null-map-pullback-condition Y f
  is-null-map-pullback-condition-is-null-map H =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
      ( diagonal-exponential B Y)
      ( postcomp Y f)
      ( cone-is-null-map-pullback-condition Y f)
      ( λ b →
        is-equiv-source-is-equiv-target-equiv-arrow
          ( map-fiber-vertical-map-cone
            ( diagonal-exponential B Y)
            ( postcomp Y f)
            ( cone-is-null-map-pullback-condition Y f)
            ( b))
          ( diagonal-exponential (fiber f b) Y)
          ( compute-map-fiber-vertical-map-cone-is-null-map-pullback-condition
            ( b))
          ( H b))

  is-null-map-is-null-map-pullback-condition :
    is-null-map-pullback-condition Y f → is-null-map Y f
  is-null-map-is-null-map-pullback-condition H b =
    is-equiv-target-is-equiv-source-equiv-arrow
      ( map-fiber-vertical-map-cone
        ( diagonal-exponential B Y)
        ( postcomp Y f)
        ( cone-is-null-map-pullback-condition Y f)
        ( b))
      ( diagonal-exponential (fiber f b) Y)
      ( compute-map-fiber-vertical-map-cone-is-null-map-pullback-condition b)
      ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
        ( diagonal-exponential B Y)
        ( postcomp Y f)
        ( cone-is-null-map-pullback-condition Y f)
        ( H)
        ( b))
```

### A map is `Y`-null if and only if it is local at the terminal projection `Y → unit`

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (f : A → B)
  where

  is-local-terminal-map-is-null-map :
    is-null-map Y f → is-local-map (terminal-map Y) f
  is-local-terminal-map-is-null-map H x =
    is-local-terminal-map-is-null Y (fiber f x) (H x)

  is-null-map-is-local-terminal-map :
    is-local-map (terminal-map Y) f → is-null-map Y f
  is-null-map-is-local-terminal-map H x =
    is-null-is-local-terminal-map Y (fiber f x) (H x)

  equiv-is-local-terminal-map-is-null-map :
    is-null-map Y f ≃ is-local-map (terminal-map Y) f
  equiv-is-local-terminal-map-is-null-map =
    equiv-iff-is-prop
      ( is-property-is-null-map Y f)
      ( is-property-is-local-map (terminal-map Y) f)
      ( is-local-terminal-map-is-null-map)
      ( is-null-map-is-local-terminal-map)

  equiv-is-null-map-is-local-terminal-map :
    is-local-map (terminal-map Y) f ≃ is-null-map Y f
  equiv-is-null-map-is-local-terminal-map =
    inv-equiv equiv-is-local-terminal-map-is-null-map
```

### A map is `Y`-null if and only if it is `Y`-orthogonal

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (f : A → B)
  where

  is-null-map-is-orthogonal-fiber-condition-terminal-map :
    is-orthogonal-fiber-condition-right-map (terminal-map Y) f →
    is-null-map Y f
  is-null-map-is-orthogonal-fiber-condition-terminal-map H b =
    is-equiv-target-is-equiv-source-equiv-arrow
      ( precomp (terminal-map Y) (fiber f b))
      ( diagonal-exponential (fiber f b) Y)
      ( left-unit-law-function-type (fiber f b) , id-equiv , refl-htpy)
      ( H (point b))

  is-orthogonal-fiber-condition-terminal-map-is-null-map :
    is-null-map Y f →
    is-orthogonal-fiber-condition-right-map (terminal-map Y) f
  is-orthogonal-fiber-condition-terminal-map-is-null-map H b =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp (terminal-map Y) (fiber f (b star)))
      ( diagonal-exponential (fiber f (b star)) Y)
      ( left-unit-law-function-type (fiber f (b star)) , id-equiv , refl-htpy)
      ( H (b star))

  is-null-map-is-orthogonal-pullback-condition-terminal-map :
    is-orthogonal-pullback-condition (terminal-map Y) f → is-null-map Y f
  is-null-map-is-orthogonal-pullback-condition-terminal-map H =
    is-null-map-is-orthogonal-fiber-condition-terminal-map
      ( is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-condition
        ( terminal-map Y)
        ( f)
        ( H))

  is-orthogonal-pullback-condition-terminal-map-is-null-map :
    is-null-map Y f → is-orthogonal-pullback-condition (terminal-map Y) f
  is-orthogonal-pullback-condition-terminal-map-is-null-map H =
    is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-map
      ( terminal-map Y)
      ( f)
      ( is-orthogonal-fiber-condition-terminal-map-is-null-map H)

  is-null-map-is-orthogonal-terminal-map :
    is-orthogonal (terminal-map Y) f → is-null-map Y f
  is-null-map-is-orthogonal-terminal-map H =
    is-null-map-is-orthogonal-fiber-condition-terminal-map
      ( is-orthogonal-fiber-condition-right-map-is-orthogonal
        ( terminal-map Y)
        ( f)
        ( H))

  is-orthogonal-terminal-map-is-null-map :
    is-null-map Y f → is-orthogonal (terminal-map Y) f
  is-orthogonal-terminal-map-is-null-map H =
    is-orthogonal-is-orthogonal-fiber-condition-right-map (terminal-map Y) f
      ( is-orthogonal-fiber-condition-terminal-map-is-null-map H)
```

### Equivalences are null at any type

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3} (e : A ≃ B)
  where

  is-null-map-map-equiv : is-null-map Y (map-equiv e)
  is-null-map-map-equiv =
    is-null-map-is-orthogonal-terminal-map Y
      ( map-equiv e)
      ( is-orthogonal-equiv-right (terminal-map Y) e)
```

### Null maps are closed under homotopies

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : UU l3}
  {f g : A → B}
  where

  is-null-map-htpy : f ~ g → is-null-map Y f → is-null-map Y g
  is-null-map-htpy H is-null-f =
    is-null-map-is-orthogonal-terminal-map Y g
      ( is-orthogonal-htpy-right (terminal-map Y) f H
        ( is-orthogonal-terminal-map-is-null-map Y f is-null-f))

  is-null-map-htpy' : g ~ f → is-null-map Y f → is-null-map Y g
  is-null-map-htpy' H = is-null-map-htpy (inv-htpy H)
```

### A family is `Y`-null if and only if it is `Y`-orthogonal

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : A → UU l3}
  where

  is-null-family-is-orthogonal-terminal-map :
    is-orthogonal (terminal-map Y) (pr1 {B = B}) → is-null-family Y B
  is-null-family-is-orthogonal-terminal-map H =
    is-null-family-is-null-map-pr1 Y B
      ( is-null-map-is-orthogonal-terminal-map Y pr1 H)

  is-orthogonal-terminal-map-is-null-family :
    is-null-family Y B → is-orthogonal (terminal-map Y) (pr1 {B = B})
  is-orthogonal-terminal-map-is-null-family H =
    is-orthogonal-terminal-map-is-null-map Y pr1
      ( is-null-map-pr1-is-null-family Y B H)
```

### The dependent sum of a `Y`-null type family over a `Y`-null base is `Y`-null

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} {B : A → UU l3}
  where

  abstract
    is-null-Σ : is-null Y A → is-null-family Y B → is-null Y (Σ A B)
    is-null-Σ is-null-A is-null-B =
      is-null-is-orthogonal-terminal-maps
        ( is-orthogonal-right-comp
          ( terminal-map Y)
          ( pr1)
          ( terminal-map A)
          ( is-orthogonal-terminal-maps-is-null is-null-A)
          ( is-orthogonal-terminal-map-is-null-family Y is-null-B))

  abstract
    is-null-family-is-null-Σ :
      is-null Y A → is-null Y (Σ A B) → is-null-family Y B
    is-null-family-is-null-Σ is-null-A is-null-ΣAB =
      is-null-family-is-orthogonal-terminal-map Y
        ( is-orthogonal-right-right-factor
          ( terminal-map Y)
          ( pr1)
          ( terminal-map A)
          ( is-orthogonal-terminal-maps-is-null is-null-A)
          ( is-orthogonal-terminal-maps-is-null is-null-ΣAB))
```

### Composition and right cancellation of null maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (Y : UU l1) {A : UU l2} {B : UU l3} {C : UU l4}
  {f : A → B} {g : B → C}
  where

  abstract
    is-null-map-comp :
      is-null-map Y g → is-null-map Y f → is-null-map Y (g ∘ f)
    is-null-map-comp is-null-g is-null-f =
      is-null-map-is-orthogonal-terminal-map Y (g ∘ f)
        ( is-orthogonal-right-comp (terminal-map Y) f g
          ( is-orthogonal-terminal-map-is-null-map Y g is-null-g)
          ( is-orthogonal-terminal-map-is-null-map Y f is-null-f))

  abstract
    is-null-map-right-factor :
      is-null-map Y g → is-null-map Y (g ∘ f) → is-null-map Y f
    is-null-map-right-factor is-null-g is-null-gf =
      is-null-map-is-orthogonal-terminal-map Y f
        ( is-orthogonal-right-right-factor (terminal-map Y) f g
          ( is-orthogonal-terminal-map-is-null-map Y g is-null-g)
          ( is-orthogonal-terminal-map-is-null-map Y (g ∘ f) is-null-gf))

module _
  {l1 l2 l3 l4 : Level}
  (Y : UU l1) {A : UU l2} {B : UU l3} {C : UU l4}
  {f : A → B} {g : B → C} {h : A → C} (H : h ~ g ∘ f)
  where

  is-null-map-left-map-triangle :
    is-null-map Y g → is-null-map Y f → is-null-map Y h
  is-null-map-left-map-triangle is-null-g is-null-f =
    is-null-map-htpy' Y H (is-null-map-comp Y is-null-g is-null-f)

  is-null-map-top-map-triangle :
    is-null-map Y g → is-null-map Y h → is-null-map Y f
  is-null-map-top-map-triangle is-null-g is-null-h =
    is-null-map-right-factor Y is-null-g (is-null-map-htpy Y H is-null-h)
```

### Null maps are closed under dependent products

```agda
module _
  {l1 l2 l3 l4 : Level}
  (Y : UU l1) {I : UU l2} {A : I → UU l3} {B : I → UU l4}
  {f : (i : I) → A i → B i}
  where

  abstract
    is-null-map-Π : ((i : I) → is-null-map Y (f i)) → is-null-map Y (map-Π f)
    is-null-map-Π is-null-f =
      is-null-map-is-orthogonal-terminal-map Y (map-Π f)
      ( is-orthogonal-right-Π (terminal-map Y) f
        ( λ i → is-orthogonal-terminal-map-is-null-map Y (f i) (is-null-f i)))
```

### Null maps are closed under exponentiation

```agda
module _
  {l1 l2 l3 l4 : Level}
  (Y : UU l1) (I : UU l2) {A : UU l3} {B : UU l4} {f : A → B}
  where

  abstract
    is-null-map-postcomp : is-null-map Y f → is-null-map Y (postcomp I f)
    is-null-map-postcomp is-null-f =
      is-null-map-is-orthogonal-terminal-map Y (postcomp I f)
        ( is-orthogonal-right-postcomp I (terminal-map Y) f
          ( is-orthogonal-terminal-map-is-null-map Y f is-null-f))
```

### Null maps are closed under cartesian products

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (Y : UU l1) {A : UU l2} {B : UU l3} {C : UU l4} {D : UU l5}
  {f : A → B} {g : C → D}
  where

  abstract
    is-null-map-product :
      is-null-map Y f → is-null-map Y g → is-null-map Y (map-product f g)
    is-null-map-product is-null-f is-null-g =
      is-null-map-is-orthogonal-terminal-map Y (map-product f g)
        ( is-orthogonal-right-product (terminal-map Y) f g
          ( is-orthogonal-terminal-map-is-null-map Y f is-null-f)
          ( is-orthogonal-terminal-map-is-null-map Y g is-null-g))
```
