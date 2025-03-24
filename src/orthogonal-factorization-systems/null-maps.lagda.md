# Null maps

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module orthogonal-factorization-systems.null-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams funext
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.equivalences-arrows funext univalence truncations
open import foundation.families-of-equivalences funext
open import foundation.fibers-of-maps funext
open import foundation.function-types funext
open import foundation.functoriality-fibers-of-maps funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.logical-equivalences funext
open import foundation.morphisms-arrows funext
open import foundation.postcomposition-functions funext
open import foundation.precomposition-functions funext
open import foundation.propositions funext univalence
open import foundation.pullbacks funext univalence truncations
open import foundation.type-arithmetic-unit-type funext
open import foundation.type-theoretic-principle-of-choice funext
open import foundation.unit-type
open import foundation.universal-property-family-of-fibers-of-maps funext
open import foundation.universe-levels

open import foundation-core.diagonal-maps-of-types

open import orthogonal-factorization-systems.maps-local-at-maps funext univalence truncations
open import orthogonal-factorization-systems.null-families-of-types funext univalence truncations
open import orthogonal-factorization-systems.null-types funext univalence truncations
open import orthogonal-factorization-systems.orthogonal-maps funext univalence truncations
open import orthogonal-factorization-systems.types-local-at-maps funext univalence truncations
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

### A map is `Y`-null if and only if the terminal projection of `Y` is orthogonal to `f`

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
