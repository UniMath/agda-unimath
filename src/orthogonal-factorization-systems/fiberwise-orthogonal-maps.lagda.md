# Fiberwise orthogonal maps

```agda
module orthogonal-factorization-systems.fiberwise-orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.colocal-types
open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "fiberwise orthogonal" Disambiguation="maps of types" Agda=is-orthogonal}}
to `g : X → Y` if every [base change](foundation.cartesian-morphisms-arrows.md)
of `f` is [orthogonal](orthogonal-factorization-systems.md) to `g`.

More concretely, `f` _is fiberwise orthogonal to_ `g` if for every
[pullback](foundation-core.pullbacks.md) square

```text
    A' -------> A
    | ⌟         |
  f'|           | f
    ∨           ∨
    B' -------> B,
```

the exponential square

```text
             - ∘ f'
     B' → X -------> A' → X
        |               |
  g ∘ - |               | g ∘ -
        ∨               ∨
     B' → Y -------> A' → Y
             - ∘ f'
```

is also a pullback.

## Definitions

### The fiber condition for fiberwise orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-fiberwise-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-fiberwise-orthogonal =
    (y : B) → is-null-map (fiber f y) g
```

### The pullback condition for fiberwise orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-fiberwise-orthogonal-pullback-condition : UUω
  is-fiberwise-orthogonal-pullback-condition =
    {l5 l6 : Level} {A' : UU l5} {B' : UU l6}
    (f' : A' → B') (α : cartesian-hom-arrow f' f) →
    is-orthogonal-pullback-condition f' g
```

### The universal property of fiberwise orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-fiberwise-orthogonal-maps : UUω
  universal-property-fiberwise-orthogonal-maps =
    {l5 l6 : Level} {A' : UU l5} {B' : UU l6}
    (f' : A' → B') (α : cartesian-hom-arrow f' f) →
    universal-property-orthogonal-maps f' g
```

## Properties

### The fiber condition and the pullback condition for fiberwise orthogonal maps are equivalent

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-fiberwise-orthogonal-is-fiberwise-orthogonal-pullback-condition :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal f g
  is-fiberwise-orthogonal-is-fiberwise-orthogonal-pullback-condition H y =
    is-null-map-is-orthogonal-pullback-condition-terminal-map
      ( fiber f y)
      ( g)
      ( H (terminal-map (fiber f y)) (fiber-cartesian-hom-arrow f y))
```

The converse remains to be formalized.

### The pullback condition for fiberwise orthogonal maps is equivalent to the universal property

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-fiberwise-orthogonal-maps-is-fiberwise-orthogonal-pullback-condition :
    is-fiberwise-orthogonal-pullback-condition f g →
    universal-property-fiberwise-orthogonal-maps f g
  universal-property-fiberwise-orthogonal-maps-is-fiberwise-orthogonal-pullback-condition
    H f' α =
    universal-property-pullback-is-pullback
      ( precomp f' Y)
      ( postcomp _ g)
      ( cone-pullback-hom f' g)
      ( H f' α)

  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-maps :
    universal-property-fiberwise-orthogonal-maps f g →
    is-fiberwise-orthogonal-pullback-condition f g
  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-maps
    H f' α =
    is-pullback-universal-property-pullback
      ( precomp f' Y)
      ( postcomp _ g)
      ( cone-pullback-hom f' g)
      ( H f' α)
```

### Fiberwise orthogonal maps are orthogonal

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-is-fiberwise-orthogonal-pullback-condition :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-fiberwise-orthogonal-pullback-condition
    H =
    H f id-cartesian-hom-arrow
```

### Fiberwise orthogonality is preserved by homotopies

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g')
  where

  is-fiberwise-orthogonal-pullback-condition-htpy :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f' g'
  is-fiberwise-orthogonal-pullback-condition-htpy H f'' α =
    is-orthogonal-pullback-condition-htpy-right f'' g G
      ( H f'' (cartesian-hom-arrow-htpy refl-htpy F' α))
```

This remains to be formalized.

### Equivalences are fiberwise orthogonal to every map

This remains to be formalized.

### Fiberwise orthogonal maps are closed under composition and have the right cancellation property

This remains to be formalized.

### Fiberwise orthogonal maps are closed under coproducts

This remains to be formalized.

### Fiberwise orthogonality is preserved under base change

This remains to be formalized.

### Fiberwise orthogonal maps are closed under cobase change

This remains to be formalized.

### Fiberwise orthogonal maps are closed transfininte composition

This remains to be formalized.

### Fiberwise orthogonal maps are closed under coproducts

This remains to be formalized.

### Fiberwise orthogonal maps are closed under taking image inclusions

This remains to be formalized.
