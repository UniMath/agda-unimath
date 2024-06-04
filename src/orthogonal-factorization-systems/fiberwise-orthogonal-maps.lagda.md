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
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
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
open import foundation.postcomposition-pullbacks
open import foundation.precomposition-functions
open import foundation.products-pullbacks
open import foundation.propositions
open import foundation.pullbacks
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-dependent-function-types
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.local-types
open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.orthogonal-maps
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "fiberwise left orthogonal" Disambiguation="maps of types" Agda=is-fiberwise-orthogonal-pullback-condition}}
to `g : X → Y` if every [base change](foundation.cartesian-morphisms-arrows.md)
of `f` is [left orthogonal](orthogonal-factorization-systems.md) to `g`.

More concretely, `f` _is fiberwise left orthogonal to_ `g` if for every
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
    H {A' = A'} f' α =
    universal-property-pullback-is-pullback
      ( precomp f' Y)
      ( postcomp A' g)
      ( cone-pullback-hom f' g)
      ( H f' α)

  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-maps :
    universal-property-fiberwise-orthogonal-maps f g →
    is-fiberwise-orthogonal-pullback-condition f g
  is-fiberwise-orthogonal-pullback-condition-universal-property-fiberwise-orthogonal-maps
    H {A' = A'} f' α =
    is-pullback-universal-property-pullback
      ( precomp f' Y)
      ( postcomp A' g)
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
  where

  is-fiberwise-orthogonal-pullback-condition-htpy-left :
    {f f' : A → B} (F' : f' ~ f) (g : X → Y) →
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f' g
  is-fiberwise-orthogonal-pullback-condition-htpy-left F' g H f'' α =
    H f'' (cartesian-hom-arrow-htpy refl-htpy F' α)

  is-fiberwise-orthogonal-pullback-condition-htpy-right :
    (f : A → B) {g g' : X → Y} (G : g ~ g') →
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f g'
  is-fiberwise-orthogonal-pullback-condition-htpy-right f {g} G H f'' α =
    is-orthogonal-pullback-condition-htpy-right f'' g G (H f'' α)

  is-fiberwise-orthogonal-pullback-condition-htpy :
    {f f' : A → B} (F' : f' ~ f) {g g' : X → Y} (G : g ~ g') →
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f' g'
  is-fiberwise-orthogonal-pullback-condition-htpy {f} {f'} F' {g} G H =
    is-fiberwise-orthogonal-pullback-condition-htpy-right f' G
      ( is-fiberwise-orthogonal-pullback-condition-htpy-left F' g H)
```

### Equivalences are fiberwise left and right orthogonal to every map

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-fiberwise-orthogonal-pullback-condition-is-equiv-left :
    is-equiv f →
    is-fiberwise-orthogonal-pullback-condition f g
  is-fiberwise-orthogonal-pullback-condition-is-equiv-left F f' α =
    is-orthogonal-pullback-condition-is-equiv-left f' g
      ( is-equiv-source-is-equiv-target-cartesian-hom-arrow f' f α F)

  is-fiberwise-orthogonal-pullback-condition-is-equiv-right :
    is-equiv g →
    is-fiberwise-orthogonal-pullback-condition f g
  is-fiberwise-orthogonal-pullback-condition-is-equiv-right G f' _ =
    is-orthogonal-pullback-condition-is-equiv-right f' g G

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A ≃ B) (g : X → Y)
  where

  is-fiberwise-orthogonal-pullback-condition-equiv-left :
    is-fiberwise-orthogonal-pullback-condition (map-equiv f) g
  is-fiberwise-orthogonal-pullback-condition-equiv-left =
    is-fiberwise-orthogonal-pullback-condition-is-equiv-left
      ( map-equiv f)
      ( g)
      ( is-equiv-map-equiv f)

module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X ≃ Y)
  where

  is-fiberwise-orthogonal-pullback-condition-equiv-right :
    is-fiberwise-orthogonal-pullback-condition f (map-equiv g)
  is-fiberwise-orthogonal-pullback-condition-equiv-right =
    is-fiberwise-orthogonal-pullback-condition-is-equiv-right
      ( f)
      ( map-equiv g)
      ( is-equiv-map-equiv g)
```

### If `g` is fiberwise right orthogonal to `f` then it is null at the fibers of `f`

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-null-map-fibers-is-fiberwise-orthogonal-pullback-condition :
    is-fiberwise-orthogonal-pullback-condition f g →
    (y : B) → is-null-map (fiber f y) g
  is-null-map-fibers-is-fiberwise-orthogonal-pullback-condition H y =
    is-null-map-is-orthogonal-pullback-condition-terminal-map
      ( fiber f y)
      ( g)
      ( H (terminal-map (fiber f y)) (fiber-cartesian-hom-arrow f y))
```

### Closure properties of right fiberwise orthogonal maps

#### The right class is closed under composition and left cancellation

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {Z : UU l5}
  (f : A → B) (g : X → Y) (h : Y → Z)
  where

  is-fiberwise-orthogonal-pullback-condition-right-comp :
    is-fiberwise-orthogonal-pullback-condition f h →
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f (h ∘ g)
  is-fiberwise-orthogonal-pullback-condition-right-comp H G f' α =
    is-orthogonal-pullback-condition-right-comp f' g h (H f' α) (G f' α)

  is-fiberwise-orthogonal-pullback-condition-right-right-factor :
    is-fiberwise-orthogonal-pullback-condition f h →
    is-fiberwise-orthogonal-pullback-condition f (h ∘ g) →
    is-fiberwise-orthogonal-pullback-condition f g
  is-fiberwise-orthogonal-pullback-condition-right-right-factor H HG f' α =
    is-orthogonal-pullback-condition-right-right-factor f' g h
      ( H f' α)
      ( HG f' α)
```

#### The right class is closed under dependent products

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : UU l2} {B : UU l3} {X : I → UU l4} {Y : I → UU l5}
  (f : A → B) (g : (i : I) → X i → Y i)
  where

  is-fiberwise-orthogonal-pullback-condition-right-Π :
    ((i : I) → is-fiberwise-orthogonal-pullback-condition f (g i)) →
    is-fiberwise-orthogonal-pullback-condition f (map-Π g)
  is-fiberwise-orthogonal-pullback-condition-right-Π G f' α =
    is-orthogonal-pullback-condition-right-Π f' g (λ i → G i f' α)
```

#### The right class is closed under exponentiation

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} (S : UU l5)
  (f : A → B) (g : X → Y)
  where

  is-fiberwise-orthogonal-pullback-condition-right-postcomp :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f (postcomp S g)
  is-fiberwise-orthogonal-pullback-condition-right-postcomp G f' α =
    is-orthogonal-pullback-condition-right-postcomp S f' g (G f' α)
```

#### The right class is closed under cartesian products

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {X' : UU l5} {Y' : UU l6}
  (f : A → B) (g : X → Y) (g' : X' → Y')
  where

  is-fiberwise-orthogonal-pullback-condition-right-product :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f g' →
    is-fiberwise-orthogonal-pullback-condition f (map-product g g')
  is-fiberwise-orthogonal-pullback-condition-right-product G G' f' α =
    is-orthogonal-pullback-condition-right-product f' g g' (G f' α) (G' f' α)
```

#### The right class is closed under base change

Given a base change of `g`

```text
    X' -----> X
    | ⌟       |
  g'|         | g
    ∨         ∨
    Y' -----> Y,
```

if `g` is fiberwise right orthogonal to `f`, then `g'` is fiberwise right
orthogonal to `f`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {X' : UU l5} {Y' : UU l6}
  (f : A → B) (g : X → Y) (g' : X' → Y') (β : cartesian-hom-arrow g' g)
  where

  is-fiberwise-orthogonal-pullback-condition-right-base-change :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f g'
  is-fiberwise-orthogonal-pullback-condition-right-base-change G f' α =
    is-orthogonal-pullback-condition-right-base-change f' g g' β (G f' α)
```

### Closure properties of left fiberwise orthogonal maps

#### The left class is closed under composition and have the right cancellation property

This remains to be formalized.

#### The left class is closed under coproducts

This remains to be formalized.

#### The left class is preserved under base change

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {A' : UU l5} {B' : UU l6}
  (f : A → B) (g : X → Y) (f' : A' → B') (α : cartesian-hom-arrow f' f)
  where

  is-fiberwise-orthogonal-pullback-condition-left-base-change :
    is-fiberwise-orthogonal-pullback-condition f g →
    is-fiberwise-orthogonal-pullback-condition f' g
  is-fiberwise-orthogonal-pullback-condition-left-base-change H f'' α' =
    H f'' (comp-cartesian-hom-arrow f'' f' f α α')
```

#### The left class is closed under cobase change

This remains to be formalized.

#### The left class is closed transfininte composition

This remains to be formalized.

#### The left class is closed under cartesian products

This remains to be formalized.

#### The left class is closed under taking image inclusions

This remains to be formalized.

## References

- Reid Barton's note on _Internal cd-structures_
  ([GitHub upload](https://github.com/UniMath/agda-unimath/files/13429800/cd1.pdf))
