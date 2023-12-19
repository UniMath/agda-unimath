# Orthogonal maps

```agda
module orthogonal-factorization-systems.orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-maps
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
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.pullbacks
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import orthogonal-factorization-systems.lifting-squares
open import orthogonal-factorization-systems.pullback-hom
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "orthogonal" Disambiguation="maps of types" Agda=is-orthogonal}} to
`g : X → Y` if any of the following equivalent definitions hold

1. Their [pullback-hom](orthogonal-factorization-systems.pullback-hom.md) is an
   equivalence.

2. There is a unique
   [lifting operation](orthogonal-factorization-systems.lifting-operations.md)
   between `f` and `g`.

3. The following is a [pullback square](foundation.pullback-squares.md):
   ```text
                - ∘ f
         B → X -------> A → X
           |              |
     g ∘ - |              | g ∘ -
           V              V
         B → Y -------> A → Y.
                - ∘ f
   ```

If `f` is orthogonal to `g`, we say that `f` is
{{#concept "left orthogonal" Disambiguation="maps of types" Agda=is-left-orthogonal}}
to `g` and `g` is
{{#concept "right orthogonal" Disambiguation="maps of types" Agda=is-right-orthogonal}}
to `f`.

## Definitions

### The orthogonality predicate

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal = is-equiv (pullback-hom f g)

  _⊥_ = is-orthogonal

  is-prop-is-orthogonal : is-prop is-orthogonal
  is-prop-is-orthogonal = is-property-is-equiv (pullback-hom f g)

  is-orthogonal-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-orthogonal-Prop = is-orthogonal
  pr2 is-orthogonal-Prop = is-prop-is-orthogonal
```

A term of `is-right-orthogonal f g` asserts that `g` is right orthogonal to `f`.

```agda
  is-right-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-right-orthogonal = is-orthogonal
```

A term of `is-left-orthogonal f g` asserts that `g` is left orthogonal to `f`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-left-orthogonal : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-left-orthogonal = is-orthogonal g f
```

### The pullback condition for orthogonal maps

The maps `f` and `g` are orthogonal if and only if the square

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B → Y -------> A → Y.
             - ∘ f
```

is a pullback.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal-pullback-condition =
    is-pullback (precomp f Y) (postcomp A g) (cone-pullback-hom' f g)

  is-orthogonal-pullback-condition-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal-pullback-condition-Prop =
    is-pullback-Prop (precomp f Y) (postcomp A g) (cone-pullback-hom' f g)

  is-prop-is-orthogonal-pullback-condition :
    is-prop is-orthogonal-pullback-condition
  is-prop-is-orthogonal-pullback-condition =
    is-property-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
```

### The universal property of orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-orthogonal-maps : UUω
  universal-property-orthogonal-maps =
    universal-property-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
```

## Properties

### Being orthogonal means that the type of lifting squares is contractible

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  unique-lifting-squares-is-orthogonal :
    is-orthogonal f g →
    (h : fibered-map f g) →
    is-contr (lifting-square-fibered-map f g h)
  unique-lifting-squares-is-orthogonal H h =
    is-contr-equiv
      ( fiber (pullback-hom f g) h)
      ( compute-fiber-pullback-hom f g h)
      ( is-contr-map-is-equiv H h)

  is-orthogonal-unique-lifting-squares :
    ( (h : fibered-map f g) → is-contr (lifting-square-fibered-map f g h)) →
    is-orthogonal f g
  is-orthogonal-unique-lifting-squares H =
    is-equiv-is-contr-map
      ( λ h →
        is-contr-equiv'
          ( lifting-square-fibered-map f g h)
          ( compute-fiber-pullback-hom f g h)
          ( H h))
```

### Being orthogonal means satisfying the pullback condition of being orthogonal maps

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-is-orthogonal :
    is-orthogonal f g → is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-orthogonal =
    is-equiv-right-factor
      ( map-fibered-map-type-standard-pullback-hom f g)
      ( gap (precomp f Y) (postcomp A g) (cone-pullback-hom' f g))
      ( is-equiv-map-equiv (equiv-fibered-map-type-standard-pullback-hom f g))

  is-orthogonal-is-orthogonal-pullback-condition :
    is-orthogonal-pullback-condition f g → is-orthogonal f g
  is-orthogonal-is-orthogonal-pullback-condition H =
    is-equiv-comp
      ( map-fibered-map-type-standard-pullback-hom f g)
      ( gap (precomp f Y) (postcomp A g) (cone-pullback-hom' f g))
      ( H)
      ( is-equiv-map-equiv (equiv-fibered-map-type-standard-pullback-hom f g))
```

### Being orthogonal means satisfying the universal property of being orthogonal

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  universal-property-orthogonal-maps-is-orthogonal :
    is-orthogonal f g → universal-property-orthogonal-maps f g
  universal-property-orthogonal-maps-is-orthogonal H =
    universal-property-pullback-is-pullback
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( is-orthogonal-pullback-condition-is-orthogonal f g H)

  is-orthogonal-universal-property-orthogonal-maps :
    universal-property-orthogonal-maps f g → is-orthogonal f g
  is-orthogonal-universal-property-orthogonal-maps H =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-pullback-universal-property-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom' f g)
        ( H))
```

### Right orthogonal maps are closed under composition and have the right cancellation property

Given two composable maps `h` after `g`, if `h` is right orthogonal to `f` then
`g` is right orthogonal to `f` if and only if `h ∘ g` is.

**Proof:** By the pullback condition of orthogonal maps, the top square in the
below diagram is a pullback precisely when `g` is right orthogonal to `f`:

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        V              V
      B → Y -------> A → Y
        | ⌟            |
  h ∘ - |              | h ∘ -
        V              V
      B → Z -------> A → Z.
             - ∘ f
```

so the result is an instance of the vertical pasting property for pullbacks.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {Z : UU l5}
  (f : A → B) (g : X → Y) (h : Y → Z)
  where

  is-orthogonal-pullback-condition-right-comp :
    is-orthogonal-pullback-condition f h →
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f (h ∘ g)
  is-orthogonal-pullback-condition-right-comp =
    is-pullback-rectangle-is-pullback-top
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  up-orthogonal-right-comp :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps f (h ∘ g)
  up-orthogonal-right-comp =
    up-pullback-rectangle-up-pullback-top
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  is-orthogonal-right-comp :
    is-orthogonal f h → is-orthogonal f g → is-orthogonal f (h ∘ g)
  is-orthogonal-right-comp H G =
    is-orthogonal-is-orthogonal-pullback-condition f (h ∘ g)
      ( is-orthogonal-pullback-condition-right-comp
        ( is-orthogonal-pullback-condition-is-orthogonal f h H)
        ( is-orthogonal-pullback-condition-is-orthogonal f g G))

  is-orthogonal-pullback-condition-right-right-factor :
    is-orthogonal-pullback-condition f h →
    is-orthogonal-pullback-condition f (h ∘ g) →
    is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-right-right-factor =
    is-pullback-top-is-pullback-rectangle
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  up-orthogonal-right-right-factor :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f (h ∘ g) →
    universal-property-orthogonal-maps f g
  up-orthogonal-right-right-factor =
    up-pullback-top-up-pullback-rectangle
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom' f h)
      ( cone-pullback-hom' f g)

  is-orthogonal-right-right-factor :
    is-orthogonal f h → is-orthogonal f (h ∘ g) → is-orthogonal f g
  is-orthogonal-right-right-factor H HG =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-right-right-factor
        ( is-orthogonal-pullback-condition-is-orthogonal f h H)
        ( is-orthogonal-pullback-condition-is-orthogonal f (h ∘ g) HG))
```

### Left orthogonal maps are closed under composition and have the left cancellation property

Given two composable maps `h` after `f`, if `f` is left orthogonal to `g` then
`h` is left orthogonal to `g` if and only if `h ∘ f` is.

**Proof:** By the universal property of orthogonal maps, the right square in the
below diagram is a pullback precisely when `f` is left orthogonal to `g`:

```text
             - ∘ h          - ∘ f
      C → X -------> B → X -------> A → X
        |              | ⌟            |
  g ∘ - |              |              | g ∘ -
        V              V              V
      C → Y -------> B → Y -------> A → Y
             - ∘ h          - ∘ f
```

so the result is an instance of the horizontal pasting property for pullbacks.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {C : UU l5}
  (f : A → B) (h : B → C) (g : X → Y)
  where

  is-orthogonal-pullback-condition-left-comp :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition h g →
    is-orthogonal-pullback-condition (h ∘ f) g
  is-orthogonal-pullback-condition-left-comp =
    is-pullback-rectangle-is-pullback-left-square
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  up-orthogonal-left-comp :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps h g →
    universal-property-orthogonal-maps (h ∘ f) g
  up-orthogonal-left-comp =
    up-pullback-rectangle-up-pullback-left-square
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  is-orthogonal-left-comp :
    is-orthogonal f g → is-orthogonal h g → is-orthogonal (h ∘ f) g
  is-orthogonal-left-comp F H =
    is-orthogonal-is-orthogonal-pullback-condition (h ∘ f) g
      ( is-orthogonal-pullback-condition-left-comp
        ( is-orthogonal-pullback-condition-is-orthogonal f g F)
        ( is-orthogonal-pullback-condition-is-orthogonal h g H))

  is-orthogonal-pullback-condition-left-left-factor :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition (h ∘ f) g →
    is-orthogonal-pullback-condition h g
  is-orthogonal-pullback-condition-left-left-factor =
    is-pullback-left-square-is-pullback-rectangle
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  up-orthogonal-left-left-factor :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps (h ∘ f) g →
    universal-property-orthogonal-maps h g
  up-orthogonal-left-left-factor =
    up-pullback-left-square-up-pullback-rectangle
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom' f g)
      ( cone-pullback-hom' h g)

  is-orthogonal-left-left-factor :
    is-orthogonal f g → is-orthogonal (h ∘ f) g → is-orthogonal h g
  is-orthogonal-left-left-factor F HF =
    is-orthogonal-is-orthogonal-pullback-condition h g
      ( is-orthogonal-pullback-condition-left-left-factor
        ( is-orthogonal-pullback-condition-is-orthogonal f g F)
        ( is-orthogonal-pullback-condition-is-orthogonal (h ∘ f) g HF))
```

### The dependent product of a family of maps that are right orthogonal to `f` is again right orthogonal to `f`

In other words, if each `g i` is right orthogonal to `f`, then `map-Π g` is
right orthogonal to `f`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : UU l2} {B : UU l3} {X : I → UU l4} {Y : I → UU l5}
  (f : A → B) (g : (i : I) → X i → Y i)
  where

  is-orthogonal-pullback-condition-right-Π :
    ((i : I) → is-orthogonal-pullback-condition f (g i)) →
    is-orthogonal-pullback-condition f (map-Π g)
  is-orthogonal-pullback-condition-right-Π H =
    is-pullback-bottom-is-pullback-top-cube-is-equiv
      ( postcomp B (map-Π g))
      ( precomp f ((i : I) → X i))
      ( precomp f ((i : I) → Y i))
      ( postcomp A (map-Π g))
      ( map-Π (λ i → postcomp B (g i)))
      ( map-Π (λ i → precomp f (X i)))
      ( map-Π (λ i → precomp f (Y i)))
      ( map-Π (λ i → postcomp A (g i)))
      ( swap-Π)
      ( swap-Π)
      ( swap-Π)
      ( swap-Π)
      ( λ _ → eq-htpy refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( ( ap swap-Π) ·l
        ( eq-htpy-refl-htpy ∘ map-Π (λ i → precomp f (Y i) ∘ postcomp B (g i))))
      ( is-equiv-swap-Π)
      ( is-equiv-swap-Π)
      ( is-equiv-swap-Π)
      ( is-equiv-swap-Π)
      ( is-pullback-Π
        ( λ i → precomp f (Y i))
        ( λ i → postcomp A (g i))
        ( λ i → cone-pullback-hom' f (g i))
        ( H))

  is-orthogonal-right-Π :
    ((i : I) → is-orthogonal f (g i)) → is-orthogonal f (map-Π g)
  is-orthogonal-right-Π H =
    is-orthogonal-is-orthogonal-pullback-condition f (map-Π g)
      ( is-orthogonal-pullback-condition-right-Π
        ( λ i → is-orthogonal-pullback-condition-is-orthogonal f (g i) (H i)))
```

### If `g` is right orthogonal to `f` then postcomposition by `g` is right orthogonal to `f`

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} (I : UU l5)
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-right-postcomp :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f (postcomp I g)
  is-orthogonal-pullback-condition-right-postcomp H =
    is-orthogonal-pullback-condition-right-Π f (λ _ → g) (λ _ → H)

  is-orthogonal-right-postcomp :
    is-orthogonal f g → is-orthogonal f (postcomp I g)
  is-orthogonal-right-postcomp H =
    is-orthogonal-right-Π f (λ _ → g) (λ _ → H)
```
