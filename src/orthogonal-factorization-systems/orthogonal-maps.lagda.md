# Orthogonal maps

```agda
module orthogonal-factorization-systems.orthogonal-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.cartesian-product-types
open import foundation.composition-algebra
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.coproducts-pullbacks
open import foundation.dependent-pair-types
open import foundation.dependent-products-pullbacks
open import foundation.dependent-sums-pullbacks
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.fibered-maps
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.postcomposition-functions
open import foundation.postcomposition-pullbacks
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.products-pullbacks
open import foundation.propositions
open import foundation.pullbacks
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universal-property-equivalences
open import foundation.universal-property-pullbacks
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import orthogonal-factorization-systems.lifting-structures-on-squares
open import orthogonal-factorization-systems.pullback-hom
open import orthogonal-factorization-systems.types-local-at-maps

open import synthetic-homotopy-theory.cocartesian-morphisms-arrows
open import synthetic-homotopy-theory.pullback-property-pushouts
open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

The map `f : A → B` is said to be
{{#concept "orthogonal" Disambiguation="maps of types" Agda=is-orthogonal}} to
`g : X → Y` if any of the following equivalent definitions hold

1. Their [pullback-hom](orthogonal-factorization-systems.pullback-hom.md)
   `f ⋔ g` is an equivalence.

2. There is a [unique](foundation-core.contractible-types.md)
   [lifting operation](orthogonal-factorization-systems.lifting-operations.md)
   between `f` and `g`.

3. The following is a [pullback](foundation-core.pullbacks.md) square:

   ```text
                - ∘ f
         B → X -------> A → X
           |              |
     g ∘ - |              | g ∘ -
           ∨              ∨
         B → Y -------> A → Y.
                - ∘ f
   ```

4. The induced dependent precomposition map

   ```text
     - ∘ f : ((x : B) → fiber g (h x)) --> ((x : A) → fiber g (h (f x)))
   ```

   is an equivalence for every `h : B → Y`.

If `f` is orthogonal to `g`, we say that `f` is
{{#concept "left orthogonal" Disambiguation="maps of types" Agda=is-left-orthogonal}}
to `g`, and `g` is
{{#concept "right orthogonal" Disambiguation="maps of types" Agda=is-right-orthogonal}}
to `f`, and may write `f ⊥ g`.

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

  infix 6 _⊥_
  _⊥_ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
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
        ∨              ∨
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
    is-pullback (precomp f Y) (postcomp A g) (cone-pullback-hom f g)

  is-orthogonal-pullback-condition-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal-pullback-condition-Prop =
    is-pullback-Prop (precomp f Y) (postcomp A g) (cone-pullback-hom f g)

  is-prop-is-orthogonal-pullback-condition :
    is-prop is-orthogonal-pullback-condition
  is-prop-is-orthogonal-pullback-condition =
    is-prop-is-pullback (precomp f Y) (postcomp A g) (cone-pullback-hom f g)
```

### The universal property of orthogonal pairs of maps

The universal property of orthogonal maps is the universal property associated
to the pullback condition, which, as opposed to the pullback condition itself,
is a large proposition.

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
      ( cone-pullback-hom f g)
```

### The fiber condition for orthogonal maps

The maps `f` and `g` are orthogonal if and only if the induced family of maps on
fibers

```text
                           (- ∘ f)
   ((x : B) → fiber g (h x)) --> ((x : A) → fiber g (h (f x)))
                      |               |
                      |               |
                      ∨    (- ∘ f)    ∨
                   (B → X) ------> (A → X)
                      |               |
              (g ∘ -) |               | (g ∘ -)
                      ∨    (- ∘ f)    ∨
               h ∈ (B → Y) ------> (A → Y)
```

is an equivalence for every `h : B → Y`.

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-fiber-condition-right-map : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-orthogonal-fiber-condition-right-map =
    (h : B → Y) → is-equiv (precomp-Π f (fiber g ∘ h))
```

## Properties

### Being orthogonal means that the type of lifting squares is contractible

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  unique-lifting-structure-squares-is-orthogonal :
    is-orthogonal f g →
    (h : hom-arrow f g) →
    is-contr (lifting-structure-square f g h)
  unique-lifting-structure-squares-is-orthogonal H h =
    is-contr-equiv
      ( fiber (pullback-hom f g) h)
      ( compute-fiber-pullback-hom f g h)
      ( is-contr-map-is-equiv H h)

  is-orthogonal-unique-lifting-structure-squares :
    ( (h : hom-arrow f g) → is-contr (lifting-structure-square f g h)) →
    is-orthogonal f g
  is-orthogonal-unique-lifting-structure-squares H =
    is-equiv-is-contr-map
      ( λ h →
        is-contr-equiv'
          ( lifting-structure-square f g h)
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
  is-orthogonal-pullback-condition-is-orthogonal H =
    is-equiv-left-map-triangle
      ( gap-pullback-hom f g)
      ( map-compute-pullback-hom f g)
      ( pullback-hom f g)
      ( inv-htpy (triangle-pullback-hom f g))
      ( H)
      ( is-equiv-map-compute-pullback-hom f g)

  is-orthogonal-is-orthogonal-pullback-condition :
    is-orthogonal-pullback-condition f g → is-orthogonal f g
  is-orthogonal-is-orthogonal-pullback-condition =
    is-equiv-top-map-triangle
      ( gap-pullback-hom f g)
      ( map-compute-pullback-hom f g)
      ( pullback-hom f g)
      ( inv-htpy (triangle-pullback-hom f g))
      ( is-equiv-map-compute-pullback-hom f g)
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
      ( cone-pullback-hom f g)
      ( is-orthogonal-pullback-condition-is-orthogonal f g H)

  is-orthogonal-universal-property-orthogonal-maps :
    universal-property-orthogonal-maps f g → is-orthogonal f g
  is-orthogonal-universal-property-orthogonal-maps H =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-pullback-universal-property-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom f g)
        ( H))
```

### Being orthogonal means satisfying the fiber condition for orthogonal maps

**Proof.** The exponential square is a pullback if and only if the induced map
on fibers of the vertical maps

```text
  fiber (g ∘ -) h → fiber (g ∘ -) (h ∘ f)
```

is an equivalence for all `h`, and this map is equivalent to the relevant fiber
map

```text
                                      ~
      (Π (b : B), fiber g (h b)) ----------> fiber (g ∘ -) h
                  |                                 |
                  |                                 |
                  ∨                   ~             ∨
  (Π (a : A) → (fiber g (h (f a)))) ----> fiber (g ∘ -) (h ∘ f),
```

hence the fiber condition is satisfied if and only if `f` and `g` are
orthogonal.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-condition :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-fiber-condition-right-map f g
  is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-condition H h =
    is-equiv-source-is-equiv-target-equiv-arrow
      ( precomp-Π f (fiber g ∘ h))
      ( map-fiber-vertical-map-cone
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom f g)
        ( h))
      ( compute-map-fiber-vertical-pullback-hom f g h)
      ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( cone-pullback-hom f g)
        ( H)
        ( h))

  is-orthogonal-fiber-condition-right-map-is-orthogonal :
    is-orthogonal f g →
    is-orthogonal-fiber-condition-right-map f g
  is-orthogonal-fiber-condition-right-map-is-orthogonal H =
    is-orthogonal-fiber-condition-right-map-is-orthogonal-pullback-condition
      ( is-orthogonal-pullback-condition-is-orthogonal f g H)

  is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-map :
    is-orthogonal-fiber-condition-right-map f g →
    is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-map H =
    is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)
      ( λ h →
        is-equiv-target-is-equiv-source-equiv-arrow
          ( precomp-Π f (fiber g ∘ h))
          ( map-fiber-vertical-map-cone
            ( precomp f Y)
            ( postcomp A g)
            ( cone-pullback-hom f g)
            ( h))
          ( compute-map-fiber-vertical-pullback-hom f g h)
          ( H h))

  is-orthogonal-is-orthogonal-fiber-condition-right-map :
    is-orthogonal-fiber-condition-right-map f g →
    is-orthogonal f g
  is-orthogonal-is-orthogonal-fiber-condition-right-map H =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-is-orthogonal-fiber-condition-right-map
        ( H))
```

### Orthogonality is preserved by homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-htpy :
    {f' : A → B} {g' : X → Y} → f ~ f' → g ~ g' →
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f' g'
  is-orthogonal-pullback-condition-htpy F G =
    is-pullback-htpy'
      ( htpy-precomp F Y)
      ( htpy-postcomp A G)
      ( cone-pullback-hom f g)
      ( ( htpy-postcomp B G) ,
        ( htpy-precomp F X) ,
        ( ( commutative-htpy-postcomp-htpy-precomp F G) ∙h
          ( inv-htpy-right-unit-htpy)))

  abstract
    is-orthogonal-pullback-condition-htpy-left :
      {f' : A → B} → f ~ f' →
      is-orthogonal-pullback-condition f g →
      is-orthogonal-pullback-condition f' g
    is-orthogonal-pullback-condition-htpy-left F =
      is-orthogonal-pullback-condition-htpy F refl-htpy

  abstract
    is-orthogonal-pullback-condition-htpy-right :
      {g' : X → Y} → g ~ g' →
      is-orthogonal-pullback-condition f g →
      is-orthogonal-pullback-condition f g'
    is-orthogonal-pullback-condition-htpy-right =
      is-orthogonal-pullback-condition-htpy refl-htpy

  abstract
    is-orthogonal-htpy :
      {f' : A → B} {g' : X → Y} → f ~ f' → g ~ g' →
      is-orthogonal f g → is-orthogonal f' g'
    is-orthogonal-htpy {f'} {g'} F G H =
      is-orthogonal-is-orthogonal-pullback-condition f' g'
        ( is-orthogonal-pullback-condition-htpy F G
          ( is-orthogonal-pullback-condition-is-orthogonal f g H))

  abstract
    is-orthogonal-htpy-left :
      {f' : A → B} → f ~ f' → is-orthogonal f g → is-orthogonal f' g
    is-orthogonal-htpy-left F = is-orthogonal-htpy F refl-htpy

  abstract
    is-orthogonal-htpy-right :
      {g' : X → Y} → g ~ g' → is-orthogonal f g → is-orthogonal f g'
    is-orthogonal-htpy-right = is-orthogonal-htpy refl-htpy
```

### Equivalences are orthogonal to every map

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-is-equiv-left :
    is-equiv f → is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-equiv-left is-equiv-f =
    is-pullback-is-equiv-horizontal-maps
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)
      ( is-equiv-precomp-is-equiv f is-equiv-f Y)
      ( is-equiv-precomp-is-equiv f is-equiv-f X)

  is-orthogonal-is-equiv-left : is-equiv f → is-orthogonal f g
  is-orthogonal-is-equiv-left is-equiv-f =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-is-equiv-left is-equiv-f)

  is-orthogonal-pullback-condition-is-equiv-right :
    is-equiv g → is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-equiv-right is-equiv-g =
    is-pullback-is-equiv-vertical-maps
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)
      ( is-equiv-postcomp-is-equiv g is-equiv-g A)
      ( is-equiv-postcomp-is-equiv g is-equiv-g B)

  is-orthogonal-is-equiv-right : is-equiv g → is-orthogonal f g
  is-orthogonal-is-equiv-right is-equiv-g =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-is-equiv-right is-equiv-g)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  where

  is-orthogonal-pullback-condition-equiv-left :
    (f : A ≃ B) (g : X → Y) → is-orthogonal-pullback-condition (map-equiv f) g
  is-orthogonal-pullback-condition-equiv-left f g =
    is-orthogonal-pullback-condition-is-equiv-left
      ( map-equiv f)
      ( g)
      ( is-equiv-map-equiv f)

  is-orthogonal-equiv-left :
    (f : A ≃ B) (g : X → Y) → is-orthogonal (map-equiv f) g
  is-orthogonal-equiv-left f g =
    is-orthogonal-is-equiv-left (map-equiv f) g (is-equiv-map-equiv f)

  is-orthogonal-pullback-condition-equiv-right :
    (f : A → B) (g : X ≃ Y) → is-orthogonal-pullback-condition f (map-equiv g)
  is-orthogonal-pullback-condition-equiv-right f g =
    is-orthogonal-pullback-condition-is-equiv-right
      ( f)
      ( map-equiv g)
      ( is-equiv-map-equiv g)

  is-orthogonal-equiv-right :
    (f : A → B) (g : X ≃ Y) → is-orthogonal f (map-equiv g)
  is-orthogonal-equiv-right f g =
    is-orthogonal-is-equiv-right f (map-equiv g) (is-equiv-map-equiv g)
```

### Right orthogonal maps are closed under composition and have the left cancellation property

Given two composable maps `h` after `g`, if `f ⊥ h`, then `f ⊥ g` if and only if
`f ⊥ (h ∘ g)`.

**Proof:** By the pullback condition of orthogonal maps, the top square in the
below diagram is a pullback precisely when `g` is right orthogonal to `f`:

```text
             - ∘ f
      B → X -------> A → X
        |              |
  g ∘ - |              | g ∘ -
        ∨              ∨
      B → Y -------> A → Y
        | ⌟            |
  h ∘ - |              | h ∘ -
        ∨              ∨
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
    is-pullback-rectangle-is-pullback-top-square
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom f h)
      ( cone-pullback-hom f g)

  up-orthogonal-right-comp :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps f (h ∘ g)
  up-orthogonal-right-comp =
    universal-property-pullback-rectangle-universal-property-pullback-top
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom f h)
      ( cone-pullback-hom f g)

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
    is-pullback-top-square-is-pullback-rectangle
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom f h)
      ( cone-pullback-hom f g)

  up-orthogonal-right-right-factor :
    universal-property-orthogonal-maps f h →
    universal-property-orthogonal-maps f (h ∘ g) →
    universal-property-orthogonal-maps f g
  up-orthogonal-right-right-factor =
    universal-property-pullback-top-universal-property-pullback-rectangle
      ( precomp f Z)
      ( postcomp A h)
      ( postcomp A g)
      ( cone-pullback-hom f h)
      ( cone-pullback-hom f g)

  is-orthogonal-right-right-factor :
    is-orthogonal f h → is-orthogonal f (h ∘ g) → is-orthogonal f g
  is-orthogonal-right-right-factor H HG =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-right-right-factor
        ( is-orthogonal-pullback-condition-is-orthogonal f h H)
        ( is-orthogonal-pullback-condition-is-orthogonal f (h ∘ g) HG))
```

### Left orthogonal maps are closed under composition and have the right cancellation property

Given two composable maps `h` after `f`, if `f ⊥ g`, then `h ⊥ g` if and only if
`(h ∘ f) ⊥ g`.

**Proof:** By the universal property of orthogonal maps, the right square in the
below diagram is a pullback precisely when `f` is left orthogonal to `g`:

```text
             - ∘ h          - ∘ f
      C → X -------> B → X -------> A → X
        |              | ⌟            |
  g ∘ - |              |              | g ∘ -
        ∨              ∨              ∨
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
      ( cone-pullback-hom f g)
      ( cone-pullback-hom h g)

  up-orthogonal-left-comp :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps h g →
    universal-property-orthogonal-maps (h ∘ f) g
  up-orthogonal-left-comp =
    universal-property-pullback-rectangle-universal-property-pullback-left-square
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)
      ( cone-pullback-hom h g)

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
      ( cone-pullback-hom f g)
      ( cone-pullback-hom h g)

  up-orthogonal-left-left-factor :
    universal-property-orthogonal-maps f g →
    universal-property-orthogonal-maps (h ∘ f) g →
    universal-property-orthogonal-maps h g
  up-orthogonal-left-left-factor =
    universal-property-pullback-left-square-universal-property-pullback-rectangle
      ( precomp h Y)
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)
      ( cone-pullback-hom h g)

  is-orthogonal-left-left-factor :
    is-orthogonal f g → is-orthogonal (h ∘ f) g → is-orthogonal h g
  is-orthogonal-left-left-factor F HF =
    is-orthogonal-is-orthogonal-pullback-condition h g
      ( is-orthogonal-pullback-condition-left-left-factor
        ( is-orthogonal-pullback-condition-is-orthogonal f g F)
        ( is-orthogonal-pullback-condition-is-orthogonal (h ∘ f) g HF))
```

### Orthogonality is preserved by equivalences of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4} {X : UU l5} {Y : UU l6}
  {f : A → B} {f' : A' → B'}
  where

  abstract
    is-orthogonal-left-equiv-arrow :
      equiv-arrow f f' → (g : X → Y) → is-orthogonal f g → is-orthogonal f' g
    is-orthogonal-left-equiv-arrow α g F =
      is-orthogonal-htpy-left
        ( map-codomain-equiv-arrow f f' α ∘
          f ∘
          map-inv-domain-equiv-arrow f f' α)
        ( g)
        ( ( coh-equiv-arrow f f' α ·r map-inv-domain-equiv-arrow f f' α) ∙h
          ( f' ·l is-section-map-inv-equiv (equiv-domain-equiv-arrow f f' α)))
        ( is-orthogonal-left-comp
          ( f ∘ map-inv-domain-equiv-arrow f f' α)
          ( map-codomain-equiv-arrow f f' α)
          ( g)
          ( is-orthogonal-left-comp
            ( map-inv-domain-equiv-arrow f f' α)
            ( f)
            ( g)
            ( is-orthogonal-equiv-left (equiv-domain-inv-equiv-arrow f f' α) g)
            ( F))
          ( is-orthogonal-equiv-left (equiv-codomain-equiv-arrow f f' α) g))

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {X' : UU l5} {Y' : UU l6}
  (f : A → B) {g : X → Y} {g' : X' → Y'}
  where

  abstract
    is-orthogonal-right-equiv-arrow :
      equiv-arrow g g' → is-orthogonal f g → is-orthogonal f g'
    is-orthogonal-right-equiv-arrow α G =
      is-orthogonal-htpy-right
        ( f)
        ( map-codomain-equiv-arrow g g' α ∘
          g ∘
          map-inv-domain-equiv-arrow g g' α)
        ( ( coh-equiv-arrow g g' α ·r map-inv-domain-equiv-arrow g g' α) ∙h
          ( g' ·l is-section-map-inv-equiv (equiv-domain-equiv-arrow g g' α)))
        ( is-orthogonal-right-comp
          ( f)
          ( g ∘ map-inv-domain-equiv-arrow g g' α)
          ( map-codomain-equiv-arrow g g' α)
          ( is-orthogonal-equiv-right f (equiv-codomain-equiv-arrow g g' α))
          ( is-orthogonal-right-comp
            ( f)
            ( map-inv-domain-equiv-arrow g g' α)
            ( g)
            ( G)
            ( is-orthogonal-equiv-right
              ( f)
              ( equiv-domain-inv-equiv-arrow g g' α))))
```

### Right orthogonality is preserved by dependent products

If `f ⊥ gᵢ`, for each `i : I`, then `f ⊥ (map-Π g)`.

**Proof:** We need to show that the square

```text
                          - ∘ f
         (B → Πᵢ Xᵢ) ---------------> (A → Πᵢ Xᵢ)
              |                           |
              |                           |
  map-Π g ∘ - |                           | map-Π g ∘ -
              |                           |
              ∨                           ∨
         (B → Πᵢ Yᵢ) ---------------> (A → Πᵢ Yᵢ)
                          - ∘ f
```

is a pullback. By swapping the arguments at each vertex, this square is
equivalent to

```text
                          map-Π (- ∘ f)
            (Πᵢ B → Xᵢ) ---------------> (Πᵢ A → Xᵢ)
                  |                           |
                  |                           |
   map-Π (gᵢ ∘ -) |                           | map-Π (gᵢ ∘ -)
                  |                           |
                  ∨                           ∨
            (Πᵢ B → Yᵢ) ---------------> (Πᵢ A → Yᵢ)
                          map-Π (- ∘ f)
```

which is a pullback by assumption since pullbacks are preserved by dependent
products.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : UU l2} {B : UU l3} {X : I → UU l4} {Y : I → UU l5}
  (f : A → B) (g : (i : I) → X i → Y i)
  where

  is-orthogonal-pullback-condition-right-Π :
    ((i : I) → is-orthogonal-pullback-condition f (g i)) →
    is-orthogonal-pullback-condition f (map-Π g)
  is-orthogonal-pullback-condition-right-Π G =
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
        ( λ i → cone-pullback-hom f (g i))
        ( G))

  is-orthogonal-right-Π :
    ((i : I) → is-orthogonal f (g i)) → is-orthogonal f (map-Π g)
  is-orthogonal-right-Π G =
    is-orthogonal-is-orthogonal-pullback-condition f (map-Π g)
      ( is-orthogonal-pullback-condition-right-Π
        ( λ i → is-orthogonal-pullback-condition-is-orthogonal f (g i) (G i)))
```

### Any map that is left orthogonal to a map `g` is also left orthogonal to postcomposing by `g`

If `f ⊥ g` then `f ⊥ postcomp S g` for every type `S`.

**Proof:** This is a special case of the previous result by taking `g` to be
constant over `S`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} (S : UU l5)
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-right-postcomp :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f (postcomp S g)
  is-orthogonal-pullback-condition-right-postcomp G =
    is-orthogonal-pullback-condition-right-Π f (λ _ → g) (λ _ → G)

  is-orthogonal-right-postcomp :
    is-orthogonal f g → is-orthogonal f (postcomp S g)
  is-orthogonal-right-postcomp G =
    is-orthogonal-right-Π f (λ _ → g) (λ _ → G)
```

### Right orthogonality is preserved by products

If `f ⊥ g` and `f ⊥ g'`, then `f ⊥ (g × g')`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {X' : UU l5} {Y' : UU l6}
  (f : A → B) (g : X → Y) (g' : X' → Y')
  where

  is-orthogonal-pullback-condition-right-product :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f g' →
    is-orthogonal-pullback-condition f (map-product g g')
  is-orthogonal-pullback-condition-right-product G G' =
    is-pullback-top-is-pullback-bottom-cube-is-equiv
      ( map-product (postcomp B g) (postcomp B g'))
      ( map-product (precomp f X) (precomp f X'))
      ( map-product (precomp f Y) (precomp f Y'))
      ( map-product (postcomp A g) (postcomp A g'))
      ( postcomp B (map-product g g'))
      ( precomp f (X × X'))
      ( precomp f (Y × Y'))
      ( postcomp A (map-product g g'))
      ( map-up-product)
      ( map-up-product)
      ( map-up-product)
      ( map-up-product)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( up-product)
      ( up-product)
      ( up-product)
      ( up-product)
      ( is-pullback-product-is-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( precomp f Y')
        ( postcomp A g')
        ( cone-pullback-hom f g)
        ( cone-pullback-hom f g')
        ( G)
        ( G'))

  is-orthogonal-right-product :
    is-orthogonal f g → is-orthogonal f g' → is-orthogonal f (map-product g g')
  is-orthogonal-right-product G G' =
    is-orthogonal-is-orthogonal-pullback-condition f (map-product g g')
      ( is-orthogonal-pullback-condition-right-product
        ( is-orthogonal-pullback-condition-is-orthogonal f g G)
        ( is-orthogonal-pullback-condition-is-orthogonal f g' G'))
```

### Left orthogonality is preserved by dependent sums

If `fᵢ ⊥ g` for every `i`, then `(tot f) ⊥ g`.

**Proof:** We need to show that the square

```text
                  - ∘ (tot f)
  ((Σ I B) → X) ---------------> ((Σ I A) → X)
        |                               |
        |                               |
  g ∘ - |                               | g ∘ -
        |                               |
        ∨                               ∨
  ((Σ I B) → Y) ---------------> ((Σ I A) → Y)
                  - ∘ (tot f)
```

is a pullback. However, by the universal property of dependent pair types this
square is equivalent to

```text
                    Πᵢ (- ∘ fᵢ)
        Πᵢ (Bᵢ → X) -----------> Πᵢ (Aᵢ → X)
             |                        |
             |                        |
  Πᵢ (g ∘ -) |                        | Πᵢ (g ∘ -)
             |                        |
             ∨                        ∨
        Πᵢ (Bᵢ → Y) -----------> Πᵢ (Aᵢ → Y),
                    Πᵢ (- ∘ fᵢ)
```

which is a pullback by assumption and the fact that pullbacks are preserved
under dependent products.

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} {X : UU l4} {Y : UU l5}
  (f : (i : I) → A i → B i) (g : X → Y)
  where

  is-orthogonal-pullback-condition-left-tot :
    ((i : I) → is-orthogonal-pullback-condition (f i) g) →
    is-orthogonal-pullback-condition (tot f) g
  is-orthogonal-pullback-condition-left-tot F =
    is-pullback-top-is-pullback-bottom-cube-is-equiv
      ( map-Π (λ i → postcomp (B i) g))
      ( map-Π (λ i → precomp (f i) X))
      ( map-Π (λ i → precomp (f i) Y))
      ( map-Π (λ i → postcomp (A i) g))
      ( postcomp (Σ I B) g)
      ( precomp (tot f) X)
      ( precomp (tot f) Y)
      ( postcomp (Σ I A) g)
      ( ev-pair)
      ( ev-pair)
      ( ev-pair)
      ( ev-pair)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( λ _ → eq-htpy refl-htpy)
      ( inv-htpy
        ( ( right-unit-htpy) ∙h
          ( ( eq-htpy-refl-htpy) ·r
            ( ( map-Π (λ i → precomp (f i) Y)) ∘
              ( map-Π (λ i → postcomp (B i) g)) ∘
              ( ev-pair)))))
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-pullback-Π
        ( λ i → precomp (f i) Y)
        ( λ i → postcomp (A i) g)
        ( λ i → cone-pullback-hom (f i) g)
        ( F))

  is-orthogonal-left-tot :
    ((i : I) → is-orthogonal (f i) g) → is-orthogonal (tot f) g
  is-orthogonal-left-tot F =
    is-orthogonal-is-orthogonal-pullback-condition (tot f) g
      ( is-orthogonal-pullback-condition-left-tot
        ( λ i → is-orthogonal-pullback-condition-is-orthogonal (f i) g (F i)))
```

### Left orthogonality is preserved by products

If `f ⊥ g` and `f' ⊥ g`, then `(f × f') ⊥ g`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-left-map-right-product :
    {l5 : Level} (C : UU l5) →
    is-orthogonal f g → is-orthogonal (map-product (id' C) f) g
  is-orthogonal-left-map-right-product C F =
    is-orthogonal-left-tot (λ _ → f) g (λ _ → F)

  is-orthogonal-left-map-left-product :
    {l5 : Level} (C : UU l5) →
    is-orthogonal f g → is-orthogonal (map-product f (id' C)) g
  is-orthogonal-left-map-left-product C F =
    is-orthogonal-left-equiv-arrow
      ( commutative-product , commutative-product , refl-htpy)
      ( g)
      ( is-orthogonal-left-map-right-product C F)

module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4} {X : UU l5} {Y : UU l6}
  (f : A → B) (f' : A' → B') (g : X → Y)
  where

  is-orthogonal-left-product :
    is-orthogonal f g → is-orthogonal f' g → is-orthogonal (map-product f f') g
  is-orthogonal-left-product F F' =
    is-orthogonal-left-comp
      ( map-product f id)
      ( map-product id f')
      ( g)
      ( is-orthogonal-left-map-left-product f g A' F)
      ( is-orthogonal-left-map-right-product f' g B F')
```

### Left orthogonality is preserved by coproducts

If `f ⊥ g` and `f' ⊥ g`, then `(f + f') ⊥ g`.

**Proof:** We need to show that the square

```text
                   - ∘ (f + f')
  ((B + B') → X) ---------------> ((A + A') → X)
        |                               |
        |                               |
  g ∘ - |                               | g ∘ -
        |                               |
        ∨                               ∨
  ((B + B') → Y) ---------------> ((A + A') → Y)
                   - ∘ (f + f')
```

is a pullback. However, by the universal property of coproducts this square is
equivalent to

```text
                            (- ∘ f) × (- ∘ f')
            (B → X) × (B' → X) -----------> (A → X) × (A' → X)
                    |                               |
                    |                               |
  (g ∘ -) × (g ∘ -) |                               | (g ∘ -) × (g ∘ -)
                    |                               |
                    ∨                               ∨
            (B → Y) × (B' → Y) -----------> (A → Y) × (A' → Y),
                            (- ∘ f) × (- ∘ f')
```

which is a pullback by assumption and the fact that pullbacks are preserved
under products.

**Note:** This result can also be obtained as a special case of the previous one
by taking the indexing type to be the
[two-element type](foundation.booleans.md).

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {A' : UU l3} {B' : UU l4} {X : UU l5} {Y : UU l6}
  (f : A → B) (f' : A' → B') (g : X → Y)
  where

  is-orthogonal-pullback-condition-left-coproduct :
    is-orthogonal-pullback-condition f g →
    is-orthogonal-pullback-condition f' g →
    is-orthogonal-pullback-condition (map-coproduct f f') g
  is-orthogonal-pullback-condition-left-coproduct F F' =
    is-pullback-top-is-pullback-bottom-cube-is-equiv
      ( map-product (postcomp B g) (postcomp B' g))
      ( map-product (precomp f X) (precomp f' X))
      ( map-product (precomp f Y) (precomp f' Y))
      ( map-product (postcomp A g) (postcomp A' g))
      ( postcomp (B + B') g)
      ( precomp (map-coproduct f f') X)
      ( precomp (map-coproduct f f') Y)
      ( postcomp (A + A') g)
      ( ev-inl-inr (λ _ → X))
      ( ev-inl-inr (λ _ → Y))
      ( ev-inl-inr (λ _ → X))
      ( ev-inl-inr (λ _ → Y))
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( refl-htpy)
      ( universal-property-coproduct X)
      ( universal-property-coproduct Y)
      ( universal-property-coproduct X)
      ( universal-property-coproduct Y)
      ( is-pullback-product-is-pullback
        ( precomp f Y)
        ( postcomp A g)
        ( precomp f' Y)
        ( postcomp A' g)
        ( cone-pullback-hom f g)
        ( cone-pullback-hom f' g)
        ( F)
        ( F'))

  is-orthogonal-left-coproduct :
    is-orthogonal f g →
    is-orthogonal f' g →
    is-orthogonal (map-coproduct f f') g
  is-orthogonal-left-coproduct F F' =
    is-orthogonal-is-orthogonal-pullback-condition (map-coproduct f f') g
      ( is-orthogonal-pullback-condition-left-coproduct
        ( is-orthogonal-pullback-condition-is-orthogonal f g F)
        ( is-orthogonal-pullback-condition-is-orthogonal f' g F'))
```

### Right orthogonality is preserved under base change

Given a pullback square

```text
    X' -----> X
    | ⌟       |
  g'|         | g
    ∨         ∨
    Y' -----> Y,
```

if `f ⊥ g`, then `f ⊥ g'`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {X' : UU l5} {Y' : UU l6}
  (f : A → B) (g : X → Y) (g' : X' → Y') (α : cartesian-hom-arrow g' g)
  where

  is-orthogonal-pullback-condition-right-base-change :
    is-orthogonal-pullback-condition f g → is-orthogonal-pullback-condition f g'
  is-orthogonal-pullback-condition-right-base-change G =
    is-pullback-back-right-is-pullback-back-left-cube
      ( refl-htpy)
      ( htpy-postcomp B (coh-cartesian-hom-arrow g' g α))
      ( refl-htpy)
      ( refl-htpy)
      ( htpy-postcomp A (coh-cartesian-hom-arrow g' g α))
      ( refl-htpy)
      ( ( right-unit-htpy) ∙h
        ( right-unit-htpy) ∙h
        ( inv-htpy
          ( commutative-precomp-htpy-postcomp
            ( f)
            ( coh-cartesian-hom-arrow g' g α))))
      ( G)
      ( is-pullback-postcomp-is-pullback
        ( map-codomain-cartesian-hom-arrow g' g α)
        ( g)
        ( cone-cartesian-hom-arrow g' g α)
        ( is-cartesian-cartesian-hom-arrow g' g α)
        ( A))
      ( is-pullback-postcomp-is-pullback
        ( map-codomain-cartesian-hom-arrow g' g α)
        ( g)
        ( cone-cartesian-hom-arrow g' g α)
        ( is-cartesian-cartesian-hom-arrow g' g α)
        ( B))

  is-orthogonal-right-base-change : is-orthogonal f g → is-orthogonal f g'
  is-orthogonal-right-base-change G =
    is-orthogonal-is-orthogonal-pullback-condition f g'
      ( is-orthogonal-pullback-condition-right-base-change
        ( is-orthogonal-pullback-condition-is-orthogonal f g G))
```

### Left orthogonality is preserved under cobase change

Given a pushout square

```text
    A ------> A'
    |         |
  f'|         | f'
    ∨       ⌜ ∨
    B ------> B',
```

if `f ⊥ g`, then `f' ⊥ g`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {A' : UU l5} {B' : UU l6}
  (f : A → B) (f' : A' → B') (g : X → Y) (α : cocartesian-hom-arrow f f')
  where

  abstract
    is-orthogonal-pullback-condition-left-cobase-change :
      is-orthogonal-pullback-condition f g →
      is-orthogonal-pullback-condition f' g
    is-orthogonal-pullback-condition-left-cobase-change F =
      is-pullback-swap-cone
        ( postcomp A' g)
        ( precomp f' Y)
        ( precomp f' X , postcomp B' g , refl-htpy)
        ( is-pullback-back-left-is-pullback-back-right-cube
          ( refl-htpy)
          ( refl-htpy)
          ( inv-htpy (htpy-precomp (coh-cocartesian-hom-arrow f f' α) X))
          ( inv-htpy (htpy-precomp (coh-cocartesian-hom-arrow f f' α) Y))
          ( refl-htpy)
          ( refl-htpy)
          ( right-unit-htpy ∙h
            ( inv ·l
              commutative-postcomp-htpy-precomp g
                ( coh-cocartesian-hom-arrow f f' α)) ∙h
            ( inv-htpy
              ( left-whisker-inv-htpy
                ( postcomp A g)
                ( htpy-precomp (coh-cocartesian-hom-arrow f f' α) X))) ∙h
            ( inv-htpy-right-unit-htpy))
          ( is-pullback-swap-cone
            ( precomp f Y)
            ( precomp (map-domain-cocartesian-hom-arrow f f' α) Y)
            ( cone-hom-arrow
              ( precomp (map-codomain-cocartesian-hom-arrow f f' α) Y)
              ( precomp (map-domain-cocartesian-hom-arrow f f' α) Y)
              ( transpose-precomp-hom-arrow f f'
                ( hom-arrow-cocartesian-hom-arrow f f' α)
                ( Y)))
            ( pullback-property-pushout-is-pushout
              ( f)
              ( map-domain-cocartesian-hom-arrow f f' α)
              ( cocone-cocartesian-hom-arrow f f' α)
              ( is-cocartesian-cocartesian-hom-arrow f f' α)
              ( Y)))
          ( is-pullback-swap-cone
            ( precomp f Y)
            ( postcomp A g)
            ( cone-pullback-hom f g)
            ( F))
          ( is-pullback-swap-cone
            ( precomp f X)
            ( precomp (map-domain-cocartesian-hom-arrow f f' α) X)
            ( cone-hom-arrow
              ( precomp (map-codomain-cocartesian-hom-arrow f f' α) X)
              ( precomp (map-domain-cocartesian-hom-arrow f f' α) X)
              ( transpose-precomp-hom-arrow f f'
                ( hom-arrow-cocartesian-hom-arrow f f' α)
                ( X)))
            ( pullback-property-pushout-is-pushout f
              ( map-domain-cocartesian-hom-arrow f f' α)
              ( cocone-cocartesian-hom-arrow f f' α)
              ( is-cocartesian-cocartesian-hom-arrow f f' α) X)))

    is-orthogonal-left-cobase-change :
      is-orthogonal f g → is-orthogonal f' g
    is-orthogonal-left-cobase-change F =
      is-orthogonal-is-orthogonal-pullback-condition f' g
        ( is-orthogonal-pullback-condition-left-cobase-change
          ( is-orthogonal-pullback-condition-is-orthogonal f g F))
```

### A type is `f`-local if and only if its terminal map is `f`-orthogonal

**Proof (forward direction):** If the terminal map is right orthogonal to `f`,
that means we have a pullback square

```text
            - ∘ f
      B → X -----> A → X
        | ⌟          |
  ! ∘ - |            | ! ∘ -
        ∨            ∨
      B → 1 -----> A → 1.
            - ∘ f
```

which displays `precomp f X` as a pullback of an equivalence, hence it is itself
an equivalence.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (f : A → B)
  where

  is-local-is-orthogonal-pullback-condition-terminal-map :
    is-orthogonal-pullback-condition f (terminal-map X) → is-local f X
  is-local-is-orthogonal-pullback-condition-terminal-map =
    is-equiv-horizontal-map-is-pullback
      ( precomp f unit)
      ( postcomp A (terminal-map X))
      ( cone-pullback-hom f (terminal-map X))
      ( is-local-is-contr f unit is-contr-unit)

  is-local-is-orthogonal-terminal-map :
    is-orthogonal f (terminal-map X) → is-local f X
  is-local-is-orthogonal-terminal-map F =
    is-local-is-orthogonal-pullback-condition-terminal-map
      ( is-orthogonal-pullback-condition-is-orthogonal f (terminal-map X) F)

  is-orthogonal-pullback-condition-terminal-map-is-local :
    is-local f X → is-orthogonal-pullback-condition f (terminal-map X)
  is-orthogonal-pullback-condition-terminal-map-is-local =
    is-pullback-is-equiv-horizontal-maps
      ( precomp f unit)
      ( postcomp A (terminal-map X))
      ( cone-pullback-hom f (terminal-map X))
      ( is-local-is-contr f unit is-contr-unit)

  is-orthogonal-terminal-map-is-local :
    is-local f X → is-orthogonal f (terminal-map X)
  is-orthogonal-terminal-map-is-local F =
    is-orthogonal-is-orthogonal-pullback-condition f (terminal-map X)
      ( is-orthogonal-pullback-condition-terminal-map-is-local F)
```

### If the codomain of `g` is `f`-local, then `g` is `f`-orthogonal if and only if the domain of `g` is `f`-local

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-orthogonal-pullback-condition-is-local-domain-is-local-codomain :
    is-local f Y → is-local f X → is-orthogonal-pullback-condition f g
  is-orthogonal-pullback-condition-is-local-domain-is-local-codomain =
    is-pullback-is-equiv-horizontal-maps
      ( precomp f Y)
      ( postcomp A g)
      ( cone-pullback-hom f g)

  is-orthogonal-is-local-domain-is-local-codomain :
    is-local f Y → is-local f X → is-orthogonal f g
  is-orthogonal-is-local-domain-is-local-codomain H K =
    is-orthogonal-is-orthogonal-pullback-condition f g
      ( is-orthogonal-pullback-condition-is-local-domain-is-local-codomain H K)

  is-local-domain-is-orthogonal-pullback-condition-is-local-codomain :
    is-local f Y → is-orthogonal-pullback-condition f g → is-local f X
  is-local-domain-is-orthogonal-pullback-condition-is-local-codomain H G =
    is-local-is-orthogonal-pullback-condition-terminal-map f
      ( is-orthogonal-pullback-condition-right-comp f g (terminal-map Y)
        ( is-orthogonal-pullback-condition-terminal-map-is-local f H)
        ( G))

  is-local-domain-is-orthogonal-is-local-codomain :
    is-local f Y → is-orthogonal f g → is-local f X
  is-local-domain-is-orthogonal-is-local-codomain H G =
    is-local-domain-is-orthogonal-pullback-condition-is-local-codomain H
      ( is-orthogonal-pullback-condition-is-orthogonal f g G)
```

## References

{{#bibliography}} {{#reference BW23}}
