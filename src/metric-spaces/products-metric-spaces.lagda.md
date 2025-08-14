# Products of metric spaces

```agda
module metric-spaces.products-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.category-of-sets
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.isomorphisms-of-sets
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.extensional-premetric-structures
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-space-of-short-functions-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.metric-structures
open import metric-spaces.monotonic-premetric-structures
open import metric-spaces.premetric-structures
open import metric-spaces.pseudometric-structures
open import metric-spaces.reflexive-premetric-structures
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.symmetric-premetric-structures
open import metric-spaces.triangular-premetric-structures
open import metric-spaces.uniformly-continuous-functions-metric-spaces
```

</details>

## Idea

A pair of [metric spaces](metric-spaces.metric-spaces.md) induces a metric space
over the [Cartesian product](foundation.cartesian-product-types.md) of the
carrier types of its arguments.

## Definitions

### Products of metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  type-product-Metric-Space : UU (l1 ⊔ l3)
  type-product-Metric-Space = type-Metric-Space A × type-Metric-Space B

  structure-product-Metric-Space : Premetric (l2 ⊔ l4) type-product-Metric-Space
  structure-product-Metric-Space d (a1 , b1) (a2 , b2) =
    structure-Metric-Space A d a1 a2 ∧ structure-Metric-Space B d b1 b2

  is-reflexive-structure-product-Metric-Space :
    is-reflexive-Premetric structure-product-Metric-Space
  is-reflexive-structure-product-Metric-Space d (a , b) =
    ( is-reflexive-structure-Metric-Space A d a ,
      is-reflexive-structure-Metric-Space B d b)

  is-symmetric-structure-product-Metric-Space :
    is-symmetric-Premetric structure-product-Metric-Space
  is-symmetric-structure-product-Metric-Space
    d (a1 , b1) (a2 , b2) (a1~a2 , b1~b2) =
      ( is-symmetric-structure-Metric-Space A d a1 a2 a1~a2 ,
        is-symmetric-structure-Metric-Space B d b1 b2 b1~b2)

  is-triangular-structure-product-Metric-Space :
    is-triangular-Premetric structure-product-Metric-Space
  is-triangular-structure-product-Metric-Space
    (a1 , b1) (a2 , b2) (a3 , b3) d12 d23 (a1~a2 , b1~b2) (a2~a3 , b2~b3) =
      ( is-triangular-structure-Metric-Space A a1 a2 a3 d12 d23 a1~a2 a2~a3 ,
        is-triangular-structure-Metric-Space B b1 b2 b3 d12 d23 b1~b2 b2~b3)

  is-local-structure-product-Metric-Space :
    is-local-Premetric structure-product-Metric-Space
  is-local-structure-product-Metric-Space =
    is-local-is-tight-Premetric
      ( structure-product-Metric-Space)
      ( λ (a1 , b1) (a2 , b2) ind-ab1-ab2 →
        eq-pair
          ( is-tight-structure-Metric-Space A a1 a2 (pr1 ∘ ind-ab1-ab2))
          ( is-tight-structure-Metric-Space B b1 b2 (pr2 ∘ ind-ab1-ab2)))

  is-pseudometric-structure-product-Metric-Space :
    is-pseudometric-Premetric structure-product-Metric-Space
  is-pseudometric-structure-product-Metric-Space =
    is-reflexive-structure-product-Metric-Space ,
    is-symmetric-structure-product-Metric-Space ,
    is-triangular-structure-product-Metric-Space

  is-metric-structure-product-Metric-Space :
    is-metric-Premetric structure-product-Metric-Space
  is-metric-structure-product-Metric-Space =
    is-pseudometric-structure-product-Metric-Space ,
    is-local-structure-product-Metric-Space

  product-Metric-Space : Metric-Space (l1 ⊔ l3) (l2 ⊔ l4)
  pr1 product-Metric-Space =
    ( type-product-Metric-Space , structure-product-Metric-Space)
  pr2 product-Metric-Space = is-metric-structure-product-Metric-Space
```

## Properties

### The projection maps on a product metric space are short

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  is-short-pr1-product-Metric-Space :
    is-short-function-Metric-Space (product-Metric-Space A B) A pr1
  is-short-pr1-product-Metric-Space _ _ _ = pr1

  is-short-pr2-product-Metric-Space :
    is-short-function-Metric-Space (product-Metric-Space A B) B pr2
  is-short-pr2-product-Metric-Space _ _ _ = pr2
```

### The pairing map is short

```agda
module _
  {lx lx' ly ly' : Level} (X : Metric-Space lx lx') (Y : Metric-Space ly ly')
  where

  is-short-pair-product-Metric-Space :
    (x : type-Metric-Space X) →
    is-short-function-Metric-Space
      ( Y)
      ( product-Metric-Space X Y)
      ( pair x)
  is-short-pair-product-Metric-Space x d y y' Nyy' =
    ( refl-structure-Metric-Space X d x , Nyy')

  short-pair-product-Metric-Space :
    type-Metric-Space X →
    short-function-Metric-Space Y (product-Metric-Space X Y)
  short-pair-product-Metric-Space x =
    ( pair x , is-short-pair-product-Metric-Space x)

  is-short-short-pair-product-Metric-Space :
    is-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space
        ( Y)
        ( product-Metric-Space X Y))
      ( short-pair-product-Metric-Space)
  is-short-short-pair-product-Metric-Space d x x' Nxx' y =
    ( Nxx' , refl-structure-Metric-Space Y d y)

  short-pair-Metric-Space :
    short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space
        ( Y)
        ( product-Metric-Space X Y))
  short-pair-Metric-Space =
    short-pair-product-Metric-Space ,
    is-short-short-pair-product-Metric-Space
```

### Currying short maps from a product metric space

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  (f : short-function-Metric-Space (product-Metric-Space X Y) Z)
  where

  map-ev-pair-short-function-product-Metric-Space :
    type-Metric-Space X →
    type-Metric-Space Y →
    type-Metric-Space Z
  map-ev-pair-short-function-product-Metric-Space x y =
    map-short-function-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( f)
      ( x , y)

  is-short-map-ev-pair-short-function-product-Metric-Space :
    (x : type-Metric-Space X) →
    is-short-function-Metric-Space
      ( Y)
      ( Z)
      ( map-ev-pair-short-function-product-Metric-Space x)
  is-short-map-ev-pair-short-function-product-Metric-Space x d y y' =
    ( is-short-map-short-function-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( f)
      ( d)
      ( x , y)
      ( x , y')) ∘
    ( is-short-pair-product-Metric-Space X Y x d y y')

  short-map-ev-pair-short-function-product-Metric-Space :
    (x : type-Metric-Space X) →
    short-function-Metric-Space Y Z
  short-map-ev-pair-short-function-product-Metric-Space x =
    map-ev-pair-short-function-product-Metric-Space x ,
    is-short-map-ev-pair-short-function-product-Metric-Space x

  is-short-short-map-ev-pair-short-function-product-Metric-Space :
    is-short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
      ( short-map-ev-pair-short-function-product-Metric-Space)
  is-short-short-map-ev-pair-short-function-product-Metric-Space d x x' Nxx' y =
    is-short-map-short-function-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( f)
      ( d)
      ( x , y)
      ( x' , y)
      ( is-short-short-pair-product-Metric-Space X Y d x x' Nxx' y)

  ev-pair-short-function-product-Metric-Space :
    short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
  ev-pair-short-function-product-Metric-Space =
    short-map-ev-pair-short-function-product-Metric-Space ,
    is-short-short-map-ev-pair-short-function-product-Metric-Space
```

### Currying short maps from a product metric space is preserves and reflects neighborhoods

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  (d : ℚ⁺)
  (f g : short-function-Metric-Space (product-Metric-Space X Y) Z)
  where

  preserves-neighborhood-ev-pair-short-function-product-Metric-Space :
    neighborhood-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( product-Metric-Space X Y)
        ( Z))
      ( d)
      ( f)
      ( g) →
    neighborhood-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
      ( d)
      ( ev-pair-short-function-product-Metric-Space X Y Z f)
      ( ev-pair-short-function-product-Metric-Space X Y Z g)
  preserves-neighborhood-ev-pair-short-function-product-Metric-Space
    Nfg x y =
    Nfg (x , y)

  reflects-neighborhood-ev-pair-short-function-product-Metric-Space :
    neighborhood-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
      ( d)
      ( ev-pair-short-function-product-Metric-Space X Y Z f)
      ( ev-pair-short-function-product-Metric-Space X Y Z g) →
    neighborhood-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( product-Metric-Space X Y)
        ( Z))
      ( d)
      ( f)
      ( g)
  reflects-neighborhood-ev-pair-short-function-product-Metric-Space
    Nfg (x , y) =
    Nfg x y
```

### Currying short maps from a product metric space is an isometry

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  where

  is-isometry-ev-pair-short-function-product-Metric-Space :
    is-isometry-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( product-Metric-Space X Y)
        ( Z))
      ( metric-space-of-short-functions-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
      ( ev-pair-short-function-product-Metric-Space X Y Z)
  is-isometry-ev-pair-short-function-product-Metric-Space d f g =
    ( preserves-neighborhood-ev-pair-short-function-product-Metric-Space
      X
      Y
      Z
      d
      f
      g) ,
    ( reflects-neighborhood-ev-pair-short-function-product-Metric-Space
      X
      Y
      Z
      d
      f
      g)

  isometry-ev-pair-short-function-product-Metric-Space :
    isometry-Metric-Space
      ( metric-space-of-short-functions-Metric-Space
        ( product-Metric-Space X Y)
        ( Z))
      ( metric-space-of-short-functions-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
  isometry-ev-pair-short-function-product-Metric-Space =
    ev-pair-short-function-product-Metric-Space X Y Z ,
    is-isometry-ev-pair-short-function-product-Metric-Space
```

### Uncurrying short maps between metric spaces

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  where

  map-ind-short-function-product-Metric-Space :
    short-function-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z) →
    map-type-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
  map-ind-short-function-product-Metric-Space f (x , y) =
    map²-short-function-Metric-Space X Y Z f x y

  eq-map-ev-pair-ind-short-function-product-Metric-Space :
    ( f :
      short-function-Metric-Space
        ( product-Metric-Space X Y)
        ( Z)) →
    map-ind-short-function-product-Metric-Space
      ( ev-pair-short-function-product-Metric-Space X Y Z f) ＝
    map-short-function-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( f)
  eq-map-ev-pair-ind-short-function-product-Metric-Space f =
    refl

  all-eq-preimage-ev-pair-short-function-product-Metric-Space :
    ( f :
        short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)) →
    ( g g' : short-function-Metric-Space (product-Metric-Space X Y) Z) →
    ( ev-pair-short-function-product-Metric-Space X Y Z g ＝ f) →
    ( ev-pair-short-function-product-Metric-Space X Y Z g' ＝ f) →
    ( g ＝ g')
  all-eq-preimage-ev-pair-short-function-product-Metric-Space f g g' H H' =
    eq-type-subtype
      ( is-short-function-prop-Metric-Space (product-Metric-Space X Y) Z)
      ( ( inv (eq-map-ev-pair-ind-short-function-product-Metric-Space g)) ∙
        ( ap map-ind-short-function-product-Metric-Space H) ∙
        ( ap map-ind-short-function-product-Metric-Space (inv H') ∙
        ( eq-map-ev-pair-ind-short-function-product-Metric-Space g')))

  all-eq-fiber-ev-pair-short-function-product-Metric-Space :
    ( f :
        short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)) →
    ( g g' :
      Σ ( short-function-Metric-Space (product-Metric-Space X Y) Z)
        ( λ g → ev-pair-short-function-product-Metric-Space X Y Z g ＝ f)) →
      ( g ＝ g')
  all-eq-fiber-ev-pair-short-function-product-Metric-Space f g g' =
    eq-type-subtype
      ( λ h →
        Id-Prop
          ( set-Metric-Space
            ( metric-space-of-short-functions-Metric-Space
              ( X)
              ( metric-space-of-short-functions-Metric-Space Y Z)))
          ( ev-pair-short-function-product-Metric-Space X Y Z h)
          ( f))
      ( all-eq-preimage-ev-pair-short-function-product-Metric-Space
        ( f)
        ( pr1 g)
        ( pr1 g')
        ( pr2 g)
        ( pr2 g'))

  is-prop-fiber-ev-pair-short-function-product-Metric-Space :
    ( f :
        short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)) →
    is-prop
      ( Σ ( short-function-Metric-Space (product-Metric-Space X Y) Z)
          ( λ g → ev-pair-short-function-product-Metric-Space X Y Z g ＝ f))
  is-prop-fiber-ev-pair-short-function-product-Metric-Space =
    is-prop-all-elements-equal ∘
    all-eq-fiber-ev-pair-short-function-product-Metric-Space

  lemma-neighborhood-map-ind-short-function-product-Metric-Space :
    ( f :
        short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)) →
    (dx dy : ℚ⁺) →
    (x x' : type-Metric-Space X) →
    (y y' : type-Metric-Space Y) →
    neighborhood-Metric-Space X dx x x' →
    neighborhood-Metric-Space Y dy y y' →
    neighborhood-Metric-Space
      ( Z)
      ( dx +ℚ⁺ dy)
      ( map-ind-short-function-product-Metric-Space f ( x , y))
      ( map-ind-short-function-product-Metric-Space f ( x' , y'))
  lemma-neighborhood-map-ind-short-function-product-Metric-Space
    f dx dy x x' y y' Nxx' Nyy' =
      is-triangular-structure-Metric-Space
        ( Z)
        ( map-ind-short-function-product-Metric-Space f (x , y))
        ( map-ind-short-function-product-Metric-Space f (x' , y))
        ( map-ind-short-function-product-Metric-Space f (x' , y'))
        ( dx)
        ( dy)
        ( is-short-map²-short-function-Metric-Space
          ( X)
          ( Y)
          ( Z)
          ( f)
          ( x')
          ( dy)
          ( y)
          ( y')
          ( Nyy'))
        ( is-short-map-short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)
          ( f)
          ( dx)
          ( x)
          ( x')
          ( Nxx')
          ( y))

  is-uniformly-continuous-map-ind-short-function-product-Metric-Space :
    ( f :
        short-function-Metric-Space
          ( X)
          ( metric-space-of-short-functions-Metric-Space Y Z)) →
    is-uniformly-continuous-map-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( map-ind-short-function-product-Metric-Space f)
  is-uniformly-continuous-map-ind-short-function-product-Metric-Space f =
    intro-exists
      modulus-le-double-le-ℚ⁺
      le-double-is-modulus-of-uc-map-ind-short-function-product-Metric-Space
    where

    le-double-is-modulus-of-uc-map-ind-short-function-product-Metric-Space :
      is-modulus-of-uniform-continuity-Metric-Space
        ( product-Metric-Space X Y)
        ( Z)
        ( map-ind-short-function-product-Metric-Space f)
        ( modulus-le-double-le-ℚ⁺)
    le-double-is-modulus-of-uc-map-ind-short-function-product-Metric-Space
      (x , y) d (x' , y') (Nxx' , Nyy') =
      is-monotonic-structure-Metric-Space
        ( Z)
        ( map-ind-short-function-product-Metric-Space f (x , y))
        ( map-ind-short-function-product-Metric-Space f (x' , y'))
        ( (modulus-le-double-le-ℚ⁺ d) +ℚ⁺ (modulus-le-double-le-ℚ⁺ d))
        ( d)
        ( le-double-le-modulus-le-double-le-ℚ⁺ d)
        ( lemma-neighborhood-map-ind-short-function-product-Metric-Space
          ( f)
          ( modulus-le-double-le-ℚ⁺ d)
          ( modulus-le-double-le-ℚ⁺ d)
          ( x)
          ( x')
          ( y)
          ( y')
          ( Nxx')
          ( Nyy'))
```

```agda
module _
  {lx lx' ly ly' lz lz' : Level}
  (X : Metric-Space lx lx') (Y : Metric-Space ly ly') (Z : Metric-Space lz lz')
  where

  is-short-map-ind-short-function-prop-Metric-Space :
    Prop (lx ⊔ lx' ⊔ ly ⊔ ly' ⊔ lz ⊔ lz')
  is-short-map-ind-short-function-prop-Metric-Space =
    Π-Prop
      ( short-function-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
      ( ( is-short-function-prop-Metric-Space
          ( product-Metric-Space X Y)
          ( Z)) ∘
        ( map-ind-short-function-product-Metric-Space X Y Z))

  is-short-map-ind-short-function-Metric-Space :
    UU (lx ⊔ lx' ⊔ ly ⊔ ly' ⊔ lz ⊔ lz')
  is-short-map-ind-short-function-Metric-Space =
    type-Prop is-short-map-ind-short-function-prop-Metric-Space

  lemma-is-short-map-ind-short-function-Metric-Space :
    ( f :
      short-function-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z)) →
    ( let
        map-f : type-Metric-Space X → type-Metric-Space Y → type-Metric-Space Z
        map-f = map²-short-function-Metric-Space X Y Z f
      in
        (d : ℚ⁺) (x x' : type-Metric-Space X) (y y' : type-Metric-Space Y) →
        neighborhood-Metric-Space X d x x' →
        neighborhood-Metric-Space Y d y y' →
        neighborhood-Metric-Space Z d (map-f x y) (map-f x' y')) →
    is-short-function-Metric-Space
      ( product-Metric-Space X Y)
      ( Z)
      ( map-ind-short-function-product-Metric-Space X Y Z f)
  lemma-is-short-map-ind-short-function-Metric-Space
    f H d (x , y) (x' , y') N = H d x x' y y' (pr1 N) (pr2 N)

  is-equiv-ev-pair-is-short-map-ind-short-function-Metric-Space :
    is-short-map-ind-short-function-Metric-Space →
    is-equiv (ev-pair-short-function-product-Metric-Space X Y Z)
  is-equiv-ev-pair-is-short-map-ind-short-function-Metric-Space H =
    is-equiv-is-invertible
      ( λ f → map-ind-short-function-product-Metric-Space X Y Z f , H f)
      ( λ f →
        eq-type-subtype
          ( is-short-function-prop-Metric-Space
            ( X)
            ( metric-space-of-short-functions-Metric-Space Y Z))
          ( eq-htpy
            ( λ x →
              eq-type-subtype
                ( is-short-function-prop-Metric-Space Y Z)
                ( eq-htpy (λ y → refl)))))
      ( λ f →
        eq-type-subtype
          ( is-short-function-prop-Metric-Space
            ( product-Metric-Space X Y)
            ( Z))
          ( refl))

  lemma-eq-short-ind-short-function-Metric-Space :
    is-short-map-ind-short-function-Metric-Space →
    metric-space-of-short-functions-Metric-Space
      ( product-Metric-Space X Y)
      ( Z) ＝
    metric-space-of-short-functions-Metric-Space
      ( X)
      ( metric-space-of-short-functions-Metric-Space Y Z)
  lemma-eq-short-ind-short-function-Metric-Space H =
    eq-isometric-equiv-Metric-Space'
      ( metric-space-of-short-functions-Metric-Space
        ( product-Metric-Space X Y)
        ( Z))
      ( metric-space-of-short-functions-Metric-Space
        ( X)
        ( metric-space-of-short-functions-Metric-Space Y Z))
      ( ev-pair-short-function-product-Metric-Space X Y Z ,
        is-equiv-ev-pair-is-short-map-ind-short-function-Metric-Space H ,
        is-isometry-ev-pair-short-function-product-Metric-Space X Y Z)
```
