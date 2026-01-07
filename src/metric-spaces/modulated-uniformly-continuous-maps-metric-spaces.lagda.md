# Modulated uniformly continuous maps between metric spaces

```agda
module metric-spaces.modulated-uniformly-continuous-maps-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cartesian-products-metric-spaces
open import metric-spaces.continuity-of-maps-at-points-metric-spaces
open import metric-spaces.pointwise-continuous-maps-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-maps-metric-spaces
```

</details>

## Idea

Given a [map](metric-spaces.maps-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y`, a
{{#concept "modulus of uniform continuity" Disambiguation="map between metric spaces" Agda=modulus-of-uniform-continuity-map-Metric-Space}}
is a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever `x'` is in an
`m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of `f x`. A map `f`
paired with a modulus of uniform continuity `m` is called a
{{#concept "modulated uniformly continuous map" Agda=modulated-ucont-map-Metric-Space}}
from `X` to `Y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : map-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-map-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-map-Metric-Space m =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x →
        is-modulus-of-continuity-at-point-prop-map-Metric-Space X Y f x m)

  is-modulus-of-uniform-continuity-map-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-map-Metric-Space m =
    type-Prop (is-modulus-of-uniform-continuity-prop-map-Metric-Space m)

  modulus-of-uniform-continuity-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-map-Metric-Space =
    type-subtype is-modulus-of-uniform-continuity-prop-map-Metric-Space
```

### The type of modulated uniformly continuous maps between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  modulated-ucont-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  modulated-ucont-map-Metric-Space =
    Σ ( map-Metric-Space X Y)
      ( λ f →
        Σ ( ℚ⁺ → ℚ⁺)
          ( is-modulus-of-uniform-continuity-map-Metric-Space X Y f))

  map-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space → map-Metric-Space X Y
  map-modulated-ucont-map-Metric-Space = pr1

  modulus-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space → ℚ⁺ → ℚ⁺
  modulus-modulated-ucont-map-Metric-Space = pr1 ∘ pr2

  is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space :
    (f : modulated-ucont-map-Metric-Space) →
    is-modulus-of-uniform-continuity-map-Metric-Space
      ( X)
      ( Y)
      ( map-modulated-ucont-map-Metric-Space f)
      ( modulus-modulated-ucont-map-Metric-Space f)
  is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space =
    pr2 ∘ pr2
```

### Modulated uniformly continuous maps are continuous everywhere

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : modulated-ucont-map-Metric-Space X Y)
  where

  is-pointwise-continuous-map-modulated-ucont-map-Metric-Space :
    is-pointwise-continuous-map-Metric-Space X Y
      ( map-modulated-ucont-map-Metric-Space X Y f)
  is-pointwise-continuous-map-modulated-ucont-map-Metric-Space x =
    intro-exists
      ( modulus-modulated-ucont-map-Metric-Space X Y f)
      ( is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
        ( X)
        ( Y)
        ( f)
        ( x))
```

### The modulated uniformly continuous identity map

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  id-modulated-ucont-map-Metric-Space : modulated-ucont-map-Metric-Space X X
  id-modulated-ucont-map-Metric-Space = (id , id , λ _ _ _ → id)
```

### The composition of modulated uniformly continuous maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  (f : modulated-ucont-map-Metric-Space Y Z)
  (g : modulated-ucont-map-Metric-Space X Y)
  where

  map-comp-modulated-ucont-map-Metric-Space : map-Metric-Space X Z
  map-comp-modulated-ucont-map-Metric-Space =
    map-modulated-ucont-map-Metric-Space Y Z f ∘
    map-modulated-ucont-map-Metric-Space X Y g

  abstract
    modulus-comp-modulated-ucont-map-Metric-Space : ℚ⁺ → ℚ⁺
    modulus-comp-modulated-ucont-map-Metric-Space =
      modulus-modulated-ucont-map-Metric-Space X Y g ∘
      modulus-modulated-ucont-map-Metric-Space Y Z f

    is-modulus-comp-modulated-ucont-map-Metric-Space :
      is-modulus-of-uniform-continuity-map-Metric-Space X Z
        ( map-comp-modulated-ucont-map-Metric-Space)
        ( modulus-comp-modulated-ucont-map-Metric-Space)
    is-modulus-comp-modulated-ucont-map-Metric-Space x ε x' Nε'x'' =
      is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
        ( Y)
        ( Z)
        ( f)
        ( map-modulated-ucont-map-Metric-Space X Y g x)
        ( ε)
        ( map-modulated-ucont-map-Metric-Space X Y g x')
        ( is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
          ( X)
          ( Y)
          ( g)
          ( x)
          ( modulus-modulated-ucont-map-Metric-Space Y Z f ε)
          ( x')
          ( Nε'x''))

  comp-modulated-ucont-map-Metric-Space : modulated-ucont-map-Metric-Space X Z
  comp-modulated-ucont-map-Metric-Space =
    ( map-comp-modulated-ucont-map-Metric-Space ,
      modulus-comp-modulated-ucont-map-Metric-Space ,
      is-modulus-comp-modulated-ucont-map-Metric-Space)
```

### A map is short if and only if the identity is a modulus of uniform continuity for it

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (f : map-Metric-Space A B)
  where

  is-short-map-is-modulus-of-uniform-continuity-map-id-Metric-Space :
    is-modulus-of-uniform-continuity-map-Metric-Space A B f id →
    is-short-map-Metric-Space A B f
  is-short-map-is-modulus-of-uniform-continuity-map-id-Metric-Space H ε x =
    H x ε

  is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space :
    is-short-map-Metric-Space A B f →
    is-modulus-of-uniform-continuity-map-Metric-Space A B f id
  is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space H x ε =
    H ε x

  is-short-map-iff-is-modulus-of-uniform-continuity-map-id-Metric-Space :
    is-short-map-Metric-Space A B f ↔
    is-modulus-of-uniform-continuity-map-Metric-Space A B f id
  is-short-map-iff-is-modulus-of-uniform-continuity-map-id-Metric-Space =
    ( is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space ,
      is-short-map-is-modulus-of-uniform-continuity-map-id-Metric-Space)
```

### Short maps are modulated uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2)
  (B : Metric-Space l3 l4)
  where

  modulated-ucont-map-short-map-Metric-Space :
    short-map-Metric-Space A B →
    modulated-ucont-map-Metric-Space A B
  modulated-ucont-map-short-map-Metric-Space (f , is-short-f) =
    ( f ,
      id ,
      is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space
        ( A)
        ( B)
        ( f)
        ( is-short-f))
```

### Isometries are uniformly continuous

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  where

  modulated-ucont-map-isometry-Metric-Space :
    isometry-Metric-Space A B → modulated-ucont-map-Metric-Space A B
  modulated-ucont-map-isometry-Metric-Space f =
    modulated-ucont-map-short-map-Metric-Space A B
      ( short-map-isometry-Metric-Space A B f)
```

### The Cartesian product of modulated uniformly continuous maps on metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (C : Metric-Space l5 l6) (D : Metric-Space l7 l8)
  (f : modulated-ucont-map-Metric-Space A B)
  (g : modulated-ucont-map-Metric-Space C D)
  where

  map-product-modulated-ucont-map-Metric-Space :
    map-Metric-Space
      ( product-Metric-Space A C)
      ( product-Metric-Space B D)
  map-product-modulated-ucont-map-Metric-Space =
    map-product
      ( map-modulated-ucont-map-Metric-Space A B f)
      ( map-modulated-ucont-map-Metric-Space C D g)

  abstract
    modulus-product-modulated-ucont-map-Metric-Space : ℚ⁺ → ℚ⁺
    modulus-product-modulated-ucont-map-Metric-Space ε =
      min-ℚ⁺
        ( modulus-modulated-ucont-map-Metric-Space A B f ε)
        ( modulus-modulated-ucont-map-Metric-Space C D g ε)

    is-modulus-product-modulated-ucont-map-Metric-Space :
      is-modulus-of-uniform-continuity-map-Metric-Space
        ( product-Metric-Space A C)
        ( product-Metric-Space B D)
        ( map-product-modulated-ucont-map-Metric-Space)
        ( modulus-product-modulated-ucont-map-Metric-Space)
    is-modulus-product-modulated-ucont-map-Metric-Space
      (a , c) ε (a' , c') (Nε'aa' , Nε'cc') =
      ( is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
          ( A)
          ( B)
          ( f)
          ( a)
          ( ε)
          ( a')
          ( weakly-monotonic-neighborhood-Metric-Space A a a' _ _
            ( leq-left-min-ℚ⁺
              ( modulus-modulated-ucont-map-Metric-Space A B f ε)
              ( modulus-modulated-ucont-map-Metric-Space C D g ε))
            ( Nε'aa')) ,
        is-modulus-of-uniform-continuity-map-modulus-modulated-ucont-map-Metric-Space
          ( C)
          ( D)
          ( g)
          ( c)
          ( ε)
          ( c')
          ( weakly-monotonic-neighborhood-Metric-Space C c c' _ _
            ( leq-right-min-ℚ⁺
              ( modulus-modulated-ucont-map-Metric-Space A B f ε)
              ( modulus-modulated-ucont-map-Metric-Space C D g ε))
            ( Nε'cc')))

  product-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space
      ( product-Metric-Space A C)
      ( product-Metric-Space B D)
  product-modulated-ucont-map-Metric-Space =
    ( map-product-modulated-ucont-map-Metric-Space ,
      modulus-product-modulated-ucont-map-Metric-Space ,
      is-modulus-product-modulated-ucont-map-Metric-Space)
```

### If a binary map has a fixed modulus of uniform continuity in each argument, it is modulated uniformly continuous on the product space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  (f : type-Metric-Space A → type-Metric-Space B → type-Metric-Space C)
  (mf₁ : ℚ⁺ → ℚ⁺)
  (mf₂ : ℚ⁺ → ℚ⁺)
  (is-mod-mf₁ :
    (a : type-Metric-Space A) →
    is-modulus-of-uniform-continuity-map-Metric-Space B C
      ( f a)
      ( mf₁))
  (is-mod-mf₂ :
    (b : type-Metric-Space B) →
    is-modulus-of-uniform-continuity-map-Metric-Space A C
      ( λ a → f a b)
      ( mf₂))
  where

  abstract
    modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space :
      ℚ⁺ → ℚ⁺
    modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space
      ε =
      let
        (δ , η , _) = split-ℚ⁺ ε
      in min-ℚ⁺ (mf₁ δ) (mf₂ η)

    is-modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space :
      is-modulus-of-uniform-continuity-map-Metric-Space
        ( product-Metric-Space A B)
        ( C)
        ( rec-product f)
        ( modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space)
    is-modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space
      (a , b) ε (a' , b') (Nε'aa' , Nε'bb') =
      let
        (δ , η , δ+η=ε) = split-ℚ⁺ ε
        ε' =
          modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space
            ( ε)
      in
        tr
          ( λ d → neighborhood-Metric-Space C d (f a b) (f a' b'))
          ( δ+η=ε)
          ( triangular-neighborhood-Metric-Space
            ( C)
            ( f a b)
            ( f a b')
            ( f a' b')
            ( δ)
            ( η)
            ( is-mod-mf₂ b' a η a'
              ( weakly-monotonic-neighborhood-Metric-Space A a a'
                ( ε')
                ( mf₂ η)
                ( leq-right-min-ℚ⁺ (mf₁ δ) (mf₂ η))
                ( Nε'aa')))
            ( is-mod-mf₁ a b δ b'
              ( weakly-monotonic-neighborhood-Metric-Space B b b'
                ( ε')
                ( mf₁ δ)
                ( leq-left-min-ℚ⁺ (mf₁ δ) (mf₂ η))
                ( Nε'bb'))))

  modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space =
    ( rec-product f ,
      modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space ,
      is-modulus-modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space)
```

### If a binary map is short in each argument, it is a modulated uniformly continuous map on the product metric space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  (f : type-Metric-Space A → type-Metric-Space B → type-Metric-Space C)
  (is-short-fa :
    (a : type-Metric-Space A) →
    is-short-map-Metric-Space B C (f a))
  (is-short-fb :
    (b : type-Metric-Space B) →
    is-short-map-Metric-Space A C (λ a → f a b))
  where

  modulated-ucont-uncurry-map-is-short-binary-map-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-uncurry-map-is-short-binary-map-Metric-Space =
    modulated-ucont-uncurry-map-is-modulated-ucont-binary-map-Metric-Space A B C
      ( f)
      ( id)
      ( id)
      ( λ a →
        is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space
          ( B)
          ( C)
          ( f a)
          ( is-short-fa a))
      ( λ b →
        is-modulus-of-uniform-continuity-map-id-is-short-map-Metric-Space
          ( A)
          ( C)
          ( λ a → f a b)
          ( is-short-fb b))
```

### If a binary map is an isometry in each argument, it is a modulated uniformly continuous map on the product metric space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  (f : type-Metric-Space A → type-Metric-Space B → type-Metric-Space C)
  (is-iso-fa :
    (a : type-Metric-Space A) → is-isometry-Metric-Space B C (f a))
  (is-iso-fb :
    (b : type-Metric-Space B) → is-isometry-Metric-Space A C (λ a → f a b))
  where

  modulated-ucont-uncurry-map-is-binary-isometry-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-uncurry-map-is-binary-isometry-Metric-Space =
    modulated-ucont-uncurry-map-is-short-binary-map-Metric-Space A B C f
      ( λ a →
        is-short-map-is-isometry-Metric-Space B C (f a) (is-iso-fa a))
      ( λ b →
        is-short-map-is-isometry-Metric-Space A C (λ a → f a b) (is-iso-fb b))
```

## See also

- [(Unmodulated) uniformly continuous maps on metric spaces](metric-spaces.uniformly-continuous-maps-metric-spaces.md)
