# Modulated uniformly continuous functions between metric spaces

```agda
module metric-spaces.modulated-uniformly-continuous-functions-metric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.minimum-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers

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
open import metric-spaces.continuous-functions-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.short-functions-metric-spaces
```

</details>

## Idea

Given a [function](metric-spaces.functions-metric-spaces.md) `f` between
[metric spaces](metric-spaces.metric-spaces.md) `X` and `Y`, a
{{#concept "modulus of uniform continuity" Disambiguation="function between metric spaces" Agda=modulus-of-uniform-continuity-function-Metric-Space}}
is a function `m : ℚ⁺ → ℚ⁺` such that for any `x : X`, whenever `x'` is in an
`m ε`-neighborhood of `x`, `f x'` is in an `ε`-neighborhood of `f x`. A function
`f` paired with a modulus of uniform continuity `m` is called a
{{#concept "modulated uniformly continuous function" Agda=modulated-ucont-map-Metric-Space}}
from `X` to `Y`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : type-function-Metric-Space X Y)
  where

  is-modulus-of-uniform-continuity-prop-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → Prop (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-prop-function-Metric-Space m =
    Π-Prop
      ( type-Metric-Space X)
      ( λ x →
        is-modulus-of-continuity-at-point-prop-function-Metric-Space X Y f x m)

  is-modulus-of-uniform-continuity-function-Metric-Space :
    (ℚ⁺ → ℚ⁺) → UU (l1 ⊔ l2 ⊔ l4)
  is-modulus-of-uniform-continuity-function-Metric-Space m =
    type-Prop (is-modulus-of-uniform-continuity-prop-function-Metric-Space m)

  modulus-of-uniform-continuity-function-Metric-Space : UU (l1 ⊔ l2 ⊔ l4)
  modulus-of-uniform-continuity-function-Metric-Space =
    type-subtype is-modulus-of-uniform-continuity-prop-function-Metric-Space
```

### The type of modulated uniformly continuous maps between metric spaces

```agda
module _
  {l1 l2 l3 l4 : Level} (X : Metric-Space l1 l2) (Y : Metric-Space l3 l4)
  where

  modulated-ucont-map-Metric-Space : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  modulated-ucont-map-Metric-Space =
    Σ ( type-function-Metric-Space X Y)
      ( λ f →
        Σ ( ℚ⁺ → ℚ⁺)
          ( is-modulus-of-uniform-continuity-function-Metric-Space X Y f))

  map-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space → type-function-Metric-Space X Y
  map-modulated-ucont-map-Metric-Space = pr1

  modulus-modulated-ucont-map-Metric-Space :
    modulated-ucont-map-Metric-Space → ℚ⁺ → ℚ⁺
  modulus-modulated-ucont-map-Metric-Space = pr1 ∘ pr2

  is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space :
    (f : modulated-ucont-map-Metric-Space) →
    is-modulus-of-uniform-continuity-function-Metric-Space
      ( X)
      ( Y)
      ( map-modulated-ucont-map-Metric-Space f)
      ( modulus-modulated-ucont-map-Metric-Space f)
  is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space =
    pr2 ∘ pr2
```

### Modulated uniformly continuous functions are continuous everywhere

```agda
module _
  {l1 l2 l3 l4 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (f : modulated-ucont-map-Metric-Space X Y)
  where

  is-continuous-at-point-map-modulated-ucont-map-Metric-Space :
    (x : type-Metric-Space X) →
    is-continuous-at-point-function-Metric-Space X Y
      ( map-modulated-ucont-map-Metric-Space X Y f)
      ( x)
  is-continuous-at-point-map-modulated-ucont-map-Metric-Space x =
    intro-exists
      ( modulus-modulated-ucont-map-Metric-Space X Y f)
      ( is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
        ( X)
        ( Y)
        ( f)
        ( x))
```

### The modulated uniformly continuous identity function

```agda
module _
  {l1 l2 : Level} (X : Metric-Space l1 l2)
  where

  id-modulated-ucont-map-Metric-Space : modulated-ucont-map-Metric-Space X X
  id-modulated-ucont-map-Metric-Space = ( id , id , λ _ _ _ → id)
```

### The composition of modulated uniformly continuous functions

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (X : Metric-Space l1 l2)
  (Y : Metric-Space l3 l4)
  (Z : Metric-Space l5 l6)
  (f : modulated-ucont-map-Metric-Space Y Z)
  (g : modulated-ucont-map-Metric-Space X Y)
  where

  map-comp-modulated-ucont-map-Metric-Space : type-function-Metric-Space X Z
  map-comp-modulated-ucont-map-Metric-Space =
    map-modulated-ucont-map-Metric-Space Y Z f ∘
    map-modulated-ucont-map-Metric-Space X Y g

  abstract
    modulus-comp-modulated-ucont-map-Metric-Space : ℚ⁺ → ℚ⁺
    modulus-comp-modulated-ucont-map-Metric-Space =
      modulus-modulated-ucont-map-Metric-Space X Y g ∘
      modulus-modulated-ucont-map-Metric-Space Y Z f

    is-modulus-comp-modulated-ucont-map-Metric-Space :
      is-modulus-of-uniform-continuity-function-Metric-Space X Z
        ( map-comp-modulated-ucont-map-Metric-Space)
        ( modulus-comp-modulated-ucont-map-Metric-Space)
    is-modulus-comp-modulated-ucont-map-Metric-Space x ε x' Nε'x'' =
      is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
        ( Y)
        ( Z)
        ( f)
        ( map-modulated-ucont-map-Metric-Space X Y g x)
        ( ε)
        ( map-modulated-ucont-map-Metric-Space X Y g x')
        ( is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
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

### A function is short if and only if the identity is a modulus of uniform continuity for it

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (f : type-function-Metric-Space A B)
  where

  is-short-is-modulus-of-uniform-continuity-id-function-Metric-Space :
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id →
    is-short-function-Metric-Space A B f
  is-short-id-is-modulus-of-uniform-continuity-function-Metric-Space H ε x =
    H x ε

  is-modulus-of-uniform-continuity-id-is-short-function-Metric-Space :
    is-short-function-Metric-Space A B f →
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id
  id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space H x ε =
    H ε x

  is-short-iff-is-modulus-of-uniform-continuity-id-function-Metric-Space :
    is-short-function-Metric-Space A B f ↔
    is-modulus-of-uniform-continuity-function-Metric-Space A B f id
  is-short-iff-id-is-modulus-of-uniform-continuity-function-Metric-Space =
    ( id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space ,
      is-short-id-is-modulus-of-uniform-continuity-function-Metric-Space)
```

### Modulated uniformly continuous functions from short functions

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Metric-Space l1 l2)
  (B : Metric-Space l3 l4)
  where

  modulated-ucont-map-short-function-Metric-Space :
    short-function-Metric-Space A B →
    modulated-ucont-map-Metric-Space A B
  modulated-ucont-map-short-function-Metric-Space (f , is-short-f) =
    ( f ,
      id ,
      id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space
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
    modulated-ucont-map-short-function-Metric-Space A B
      ( short-isometry-Metric-Space A B f)
```

### The Cartesian product of modulated uniformly continuous functions on metric spaces

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4)
  (C : Metric-Space l5 l6) (D : Metric-Space l7 l8)
  (f : modulated-ucont-map-Metric-Space A B)
  (g : modulated-ucont-map-Metric-Space C D)
  where

  map-product-modulated-ucont-map-Metric-Space :
    type-function-Metric-Space
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
      is-modulus-of-uniform-continuity-function-Metric-Space
        ( product-Metric-Space A C)
        ( product-Metric-Space B D)
        ( map-product-modulated-ucont-map-Metric-Space)
        ( modulus-product-modulated-ucont-map-Metric-Space)
    is-modulus-product-modulated-ucont-map-Metric-Space
      (a , c) ε (a' , c') (Nε'aa' , Nε'cc') =
      ( is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
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
        is-modulus-of-uniform-continuity-modulus-modulated-ucont-map-Metric-Space
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

### If a binary function has a fixed modulus of uniform continuity in each argument, it is modulated uniformly continuous on the product space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  (f : type-Metric-Space A → type-Metric-Space B → type-Metric-Space C)
  (mf₁ : ℚ⁺ → ℚ⁺)
  (is-mod-mf₁ :
    (a : type-Metric-Space A) →
    is-modulus-of-uniform-continuity-function-Metric-Space B C
      ( f a)
      ( mf₁))
  (mf₂ : ℚ⁺ → ℚ⁺)
  (is-mod-mf₂ :
    (b : type-Metric-Space B) →
    is-modulus-of-uniform-continuity-function-Metric-Space A C
      ( λ a → f a b)
      ( mf₂))
  where

  abstract
    modulus-modulated-ucont-binary-map-Metric-Space : ℚ⁺ → ℚ⁺
    modulus-modulated-ucont-binary-map-Metric-Space ε =
      let
        (δ , η , _) = split-ℚ⁺ ε
      in min-ℚ⁺ (mf₁ δ) (mf₂ η)

    is-modulus-modulated-ucont-binary-map-Metric-Space :
      is-modulus-of-uniform-continuity-function-Metric-Space
        ( product-Metric-Space A B)
        ( C)
        ( ind-Σ f)
        ( modulus-modulated-ucont-binary-map-Metric-Space)
    is-modulus-modulated-ucont-binary-map-Metric-Space
      (a , b) ε (a' , b') (Nε'aa' , Nε'bb') =
      let
        (δ , η , δ+η=ε) = split-ℚ⁺ ε
        ε' = modulus-modulated-ucont-binary-map-Metric-Space ε
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

  modulated-ucont-binary-map-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-binary-map-Metric-Space =
    ( ind-Σ f ,
      modulus-modulated-ucont-binary-map-Metric-Space ,
      is-modulus-modulated-ucont-binary-map-Metric-Space)
```

### If a binary function is short in each argument, it is a modulated uniformly continuous function on the product metric space

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Metric-Space l1 l2) (B : Metric-Space l3 l4) (C : Metric-Space l5 l6)
  (f : type-Metric-Space A → type-Metric-Space B → type-Metric-Space C)
  (is-short-fa :
    (a : type-Metric-Space A) →
    is-short-function-Metric-Space B C (f a))
  (is-short-fb :
    (b : type-Metric-Space B) →
    is-short-function-Metric-Space A C (λ a → f a b))
  where

  modulated-ucont-short-binary-map-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-short-binary-map-Metric-Space =
    modulated-ucont-binary-map-Metric-Space A B C f
      ( id)
      ( λ a →
        id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space
          ( B)
          ( C)
          ( f a)
          ( is-short-fa a))
      ( id)
      ( λ b →
        id-is-modulus-of-uniform-continuity-is-short-function-Metric-Space
          ( A)
          ( C)
          ( λ a → f a b)
          ( is-short-fb b))
```

### If a binary function is an isometry in each argument, it is a modulated uniformly continuous function on the product metric space

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

  modulated-ucont-binary-isometry-Metric-Space :
    modulated-ucont-map-Metric-Space (product-Metric-Space A B) C
  modulated-ucont-binary-isometry-Metric-Space =
    modulated-ucont-short-binary-map-Metric-Space A B C f
      ( λ a → is-short-is-isometry-Metric-Space B C (f a) (is-iso-fa a))
      ( λ b → is-short-is-isometry-Metric-Space A C (λ a → f a b) (is-iso-fb b))
```

## See also

- [(Unmodulated) uniformly continuous functions on metric spaces](metric-spaces.uniformly-continuous-functions-metric-spaces.md)
