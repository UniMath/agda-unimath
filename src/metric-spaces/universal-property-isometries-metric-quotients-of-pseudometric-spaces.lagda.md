# Universal property of metric quotients of pseudometric spaces and isometries

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.universal-property-isometries-metric-quotients-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
open import metric-spaces.unit-map-metric-quotients-of-pseudometric-spaces
open import metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces
```

</details>

## Idea

Precomposition with the natural
[isometry](metric-spaces.isometries-pseudometric-spaces.md) from a
[pseudometric space](metric-spaces.pseudometric-spaces.md) `P` into its
[metric quotient](metric-spaces.metric-quotients-of-pseudometric-spaces.md)

```text
q : P → [P]
```

maps [isometries](metric-spaces.isometries-metric-spaces.md) into a metric space
`[P] → M` to [isometries](metric-spaces.isometries-pseudometric-spaces.md) from
`P` to the underlying pseudometric space of `M`.

This action is an [equivalence](foundation.equivalences.md) so isometries from a
pseudometric space to a metric space are
{{#concept "equivalent" Disambiguation="isometries of metric quotients of pseudometric spaces" Agda=equiv-isometry-metric-quotient-Pseudometric-Space}}
to isometries from its metric quotient.

Equivalently, the metric quotient satisfies the
{{#concept "universal property" Disambiguation="of metric quotients and isometries" Agda=is-contr-extension-isometry-metric-quotient-Pseudometric-Space}}
of metric quotients and isometries: for any isometry `f : P → M` into a metric
space `M`, there [uniquely exists](foundation.uniqueness-quantification.md) an
extension of `f` along `q`, i.e., an isometry `g : [P] → M` such that

```text
g ∘ q ~ f.
```

## Definitions

### Precomposition of isometries by the metric quotient isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M →
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-isometry-metric-quotient-Pseudometric-Space f =
    comp-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( f)
      ( unit-isometry-metric-quotient-Pseudometric-Space P)
```

### Induced isometry from the quotient metric space into a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2)
  (B : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space A (pseudometric-Metric-Space B))
  where

  map-exten-isometry-metric-quotient-Pseudometric-Space :
    map-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  map-exten-isometry-metric-quotient-Pseudometric-Space =
    map-exten-short-map-metric-quotient-Pseudometric-space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  compute-map-exten-isometry-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space A) →
    {x : type-Pseudometric-Space A} →
    is-in-class-metric-quotient-Pseudometric-Space A X x →
    map-exten-isometry-metric-quotient-Pseudometric-Space X ＝
    map-isometry-Pseudometric-Space
      ( A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( x)
  compute-map-exten-isometry-metric-quotient-Pseudometric-Space =
    compute-map-exten-short-map-metric-quotient-Pseudometric-Space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))
```

### Extensions of isometries along the natural inclusion into the metric quotient

#### The property of being the extension of an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M)
  where

  is-extension-prop-isometry-metric-quotient-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  is-extension-prop-isometry-metric-quotient-Pseudometric-Space =
    Π-Prop
      ( type-Pseudometric-Space P)
      ( λ x →
        eq-prop-Metric-Space
          ( M)
          ( map-isometry-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( precomp-isometry-metric-quotient-Pseudometric-Space P M g)
            ( x))
          ( map-isometry-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)
            ( x)))

  is-extension-isometry-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l1')
  is-extension-isometry-metric-quotient-Pseudometric-Space =
    type-Prop
      is-extension-prop-isometry-metric-quotient-Pseudometric-Space

  is-prop-is-extension-isometry-metric-quotient-Pseudometric-Space :
    is-prop
      is-extension-isometry-metric-quotient-Pseudometric-Space
  is-prop-is-extension-isometry-metric-quotient-Pseudometric-Space =
    is-prop-type-Prop
      is-extension-prop-isometry-metric-quotient-Pseudometric-Space
```

#### The type of extensions of isometries

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  extension-isometry-metric-quotient-Pseudometric-Space :
    UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  extension-isometry-metric-quotient-Pseudometric-Space =
    Σ ( isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M)
      ( is-extension-isometry-metric-quotient-Pseudometric-Space P M f)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : extension-isometry-metric-quotient-Pseudometric-Space P M f)
  where

  isometry-extension-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M
  isometry-extension-isometry-metric-quotient-Pseudometric-Space = pr1 g

  map-extension-isometry-metric-quotient-Pseudometric-Space :
    map-Metric-Space (metric-quotient-Pseudometric-Space P) M
  map-extension-isometry-metric-quotient-Pseudometric-Space =
    map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( isometry-extension-isometry-metric-quotient-Pseudometric-Space)

  is-extension-isometry-extension-isometry-metric-quotient-Pseudometric-Space :
    map-extension-isometry-metric-quotient-Pseudometric-Space ∘
    unit-map-metric-quotient-Pseudometric-Space P ~
    map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f
  is-extension-isometry-extension-isometry-metric-quotient-Pseudometric-Space
    = pr2 g
```

## Properties

### Extensions are fibers of precomposition map of the natural inclusion of metric quotients

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  compute-extension-fiber-precomp-isometry-metric-quotient-Pseudometric-Space :
    fiber (precomp-isometry-metric-quotient-Pseudometric-Space P M) f ≃
    extension-isometry-metric-quotient-Pseudometric-Space P M f
  compute-extension-fiber-precomp-isometry-metric-quotient-Pseudometric-Space =
    equiv-tot
      ( λ g →
        equiv-eq-htpy-map-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-isometry-metric-quotient-Pseudometric-Space P M g)
          ( f))
```

### The extension of an isometry is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  preserves-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : type-metric-quotient-Pseudometric-Space P) →
    neighborhood-metric-quotient-Pseudometric-Space
      ( P)
      ( d)
      ( x)
      ( y) →
    neighborhood-Metric-Space
      ( M)
      ( d)
      ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f x)
      ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f y)
  preserves-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space =
    is-short-map-exten-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))

  reflects-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : type-metric-quotient-Pseudometric-Space P) →
    neighborhood-Metric-Space
      ( M)
      ( d)
      ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f x)
      ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f y) →
    neighborhood-metric-quotient-Pseudometric-Space
      ( P)
      ( d)
      ( x)
      ( y)
  reflects-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space
    d X Y N⟨fX,fY⟩ (x , x∈X) (y , y∈Y) =
    reflects-neighborhoods-map-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-Metric-Space M)
      ( f)
      ( d)
      ( x)
      ( y)
      ( binary-tr
        ( neighborhood-Metric-Space M d)
        ( compute-map-exten-isometry-metric-quotient-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( X)
          ( x∈X))
        ( compute-map-exten-isometry-metric-quotient-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( Y)
          ( y∈Y))
        ( N⟨fX,fY⟩))

  is-isometry-map-exten-isometry-metric-quotient-Pseudometric-Space :
    is-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f)
  is-isometry-map-exten-isometry-metric-quotient-Pseudometric-Space d x y =
    ( ( preserves-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-exten-isometry-metric-quotient-Pseudometric-Space
        ( d)
        ( x)
        ( y)))
```

### The extension induced by an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  isometry-exten-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M
  isometry-exten-isometry-metric-quotient-Pseudometric-Space =
    ( map-exten-isometry-metric-quotient-Pseudometric-Space P M f ,
      is-isometry-map-exten-isometry-metric-quotient-Pseudometric-Space P M f)

  is-extension-exten-isometry-metric-quotient-Pseudometric-Space :
    is-extension-isometry-metric-quotient-Pseudometric-Space P M f
      isometry-exten-isometry-metric-quotient-Pseudometric-Space
  is-extension-exten-isometry-metric-quotient-Pseudometric-Space =
    is-extension-exten-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))

  exten-isometry-metric-quotient-Pseudometric-Space :
    extension-isometry-metric-quotient-Pseudometric-Space P M f
  exten-isometry-metric-quotient-Pseudometric-Space =
    ( isometry-exten-isometry-metric-quotient-Pseudometric-Space ,
      is-extension-exten-isometry-metric-quotient-Pseudometric-Space)
```

### All extensions are homotopic to the induced extension

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  all-htpy-map-extension-isometry-metric-quotient-Pseudometric-Space :
    (g : extension-isometry-metric-quotient-Pseudometric-Space P M f) →
    htpy-map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( isometry-exten-isometry-metric-quotient-Pseudometric-Space P M f)
      ( isometry-extension-isometry-metric-quotient-Pseudometric-Space
        ( P)
        ( M)
        ( f)
        ( g))
  all-htpy-map-extension-isometry-metric-quotient-Pseudometric-Space g =
    all-htpy-map-extension-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f)
      ( map-Σ-map-base
        ( short-map-isometry-Metric-Space (metric-quotient-Pseudometric-Space
          ( P))
          ( M))
        ( is-extension-short-map-metric-quotient-Pseudometric-Space P M
          ( short-map-isometry-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)))
        ( g))
```

### All extensions are equal to the induced extension

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  contraction-extension-isometry-metric-quotient-Pseudometric-Space :
    (g : extension-isometry-metric-quotient-Pseudometric-Space P M f) →
    exten-isometry-metric-quotient-Pseudometric-Space P M f ＝ g
  contraction-extension-isometry-metric-quotient-Pseudometric-Space g =
    eq-type-subtype
      ( is-extension-prop-isometry-metric-quotient-Pseudometric-Space P M f)
      ( eq-htpy-map-isometry-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( M)
        ( all-htpy-map-extension-isometry-metric-quotient-Pseudometric-Space
          ( P)
          ( M)
          ( f)
          ( g)))
```

### The type of extensions of an isometry is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-contr-extension-isometry-metric-quotient-Pseudometric-Space :
    is-contr
      ( extension-isometry-metric-quotient-Pseudometric-Space P M f)
  is-contr-extension-isometry-metric-quotient-Pseudometric-Space =
    ( exten-isometry-metric-quotient-Pseudometric-Space P M f ,
      contraction-extension-isometry-metric-quotient-Pseudometric-Space P M f)
```

### Precomposing by the natual isometry of metric quotients is an equivalence

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where abstract

  is-contr-map-precomp-isometry-metric-quotient-Pseudometric-Space :
    (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M)) →
    is-contr
      (fiber (precomp-isometry-metric-quotient-Pseudometric-Space P M) f)
  is-contr-map-precomp-isometry-metric-quotient-Pseudometric-Space f =
    is-contr-equiv
      ( extension-isometry-metric-quotient-Pseudometric-Space P M f)
      ( compute-extension-fiber-precomp-isometry-metric-quotient-Pseudometric-Space
        ( P)
        ( M)
        ( f))
      ( is-contr-extension-isometry-metric-quotient-Pseudometric-Space P M f)

  is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space :
    is-equiv
      (precomp-isometry-metric-quotient-Pseudometric-Space P M)
  is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space =
    is-equiv-is-contr-map
      is-contr-map-precomp-isometry-metric-quotient-Pseudometric-Space
```

### The equivalence between isometries from a pseudometric space in a metric space and isometries from the metric quotient

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M ≃
    isometry-Pseudometric-Space P (pseudometric-Metric-Space M)
  equiv-isometry-metric-quotient-Pseudometric-Space =
    ( precomp-isometry-metric-quotient-Pseudometric-Space P M ,
      is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space P M)
```
