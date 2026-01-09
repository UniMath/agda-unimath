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

maps [isometries](metric-spaces.isometries-metric-spaces.md) `[P] → M` to a
[metric space](metric-spaces.metric-spaces.md) to
[isometries](metric-spaces.isometries-pseudometric-spaces.md) from `P` to the
underlying pseudometric space of `M`.

This action is an [equivalence](foundation.equivalences.md) so isometries from a
pseudometric space to a metric space are
{{#concept "equivalent" Disambiguation="isometries of metric quotients of pseudometric spaces Agda=equiv-isometry-metric-quotient-Pseudometric-Space}}
to isometries from its metric quotient.

Equivalently, the metric quotient satisfies the
{{#concept "universal property" Disambiguation="of metric quotients and isometries" Agda=is-contr-coh-isometry-metric-quotient-Pseudometric-Space}}
of metric quotients and isometries: for any isometry `f : P → M` into a metric
space `M`, there [uniquely exists](foundation.uniqueness-quantification.md)
an extension of `f` along `q`, i.e., an isometry `g : [P] → M` such that

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
      ( isometry-metric-quotient-Pseudometric-Space P)
```

### Induced isometry from the quotient metric space into a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (A : Pseudometric-Space l1 l2)
  (B : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space A (pseudometric-Metric-Space B))
  where

  map-isometry-metric-quotient-Pseudometric-Space :
    map-Metric-Space
      ( metric-quotient-Pseudometric-Space A)
      ( B)
  map-isometry-metric-quotient-Pseudometric-Space =
    map-short-map-metric-quotient-Pseudometric-space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  htpy-map-isometry-metric-quotient-Pseudometric-Space :
    ( ( map-isometry-metric-quotient-Pseudometric-Space) ∘
      ( map-metric-quotient-Pseudometric-Space A)) ~
    ( map-isometry-Pseudometric-Space A (pseudometric-Metric-Space B) f)
  htpy-map-isometry-metric-quotient-Pseudometric-Space =
    htpy-map-short-map-metric-quotient-Pseudometric-Space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))

  compute-map-isometry-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space A) →
    {x : type-Pseudometric-Space A} →
    is-in-class-metric-quotient-Pseudometric-Space A X x →
    map-isometry-metric-quotient-Pseudometric-Space X ＝
    map-isometry-Pseudometric-Space
      ( A)
      ( pseudometric-Metric-Space B)
      ( f)
      ( x)
  compute-map-isometry-metric-quotient-Pseudometric-Space =
    compute-map-short-map-metric-quotient-Pseudometric-Space
      ( A)
      ( B)
      ( short-map-isometry-Pseudometric-Space
        ( A)
        ( pseudometric-Metric-Space B)
        ( f))
```

### Coherent isometries from the metric quotient in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M)
  where

  coh-triangle-prop-isometry-metric-quotient-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  coh-triangle-prop-isometry-metric-quotient-Pseudometric-Space =
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

  coh-triangle-isometry-metric-quotient-Pseudometric-Space :
    UU (l1 ⊔ l1')
  coh-triangle-isometry-metric-quotient-Pseudometric-Space =
    type-Prop
      coh-triangle-prop-isometry-metric-quotient-Pseudometric-Space

  is-prop-coh-triangle-isometry-metric-quotient-Pseudometric-Space :
    is-prop
      coh-triangle-isometry-metric-quotient-Pseudometric-Space
  is-prop-coh-triangle-isometry-metric-quotient-Pseudometric-Space =
    is-prop-type-Prop
      coh-triangle-prop-isometry-metric-quotient-Pseudometric-Space

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  coh-isometry-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  coh-isometry-metric-quotient-Pseudometric-Space =
    Σ ( isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M)
      ( coh-triangle-isometry-metric-quotient-Pseudometric-Space P M f)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  (coh-f : coh-isometry-metric-quotient-Pseudometric-Space P M f)
  where

  isometry-coh-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M
  isometry-coh-isometry-metric-quotient-Pseudometric-Space = pr1 coh-f

  map-isometry-coh-isometry-metric-quotient-Pseudometric-Space :
    map-Metric-Space (metric-quotient-Pseudometric-Space P) M
  map-isometry-coh-isometry-metric-quotient-Pseudometric-Space =
    map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( isometry-coh-isometry-metric-quotient-Pseudometric-Space)

  coh-triangle-coh-isometry-metric-quotient-Pseudometric-Space :
    coh-triangle-isometry-metric-quotient-Pseudometric-Space P M f
      isometry-coh-isometry-metric-quotient-Pseudometric-Space
  coh-triangle-coh-isometry-metric-quotient-Pseudometric-Space = pr2 coh-f
```

## Properties

### The induced map from the quotient metric space into a metric space is an isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  preserves-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space :
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
      ( map-isometry-metric-quotient-Pseudometric-Space P M f x)
      ( map-isometry-metric-quotient-Pseudometric-Space P M f y)
  preserves-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space =
    is-short-map-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-Metric-Space M)
        ( f))

  reflects-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space :
    (d : ℚ⁺) →
    (x y : type-metric-quotient-Pseudometric-Space P) →
    neighborhood-Metric-Space
      ( M)
      ( d)
      ( map-isometry-metric-quotient-Pseudometric-Space P M f x)
      ( map-isometry-metric-quotient-Pseudometric-Space P M f y) →
    neighborhood-metric-quotient-Pseudometric-Space
      ( P)
      ( d)
      ( x)
      ( y)
  reflects-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space
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
        ( compute-map-isometry-metric-quotient-Pseudometric-Space P M f X x∈X)
        ( compute-map-isometry-metric-quotient-Pseudometric-Space P M f Y y∈Y)
        ( N⟨fX,fY⟩))

  is-isometry-map-isometry-metric-quotient-Pseudometric-Space :
    is-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( map-isometry-metric-quotient-Pseudometric-Space P M f)
  is-isometry-map-isometry-metric-quotient-Pseudometric-Space d x y =
    ( ( preserves-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space
        ( d)
        ( x)
        ( y)) ,
      ( reflects-neighborhoods-map-isometry-metric-quotient-Pseudometric-Space
        ( d)
        ( x)
        ( y)))
```

### The coherent induced isometry form the quotient metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  isometry-map-isometry-metric-quotient-Pseudometric-Space :
    isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M
  isometry-map-isometry-metric-quotient-Pseudometric-Space =
    ( map-isometry-metric-quotient-Pseudometric-Space P M f ,
      is-isometry-map-isometry-metric-quotient-Pseudometric-Space P M f)

  coh-triangle-isometry-map-isometry-metric-quotient-Pseudometric-Space :
    coh-triangle-isometry-metric-quotient-Pseudometric-Space P M f
      ( isometry-map-isometry-metric-quotient-Pseudometric-Space)
  coh-triangle-isometry-map-isometry-metric-quotient-Pseudometric-Space =
    coh-triangle-short-map-short-map-metric-quotient-Pseudometric-Space P M
      ( short-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f)

  coh-isometry-map-isometry-metric-quotient-Pseudometric-Space :
    coh-isometry-metric-quotient-Pseudometric-Space P M f
  coh-isometry-map-isometry-metric-quotient-Pseudometric-Space =
    ( isometry-map-isometry-metric-quotient-Pseudometric-Space ,
      coh-triangle-isometry-map-isometry-metric-quotient-Pseudometric-Space)
```

### All coherent isometries from the metric quotient are homotopic to the induced isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  all-htpy-coh-isometry-metric-quotient-Pseudometric-Space :
    (g : coh-isometry-metric-quotient-Pseudometric-Space P M f) →
    htpy-map-isometry-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( isometry-map-isometry-metric-quotient-Pseudometric-Space P M f)
      ( isometry-coh-isometry-metric-quotient-Pseudometric-Space P M f g)
  all-htpy-coh-isometry-metric-quotient-Pseudometric-Space g =
    all-htpy-coh-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( short-map-isometry-Pseudometric-Space P (pseudometric-Metric-Space M) f)
      ( map-Σ-map-base
        ( short-map-isometry-Metric-Space (metric-quotient-Pseudometric-Space
          ( P))
          ( M))
        ( coh-triangle-short-map-metric-quotient-Pseudometric-Space P M
          ( short-map-isometry-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)))
        ( g))
```

### All coherent isometries from the metric quotient are equal to the coherent induced isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  contraction-coh-isometry-metric-quotient-Pseudometric-Space :
    (g : coh-isometry-metric-quotient-Pseudometric-Space P M f) →
    coh-isometry-map-isometry-metric-quotient-Pseudometric-Space P M f ＝ g
  contraction-coh-isometry-metric-quotient-Pseudometric-Space g =
    eq-type-subtype
      ( coh-triangle-prop-isometry-metric-quotient-Pseudometric-Space P M f)
      ( eq-htpy-map-isometry-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( M)
        ( all-htpy-coh-isometry-metric-quotient-Pseudometric-Space P M f g))
```

### The type of coherent isometries from the metric quotient is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-contr-coh-isometry-metric-quotient-Pseudometric-Space :
    is-contr
      ( coh-isometry-metric-quotient-Pseudometric-Space P M f)
  is-contr-coh-isometry-metric-quotient-Pseudometric-Space =
    ( coh-isometry-map-isometry-metric-quotient-Pseudometric-Space P M f ,
      contraction-coh-isometry-metric-quotient-Pseudometric-Space P M f)
```

### Coherent isometries from the metric quotient are equivalent to fibers of the precomposition by the natural isometry of metric quotients

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  equiv-coh-isometry-fiber-precomp-isometry-metric-quotient-Pseudoemtric-Space :
    ( fiber (precomp-isometry-metric-quotient-Pseudometric-Space P M) f) ≃
    ( coh-isometry-metric-quotient-Pseudometric-Space P M f)
  equiv-coh-isometry-fiber-precomp-isometry-metric-quotient-Pseudoemtric-Space
    =
    equiv-tot
      ( λ g →
        equiv-eq-htpy-map-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-isometry-metric-quotient-Pseudometric-Space P M g)
          ( f))
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
      ( coh-isometry-metric-quotient-Pseudometric-Space P M f)
      ( equiv-coh-isometry-fiber-precomp-isometry-metric-quotient-Pseudoemtric-Space
        ( P)
        ( M)
        ( f))
      ( is-contr-coh-isometry-metric-quotient-Pseudometric-Space P M f)

  is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space :
    is-equiv
      (precomp-isometry-metric-quotient-Pseudometric-Space P M)
  is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space =
    is-equiv-is-contr-map
      ( is-contr-map-precomp-isometry-metric-quotient-Pseudometric-Space)
```

### The equivalence between isometries from a pseudometric space in a metric space and isometries from the metric quotient

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-isometry-metric-quotient-Pseudometric-Space :
    ( isometry-Metric-Space (metric-quotient-Pseudometric-Space P) M) ≃
    ( isometry-Pseudometric-Space P (pseudometric-Metric-Space M))
  equiv-isometry-metric-quotient-Pseudometric-Space =
    ( precomp-isometry-metric-quotient-Pseudometric-Space P M ,
      is-equiv-precomp-isometry-metric-quotient-Pseudometric-Space P M)
```
