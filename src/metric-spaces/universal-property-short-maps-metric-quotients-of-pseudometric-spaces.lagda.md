# Universal property of metric quotients of pseudometric spaces and short maps

```agda
{-# OPTIONS --lossy-unification #-}

module metric-spaces.universal-property-short-maps-metric-quotients-of-pseudometric-spaces where
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
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import metric-spaces.maps-metric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-maps-metric-spaces
open import metric-spaces.short-maps-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
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

maps [short maps](metric-spaces.short-maps-metric-spaces.md) `[P] → M` to a
[metric space](metric-spaces.metric-spaces.md) to
[short maps](metric-spaces.short-maps-pseudometric-spaces.md) from `P` to the
underlying pseudometric space of `M`.

This action is an [equivalence](foundation.equivalences.md) so short maps from a
pseudometric space to a metric space are
{{#concept "equivalent" Disambiguation="short maps of metric quotients of pseudometric spaces Agda=equiv-short-map-metric-quotient-Pseudometric-Space}}
to short maps from its metric quotient.

Equivalently, the metric quotient satisfies the following
{{#concept "universal property" Disambiguation="of metric quotients and short maps" Agda=is-contr-coh-short-map-metric-quotient-Pseudometric-Space}}:
for any short map `f : P → M` from a pseudometric space in a metric space, there
[exists a unique](foundation-core.contractible-types.md) short map `g : [P] → M`
such that

```text
g ∘ q ~ f.
```

## Definitions

### Precomposition of short maps by the metric quotient isometry

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  precomp-short-map-metric-quotient-Pseudometric-Space :
    short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M →
    short-map-Pseudometric-Space P (pseudometric-Metric-Space M)
  precomp-short-map-metric-quotient-Pseudometric-Space f =
    comp-short-map-Pseudometric-Space
      ( P)
      ( pseudometric-metric-quotient-Pseudometric-Space P)
      ( pseudometric-Metric-Space M)
      ( f)
      ( short-map-metric-quotient-Pseudometric-Space P)
```

### The induced map from the quotient metric space by an short map in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  map-short-map-metric-quotient-Pseudometric-space :
    map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
  map-short-map-metric-quotient-Pseudometric-space =
    inv-precomp-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space P)
      ( set-Metric-Space M)
      ( reflecting-map-short-map-metric-space-Pseudometric-Space P M f)

  htpy-map-short-map-metric-quotient-Pseudometric-Space :
    ( ( map-short-map-metric-quotient-Pseudometric-space) ∘
      ( map-metric-quotient-Pseudometric-Space P)) ~
    ( map-short-map-Pseudometric-Space P (pseudometric-Metric-Space M) f)
  htpy-map-short-map-metric-quotient-Pseudometric-Space =
    is-section-inv-precomp-set-quotient
      ( equivalence-relation-sim-Pseudometric-Space P)
      ( set-Metric-Space M)
      ( reflecting-map-short-map-metric-space-Pseudometric-Space P M f)

  compute-map-short-map-metric-quotient-Pseudometric-Space :
    (X : type-metric-quotient-Pseudometric-Space P) →
    {x : type-Pseudometric-Space P} →
    is-in-class-metric-quotient-Pseudometric-Space P X x →
    map-short-map-metric-quotient-Pseudometric-space X ＝
    map-short-map-Pseudometric-Space P (pseudometric-Metric-Space M) f x
  compute-map-short-map-metric-quotient-Pseudometric-Space X {x} x∈X =
    tr
      ( λ Y →
        map-short-map-metric-quotient-Pseudometric-space Y ＝
        map-short-map-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( f)
          ( x))
      ( eq-set-quotient-equivalence-class-set-quotient
        ( equivalence-relation-sim-Pseudometric-Space P)
        ( X)
        ( x∈X))
      ( htpy-map-short-map-metric-quotient-Pseudometric-Space x)
```

### Coherent short maps from the metric quotient in a metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  (g : short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M)
  where

  coh-triangle-prop-short-map-metric-quotient-Pseudometric-Space :
    Prop (l1 ⊔ l1')
  coh-triangle-prop-short-map-metric-quotient-Pseudometric-Space =
    Π-Prop
      ( type-Pseudometric-Space P)
      ( λ x →
        eq-prop-Metric-Space
          ( M)
          ( map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( precomp-short-map-metric-quotient-Pseudometric-Space P M g)
            ( x))
          ( map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)
            ( x)))

  coh-triangle-short-map-metric-quotient-Pseudometric-Space :
    UU (l1 ⊔ l1')
  coh-triangle-short-map-metric-quotient-Pseudometric-Space =
    type-Prop
      coh-triangle-prop-short-map-metric-quotient-Pseudometric-Space

  is-prop-coh-triangle-short-map-metric-quotient-Pseudometric-Space :
    is-prop
      coh-triangle-short-map-metric-quotient-Pseudometric-Space
  is-prop-coh-triangle-short-map-metric-quotient-Pseudometric-Space =
    is-prop-type-Prop
      coh-triangle-prop-short-map-metric-quotient-Pseudometric-Space

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  coh-short-map-metric-quotient-Pseudometric-Space : UU (l1 ⊔ l2 ⊔ l1' ⊔ l2')
  coh-short-map-metric-quotient-Pseudometric-Space =
    Σ ( short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M)
      ( coh-triangle-short-map-metric-quotient-Pseudometric-Space P M f)

module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  (coh-f : coh-short-map-metric-quotient-Pseudometric-Space P M f)
  where

  short-map-coh-short-map-metric-quotient-Pseudometric-Space :
    short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M
  short-map-coh-short-map-metric-quotient-Pseudometric-Space = pr1 coh-f

  map-short-map-coh-short-map-metric-quotient-Pseudometric-Space :
    map-Metric-Space (metric-quotient-Pseudometric-Space P) M
  map-short-map-coh-short-map-metric-quotient-Pseudometric-Space =
    map-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( short-map-coh-short-map-metric-quotient-Pseudometric-Space)

  coh-triangle-coh-short-map-metric-quotient-Pseudometric-Space :
    coh-triangle-short-map-metric-quotient-Pseudometric-Space P M f
      short-map-coh-short-map-metric-quotient-Pseudometric-Space
  coh-triangle-coh-short-map-metric-quotient-Pseudometric-Space = pr2 coh-f
```

## Properties

### The induced map from the quotient metric space into a metric space is short

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  is-short-map-short-map-metric-quotient-Pseudometric-Space :
    is-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( map-short-map-metric-quotient-Pseudometric-space P M f)
  is-short-map-short-map-metric-quotient-Pseudometric-Space
    d X Y N⟨X,Y⟩ =
    let
      open
        do-syntax-trunc-Prop
          ( neighborhood-prop-Metric-Space
            ( M)
            ( d)
            ( map-short-map-metric-quotient-Pseudometric-space P M f X)
            ( map-short-map-metric-quotient-Pseudometric-space P M f Y))
      in do
        ( x , x∈X) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space P)
            ( X)
        ( y , y∈Y) ←
          is-inhabited-subtype-set-quotient
            ( equivalence-relation-sim-Pseudometric-Space P)
            ( Y)

        binary-tr
          ( neighborhood-Metric-Space M d)
          ( inv
            ( compute-map-short-map-metric-quotient-Pseudometric-Space
              ( P)
              ( M)
              ( f)
              ( X)
              ( x∈X)))
          ( inv
            ( compute-map-short-map-metric-quotient-Pseudometric-Space
              ( P)
              ( M)
              ( f)
              ( Y)
              ( y∈Y)))
          ( is-short-map-short-map-Pseudometric-Space
            ( P)
            ( pseudometric-Metric-Space M)
            ( f)
            ( d)
            ( x)
            ( y)
            ( N⟨X,Y⟩ (x , x∈X) (y , y∈Y)))
```

### The coherent short induced map from the quotient metric space

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  short-map-short-map-metric-quotient-Pseudometric-Space :
    short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M
  short-map-short-map-metric-quotient-Pseudometric-Space =
    ( map-short-map-metric-quotient-Pseudometric-space P M f ,
      is-short-map-short-map-metric-quotient-Pseudometric-Space P M f)

  coh-triangle-short-map-short-map-metric-quotient-Pseudometric-Space :
    coh-triangle-short-map-metric-quotient-Pseudometric-Space P M f
      ( short-map-short-map-metric-quotient-Pseudometric-Space)
  coh-triangle-short-map-short-map-metric-quotient-Pseudometric-Space x =
    compute-map-short-map-metric-quotient-Pseudometric-Space
      ( P)
      ( M)
      ( f)
      ( map-metric-quotient-Pseudometric-Space P x)
      ( is-in-class-map-quotient-Pseudometric-Space P x)

  coh-short-map-short-map-metric-quotient-Pseudometric-Space :
    coh-short-map-metric-quotient-Pseudometric-Space P M f
  coh-short-map-short-map-metric-quotient-Pseudometric-Space =
    ( short-map-short-map-metric-quotient-Pseudometric-Space ,
      coh-triangle-short-map-short-map-metric-quotient-Pseudometric-Space)
```

### All coherent short maps from the metric quotient are homotopic to the induced short map

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  all-htpy-coh-short-map-metric-quotient-Pseudometric-Space :
    (g : coh-short-map-metric-quotient-Pseudometric-Space P M f) →
    htpy-map-short-map-Metric-Space
      ( metric-quotient-Pseudometric-Space P)
      ( M)
      ( short-map-short-map-metric-quotient-Pseudometric-Space P M f)
      ( short-map-coh-short-map-metric-quotient-Pseudometric-Space P M f g)
  all-htpy-coh-short-map-metric-quotient-Pseudometric-Space g X =
    let
      open
        do-syntax-trunc-Prop
          ( eq-prop-Metric-Space M
            ( map-short-map-metric-quotient-Pseudometric-space P M f X)
            ( map-short-map-coh-short-map-metric-quotient-Pseudometric-Space
              ( P)
              ( M)
              ( f)
              ( g)
              ( X)))

    in do
      ( x , x∈X) ←
        is-inhabited-class-metric-quotient-Pseudometric-Space P X

      let
        lemma-lhs =
          compute-map-short-map-metric-quotient-Pseudometric-Space P M f X x∈X

        lemma-mhs =
          coh-triangle-coh-short-map-metric-quotient-Pseudometric-Space
            ( P)
            ( M)
            ( f)
            ( g)
            ( x)

        lemma-rhs =
          ap
            ( map-short-map-coh-short-map-metric-quotient-Pseudometric-Space
              ( P)
              ( M)
              ( f)
              ( g))
            ( eq-map-is-in-class-metric-quotient-Pseudometric-Space P X x∈X)

      lemma-lhs ∙ (inv lemma-mhs) ∙ lemma-rhs
```

### All coherent short maps from the metric quotient are equal to the coherent induced short map

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where abstract

  contraction-coh-short-map-metric-quotient-Pseudometric-Space :
    (g : coh-short-map-metric-quotient-Pseudometric-Space P M f) →
    coh-short-map-short-map-metric-quotient-Pseudometric-Space P M f ＝ g
  contraction-coh-short-map-metric-quotient-Pseudometric-Space g =
    eq-type-subtype
      ( coh-triangle-prop-short-map-metric-quotient-Pseudometric-Space P M f)
      ( eq-htpy-map-short-map-Metric-Space
        ( metric-quotient-Pseudometric-Space P)
        ( M)
        ( short-map-short-map-metric-quotient-Pseudometric-Space P M f)
        ( short-map-coh-short-map-metric-quotient-Pseudometric-Space P M f g)
        ( all-htpy-coh-short-map-metric-quotient-Pseudometric-Space P M f g))
```

### The type of coherent short maps from the metric quotient is contractible

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  is-contr-coh-short-map-metric-quotient-Pseudometric-Space :
    is-contr
      ( coh-short-map-metric-quotient-Pseudometric-Space P M f)
  is-contr-coh-short-map-metric-quotient-Pseudometric-Space =
    ( coh-short-map-short-map-metric-quotient-Pseudometric-Space P M f ,
      contraction-coh-short-map-metric-quotient-Pseudometric-Space P M f)
```

### Coherent short maps from the metric quotient are equivalent to fibers of the precomposition by the natural isometry of metric quotients

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  where

  equiv-coh-short-map-fiber-precomp-short-map-metric-quotient-Pseudoemtric-Space :
    ( fiber (precomp-short-map-metric-quotient-Pseudometric-Space P M) f) ≃
    ( coh-short-map-metric-quotient-Pseudometric-Space P M f)
  equiv-coh-short-map-fiber-precomp-short-map-metric-quotient-Pseudoemtric-Space
    =
    equiv-tot
      ( λ g →
        equiv-eq-htpy-map-short-map-Pseudometric-Space
          ( P)
          ( pseudometric-Metric-Space M)
          ( precomp-short-map-metric-quotient-Pseudometric-Space P M g)
          ( f))
```

### Precomposing by the natual isometry of metric quotients is an equivalence

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where abstract

  is-contr-map-precomp-short-map-metric-quotient-Pseudometric-Space :
    (f : short-map-Pseudometric-Space P (pseudometric-Metric-Space M)) →
    is-contr
      (fiber (precomp-short-map-metric-quotient-Pseudometric-Space P M) f)
  is-contr-map-precomp-short-map-metric-quotient-Pseudometric-Space f =
    is-contr-equiv
      ( coh-short-map-metric-quotient-Pseudometric-Space P M f)
      ( equiv-coh-short-map-fiber-precomp-short-map-metric-quotient-Pseudoemtric-Space
        ( P)
        ( M)
        ( f))
      ( is-contr-coh-short-map-metric-quotient-Pseudometric-Space P M f)

  is-equiv-precomp-short-map-metric-quotient-Pseudometric-Space :
    is-equiv
      (precomp-short-map-metric-quotient-Pseudometric-Space P M)
  is-equiv-precomp-short-map-metric-quotient-Pseudometric-Space =
    is-equiv-is-contr-map
      ( is-contr-map-precomp-short-map-metric-quotient-Pseudometric-Space)
```

### The equivalence between short maps from a pseudometric space in a metric space and short maps from the metric quotient

```agda
module _
  {l1 l2 l1' l2' : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Space l1' l2')
  where

  equiv-short-map-metric-quotient-Pseudometric-Space :
    ( short-map-Metric-Space (metric-quotient-Pseudometric-Space P) M) ≃
    ( short-map-Pseudometric-Space P (pseudometric-Metric-Space M))
  equiv-short-map-metric-quotient-Pseudometric-Space =
    ( precomp-short-map-metric-quotient-Pseudometric-Space P M ,
      is-equiv-precomp-short-map-metric-quotient-Pseudometric-Space P M)
```
