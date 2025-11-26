# Cauchy metric extensions of pseudometric spaces

```agda
module metric-spaces.cauchy-metric-extensions-of-pseudometric-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.cauchy-approximations-metric-quotients-of-pseudometric-spaces
open import metric-spaces.cauchy-approximations-metric-spaces
open import metric-spaces.cauchy-approximations-pseudometric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-metric-spaces
open import metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces
open import metric-spaces.complete-metric-spaces
open import metric-spaces.convergent-cauchy-approximations-metric-spaces
open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.functions-pseudometric-spaces
open import metric-spaces.isometries-metric-spaces
open import metric-spaces.isometries-pseudometric-spaces
open import metric-spaces.limits-of-cauchy-approximations-metric-spaces
open import metric-spaces.limits-of-cauchy-approximations-pseudometric-spaces
open import metric-spaces.metric-extensions-of-pseudometric-spaces
open import metric-spaces.metric-quotients-of-pseudometric-spaces
open import metric-spaces.metric-spaces
open import metric-spaces.precategory-of-metric-spaces-and-short-functions
open import metric-spaces.pseudometric-spaces
open import metric-spaces.rational-neighborhood-relations
open import metric-spaces.short-functions-metric-spaces
open import metric-spaces.short-functions-pseudometric-spaces
open import metric-spaces.similarity-of-elements-pseudometric-spaces
```

</details>

## Idea

A [metric extension](metric-spaces.metric-extensions-of-pseudometric-spaces.md)
`f : P → M` of a [pseudometric space](metric-spaces.pseudometric-spaces.md) is a
{{#concept "Cauchy metric extension" Disambiguation="of a pseudometric space" Agda=cauchy-Metric-Extension}}
if there exists some isometry `g : C P → M` such that

```text
  g ∘ κ ~ f
```

where `C P` is the
[cauchy pseudocompletion](metric-spaces.cauchy-pseudocompletion-of-pseudometric-spaces.md)
of `P` and `κ : P → C P` the natural isometry of cauchy pseudocompletions.

Any such `g : C P → M` is unique and, for any
[Cauchy approximation](metric-spaces.cauchy-approximations-pseudometric-spaces.md)
`u : C P`, `g u` is the limit in `M` of the image `f⋆u : C M`. I.e., **Cauchy
metric extensions** are metric extensions such that the images of Cauchy
approximations are convergent in the target
[metric space](metric-spaces.metric-spaces.md).

Any metric extension of the Cauchy pseudocompletion of a pseudometric space
induces a Cauchy metric extension of this pseudometric space. This mapping is an
[equivalence](foundation.equivalences.md) so **Cauchy metric extensions** are
equivalent to metric extensions of the Cauchy pseudocompletion.

## Definitions

### The property of being a coherent isometry from the Cauchy pseudocompletion into the codomain of a metric extension

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Metric-Extension P M))
  where

  coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension :
    UU (l1 ⊔ l3)
  coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension =
    htpy-isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-Metric-Extension P M)
      ( comp-isometry-Pseudometric-Space
        ( P)
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( g)
        ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))
      ( isometry-metric-space-Metric-Extension P M)

  is-prop-coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension :
    is-prop coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension
  is-prop-coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension =
    is-prop-Π
      ( λ x →
        is-set-type-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( map-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( pseudometric-space-Metric-Extension P M)
            ( g)
            ( map-cauchy-pseudocompletion-Pseudometric-Space P x))
          ( map-isometry-metric-space-Metric-Extension P M x))

  coherence-triangle-prop-isometry-cauchy-pseudocompletion-Metric-Space :
    Prop (l1 ⊔ l3)
  coherence-triangle-prop-isometry-cauchy-pseudocompletion-Metric-Space =
    ( coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension ,
      is-prop-coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension)
```

### The condition of being a Cauchy metric extension

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Metric-Extension l3 l4 P)
  where

  is-cauchy-Metric-Extension : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-Metric-Extension =
    type-subtype
      ( coherence-triangle-prop-isometry-cauchy-pseudocompletion-Metric-Space
        ( P)
        ( M))
```

### The type of Cauchy metric extensions of a pseudometric space

```agda
module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  Cauchy-Metric-Extension : UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  Cauchy-Metric-Extension =
    Σ ( Metric-Extension l3 l4 P)
      ( is-cauchy-Metric-Extension P)

module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  (M : Cauchy-Metric-Extension l3 l4 P)
  where

  extension-Cauchy-Metric-Extension : Metric-Extension l3 l4 P
  extension-Cauchy-Metric-Extension = pr1 M

  metric-space-Cauchy-Metric-Extension : Metric-Space l3 l4
  metric-space-Cauchy-Metric-Extension =
    metric-space-Metric-Extension P extension-Cauchy-Metric-Extension

  pseudometric-space-Cauchy-Metric-Extension : Pseudometric-Space l3 l4
  pseudometric-space-Cauchy-Metric-Extension =
    pseudometric-space-Metric-Extension P
      extension-Cauchy-Metric-Extension

  isometry-metric-space-Cauchy-Metric-Extension :
    isometry-Pseudometric-Space
      ( P)
      ( pseudometric-space-Cauchy-Metric-Extension)
  isometry-metric-space-Cauchy-Metric-Extension =
    isometry-metric-space-Metric-Extension
      ( P)
      ( extension-Cauchy-Metric-Extension)

  is-cauchy-metric-extension-Cauchy-Metric-Extension :
    is-cauchy-Metric-Extension
      ( P)
      ( extension-Cauchy-Metric-Extension)
  is-cauchy-metric-extension-Cauchy-Metric-Extension = pr2 M

  isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Cauchy-Metric-Extension)
  isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension =
    pr1 is-cauchy-metric-extension-Cauchy-Metric-Extension

  coh-isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension :
    coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension
      ( P)
      ( extension-Cauchy-Metric-Extension)
      ( isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension)
  coh-isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension =
    pr2 is-cauchy-metric-extension-Cauchy-Metric-Extension

  extension-cauchy-pseudocompletion-Cauchy-Metric-Extension :
    Metric-Extension l3 l4 (cauchy-pseudocompletion-Pseudometric-Space P)
  extension-cauchy-pseudocompletion-Cauchy-Metric-Extension =
    ( metric-space-Cauchy-Metric-Extension ,
      isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension)
```

## Properties

### The values of a coherent isometries are the limits of images of Cauchy approximations

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( g :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Metric-Extension P M))
  ( coh-g :
    coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension P M g)
  ( u : cauchy-approximation-Pseudometric-Space P)
  where abstract

  lemma-sim-coherent-isometry-cauchy-pseudocompletion-Metric-Extension :
    sim-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M))
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
      ( map-cauchy-pseudocompletion-Metric-Space
        ( metric-space-Metric-Extension P M)
        ( map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-space-Metric-Extension P M)
          ( g)
          ( u)))
  lemma-sim-coherent-isometry-cauchy-pseudocompletion-Metric-Extension =
    inv-tr
      ( λ z →
        sim-Pseudometric-Space
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-Metric-Extension P M))
          ( z)
          ( map-cauchy-pseudocompletion-Metric-Space
            ( metric-space-Metric-Extension P M)
            ( map-isometry-Pseudometric-Space
              ( cauchy-pseudocompletion-Pseudometric-Space P)
              ( pseudometric-space-Metric-Extension P M)
              ( g)
              ( u))))
      ( eq-mapM-u)
      ( lemma-sim-κgu)
    where

    eq-mapM-u :
      map-cauchy-pseudocompletion-Metric-Extension P M u ＝
      map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-space-Metric-Extension P M)
        ( comp-isometry-Pseudometric-Space
          ( P)
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-space-Metric-Extension P M)
          ( g)
          ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))
        ( u)
    eq-mapM-u =
      htpy-map-cauchy-approximation-isometry-Pseudometric-Space
        ( P)
        ( pseudometric-space-Metric-Extension P M)
        ( isometry-metric-space-Metric-Extension P M)
        ( comp-isometry-Pseudometric-Space
          ( P)
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( pseudometric-space-Metric-Extension P M)
          ( g)
          ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))
        ( inv-htpy coh-g)
        ( u)

    lemma-sim-κgu :
      sim-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M))
        ( map-cauchy-approximation-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-space-Metric-Extension P M)
          ( comp-isometry-Pseudometric-Space
            ( P)
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( pseudometric-space-Metric-Extension P M)
            ( g)
            ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))
            ( u))
        ( map-cauchy-pseudocompletion-Metric-Space
          ( metric-space-Metric-Extension P M)
          ( map-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( pseudometric-space-Metric-Extension P M)
            ( g)
            ( u)))
    lemma-sim-κgu =
      tr
        ( λ z →
          sim-Pseudometric-Space
            ( cauchy-pseudocompletion-Metric-Space
              ( metric-space-Metric-Extension P M))
            ( map-cauchy-approximation-isometry-Pseudometric-Space
              ( P)
              ( pseudometric-space-Metric-Extension P M)
              ( comp-isometry-Pseudometric-Space
                ( P)
                ( cauchy-pseudocompletion-Pseudometric-Space P)
                ( pseudometric-space-Metric-Extension P M)
                ( g)
                ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))
              ( u))
            ( z))
        ( htpy-map-cauchy-pseudocompletion-Metric-Extension
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( metric-space-Metric-Extension P M , g)
          ( u))
        ( preserves-sim-map-isometry-Pseudometric-Space
          ( cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P))
          ( cauchy-pseudocompletion-Metric-Space
            ( metric-space-Metric-Extension P M))
          ( isometry-map-cauchy-approximation-isometry-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( pseudometric-space-Metric-Extension P M)
            ( g))
          ( map-cauchy-approximation-isometry-Pseudometric-Space
            ( P)
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( isometry-cauchy-pseudocompletion-Pseudometric-Space P)
            ( u))
          ( map-cauchy-pseudocompletion-Pseudometric-Space
            ( cauchy-pseudocompletion-Pseudometric-Space P)
            ( u))
          ( sim-map-cauchy-approximation-cauchy-pseudocompletion-Pseudometric-Space
            ( P)
            ( u)))

  is-limit-coherent-isometry-cauchy-pseudocompletion-Metric-Extension :
    is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( g)
        ( u))
  is-limit-coherent-isometry-cauchy-pseudocompletion-Metric-Extension =
    is-limit-sim-const-cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( g)
        ( u))
      ( lemma-sim-coherent-isometry-cauchy-pseudocompletion-Metric-Extension)
```

### All coherent isometries from the cauchy pseudocompletion are homotopic

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  ( g h :
    isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Metric-Extension P M))
  ( coh-g :
    coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension P M g)
  ( coh-h :
    coherence-triangle-isometry-cauchy-pseudocompletion-Metric-Extension P M h)
  where abstract

  all-htpy-is-cauchy-extension-Metric-Space :
    htpy-isometry-Pseudometric-Space
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( pseudometric-space-Metric-Extension P M)
      ( g)
      ( h)
  all-htpy-is-cauchy-extension-Metric-Space u =
    all-eq-is-limit-cauchy-approximation-Metric-Space
      ( metric-space-Metric-Extension P M)
      ( map-cauchy-pseudocompletion-Metric-Extension P M u)
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( g)
        ( u))
      ( map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( h)
        ( u))
      ( is-limit-coherent-isometry-cauchy-pseudocompletion-Metric-Extension P M
        ( g)
        ( coh-g)
        ( u))
      ( is-limit-coherent-isometry-cauchy-pseudocompletion-Metric-Extension P M
        ( h)
        ( coh-h)
        ( u))
```

### All coherent isometries from the cauchy pseudocompletion are equal

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  where abstract

  all-eq-is-cauchy-Metric-Extension :
    ( g h :
      type-subtype
        ( coherence-triangle-prop-isometry-cauchy-pseudocompletion-Metric-Space
          ( P)
          ( M))) →
    ( g ＝ h)
  all-eq-is-cauchy-Metric-Extension (g , coh-g) (h , coh-h) =
    eq-type-subtype
      ( coherence-triangle-prop-isometry-cauchy-pseudocompletion-Metric-Space
        ( P)
        ( M))
      ( eq-htpy-map-isometry-Pseudometric-Space
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension P M)
        ( all-htpy-is-cauchy-extension-Metric-Space
          ( P)
          ( M)
          ( g)
          ( h)
          ( coh-g)
          ( coh-h)))
```

### Being a Cauchy metric extension is a proposition

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4 P)
  where

  abstract
    is-prop-is-cauchy-Metric-Extension :
      is-prop (is-cauchy-Metric-Extension P M)
    is-prop-is-cauchy-Metric-Extension =
      is-prop-all-elements-equal
        ( all-eq-is-cauchy-Metric-Extension P M)

  is-cauchy-prop-Metric-Extension : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-cauchy-prop-Metric-Extension =
    (is-cauchy-Metric-Extension P M , is-prop-is-cauchy-Metric-Extension)
```

### Metric extensions of the Cauchy pseudocompletion are Cauchy metric extensions

```agda
module _
  { l1 l2 l3 l4 : Level}
  ( P : Pseudometric-Space l1 l2)
  ( M : Metric-Extension l3 l4
    ( cauchy-pseudocompletion-Pseudometric-Space P))
  where

  extension-cauchy-pseudocompletion-Metric-Extension :
    Metric-Extension l3 l4 P
  extension-cauchy-pseudocompletion-Metric-Extension =
    ( ( metric-space-Metric-Extension
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( M)) ,
      ( comp-isometry-Pseudometric-Space
        ( P)
        ( cauchy-pseudocompletion-Pseudometric-Space P)
        ( pseudometric-space-Metric-Extension
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( M))
        ( isometry-metric-space-Metric-Extension
          ( cauchy-pseudocompletion-Pseudometric-Space P)
          ( M)))
        ( isometry-cauchy-pseudocompletion-Pseudometric-Space P))

  is-cauchy-extension-cauchy-pseudocompletion-Metric-Extension :
    is-cauchy-Metric-Extension
      ( P)
      ( extension-cauchy-pseudocompletion-Metric-Extension)
  pr1 is-cauchy-extension-cauchy-pseudocompletion-Metric-Extension =
    isometry-metric-space-Metric-Extension
      ( cauchy-pseudocompletion-Pseudometric-Space P)
      ( M)
  pr2 is-cauchy-extension-cauchy-pseudocompletion-Metric-Extension = refl-htpy

  cauchy-extension-cauchy-pseudocompletion-Metric-Extension :
    Cauchy-Metric-Extension l3 l4 P
  cauchy-extension-cauchy-pseudocompletion-Metric-Extension =
    ( extension-cauchy-pseudocompletion-Metric-Extension ,
      is-cauchy-extension-cauchy-pseudocompletion-Metric-Extension)
```

### Cauchy metric extensions are equivalent to metric extensions of the Cauchy pseudocompletion

```agda
module _
  {l1 l2 l3 l4 : Level}
  (P : Pseudometric-Space l1 l2)
  where

  is-section-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension :
    ( M : Cauchy-Metric-Extension l3 l4 P) →
    ( cauchy-extension-cauchy-pseudocompletion-Metric-Extension
      ( P)
      ( extension-cauchy-pseudocompletion-Cauchy-Metric-Extension P M)) ＝
    ( M)
  is-section-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension M =
    eq-type-subtype
      ( is-cauchy-prop-Metric-Extension P)
      ( eq-pair-eq-fiber
        ( eq-htpy-map-isometry-Pseudometric-Space
          ( P)
          ( pseudometric-space-Cauchy-Metric-Extension P M)
          ( coh-isometry-cauchy-pseudocompletion-Cauchy-Metric-Extension P M)))

  is-retraction-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension :
    ( N :
      Metric-Extension l3 l4
        ( cauchy-pseudocompletion-Pseudometric-Space P)) →
    ( extension-cauchy-pseudocompletion-Cauchy-Metric-Extension P
      ( cauchy-extension-cauchy-pseudocompletion-Metric-Extension P N)) ＝
    ( N)
  is-retraction-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension N =
    refl

module _
  {l1 l2 : Level}
  (l3 l4 : Level)
  (P : Pseudometric-Space l1 l2)
  where

  equiv-Cauchy-Metric-Extension :
    Metric-Extension l3 l4 (cauchy-pseudocompletion-Pseudometric-Space P) ≃
    Cauchy-Metric-Extension l3 l4 P
  pr1 equiv-Cauchy-Metric-Extension =
    cauchy-extension-cauchy-pseudocompletion-Metric-Extension P
  pr2 equiv-Cauchy-Metric-Extension =
    is-equiv-is-invertible
      ( extension-cauchy-pseudocompletion-Cauchy-Metric-Extension
        ( P))
      ( is-section-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension
        ( P))
      ( is-retraction-extension-cauchy-pseudocompletion-Cauchy-Metric-Extension
        ( P))
```
