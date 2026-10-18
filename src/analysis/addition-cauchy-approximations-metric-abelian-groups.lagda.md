# Addition of Cauchy approximations in metric abelian groups

```agda
module analysis.addition-cauchy-approximations-metric-abelian-groups where
```

<details><summary>Imports</summary>

```agda
open import analysis.cauchy-approximations-metric-abelian-groups
open import analysis.cauchy-pseudocompletions-metric-abelian-groups
open import analysis.metric-abelian-groups

open import elementary-number-theory.addition-positive-rational-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.strict-inequality-positive-rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.binary-functoriality-set-quotients
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import metric-spaces.short-maps-pseudometric-spaces
```

</details>

## Idea

[Cauchy approximations](analysis.cauchy-approximations-metric-abelian-groups.md)
in [metric abelian groups](analysis.metric-abelian-groups.md) admit an addition
operation whose properties resemble an
[abelian group](group-theory.abelian-groups.md) with respect to the
[similarity relationship](metric-spaces.similarity-of-elements-pseudometric-spaces.md)
of the
[Cauchy pseudocompletion of the metric abelian group](analysis.cauchy-pseudocompletions-metric-abelian-groups.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  ((x , is-approx-x) (y , is-approx-y) :
    cauchy-approximation-Metric-Ab G)
  where

  opaque
    map-add-cauchy-approximation-Metric-Ab :
      ℚ⁺ → type-Metric-Ab G
    map-add-cauchy-approximation-Metric-Ab ε =
      let (δ , _) = bound-double-le-ℚ⁺ ε in add-Metric-Ab G (x δ) (y δ)

  abstract opaque
    unfolding map-add-cauchy-approximation-Metric-Ab

    is-cauchy-approximation-map-add-cauchy-approximation-Metric-Ab :
      is-cauchy-approximation-Metric-Ab G map-add-cauchy-approximation-Metric-Ab
    is-cauchy-approximation-map-add-cauchy-approximation-Metric-Ab δ ε =
      let
        (δ' , 2δ'<δ) = bound-double-le-ℚ⁺ δ
        (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε
      in
        monotonic-neighborhood-Metric-Ab G
          ( add-Metric-Ab G (x δ') (y δ'))
          ( add-Metric-Ab G (x ε') (y ε'))
          ( (δ' +ℚ⁺ ε') +ℚ⁺ (δ' +ℚ⁺ ε'))
          ( δ +ℚ⁺ ε)
          ( concat-eq-le-ℚ⁺
            { z = δ +ℚ⁺ ε}
            ( interchange-law-add-add-ℚ⁺ δ' ε' δ' ε')
            ( preserves-le-add-ℚ 2δ'<δ 2ε'<ε))
          ( neighborhood-add-Metric-Ab
            ( G)
            ( δ' +ℚ⁺ ε')
            ( δ' +ℚ⁺ ε')
            ( x δ')
            ( x ε')
            ( y δ')
            ( y ε')
            ( is-approx-x δ' ε')
            ( is-approx-y δ' ε'))

  add-cauchy-approximation-Metric-Ab : cauchy-approximation-Metric-Ab G
  add-cauchy-approximation-Metric-Ab =
    ( map-add-cauchy-approximation-Metric-Ab ,
      is-cauchy-approximation-map-add-cauchy-approximation-Metric-Ab)
```

## Properties

### Addition of Cauchy approximations is a similarity-preserving binary map

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  preserves-sim-add-cauchy-approximation-Metric-Ab :
    preserves-sim-binary-map-equivalence-relation
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( equivalence-relation-sim-cauchy-pseudocompletion-Metric-Ab G)
      ( add-cauchy-approximation-Metric-Ab G)
  preserves-sim-add-cauchy-approximation-Metric-Ab
    {x , is-approx-x} {x' , is-approx-x'} {y , is-approx-y} {y' , is-approx-y'}
    x~x' y~y' δ ε θ =
    let
      (δ' , 2δ'<δ) = bound-double-le-ℚ⁺ δ
      (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε
      (θ' , 2θ'<θ) = bound-double-le-ℚ⁺ θ
    in
      monotonic-neighborhood-Metric-Ab G
        ( add-Metric-Ab G (x ε') (y ε'))
        ( add-Metric-Ab G (x' θ') (y' θ'))
        ( (ε' +ℚ⁺ θ' +ℚ⁺ δ') +ℚ⁺ (ε' +ℚ⁺ θ' +ℚ⁺ δ'))
        ( ε +ℚ⁺ θ +ℚ⁺ δ)
        ( concat-eq-le-ℚ⁺
          { z = ε +ℚ⁺ θ +ℚ⁺ δ}
          ( equational-reasoning
            (ε' +ℚ⁺ θ' +ℚ⁺ δ') +ℚ⁺ (ε' +ℚ⁺ θ' +ℚ⁺ δ')
            ＝ ((ε' +ℚ⁺ θ') +ℚ⁺ (ε' +ℚ⁺ θ')) +ℚ⁺ (δ' +ℚ⁺ δ')
              by interchange-law-add-add-ℚ⁺ _ _ _ _
            ＝ (ε' +ℚ⁺ ε') +ℚ⁺ (θ' +ℚ⁺ θ') +ℚ⁺ (δ' +ℚ⁺ δ')
              by ap-add-ℚ⁺ (interchange-law-add-add-ℚ⁺ ε' θ' ε' θ') refl)
          ( preserves-le-add-ℚ
            ( preserves-le-add-ℚ 2ε'<ε 2θ'<θ)
            ( 2δ'<δ)))
        ( neighborhood-add-Metric-Ab
          ( G)
          ( ε' +ℚ⁺ θ' +ℚ⁺ δ')
          ( ε' +ℚ⁺ θ' +ℚ⁺ δ')
          ( x ε')
          ( x' θ')
          ( y ε')
          ( y' θ')
          ( x~x' δ' ε' θ')
          ( y~y' δ' ε' θ'))
```

### The addition of two constant Cauchy approximations for `x` and `y` is similar to the constant approximation for `x + y`

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  sim-add-const-cauchy-approximation-Metric-Ab :
    (x y : type-Metric-Ab G) →
    sim-cauchy-pseudocompletion-Metric-Ab G
      ( add-cauchy-approximation-Metric-Ab G
        ( const-cauchy-approximation-Metric-Ab G x)
        ( const-cauchy-approximation-Metric-Ab G y))
      ( const-cauchy-approximation-Metric-Ab G (add-Metric-Ab G x y))
  sim-add-const-cauchy-approximation-Metric-Ab x y δ ε θ =
    refl-neighborhood-Metric-Ab G (ε +ℚ⁺ θ +ℚ⁺ δ) (add-Metric-Ab G x y)
```

### Addition is associative relative to the similarity relation

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (ax@(x , is-approx-x) ay@(y , is-approx-y) az@(z , is-approx-z) :
    cauchy-approximation-Metric-Ab G)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  sim-associative-add-cauchy-approximation-Metric-Ab :
    sim-cauchy-pseudocompletion-Metric-Ab G
      ( add-cauchy-approximation-Metric-Ab G
        ( add-cauchy-approximation-Metric-Ab G ax ay)
        ( az))
      ( add-cauchy-approximation-Metric-Ab G
        ( ax)
        ( add-cauchy-approximation-Metric-Ab G ay az))
  sim-associative-add-cauchy-approximation-Metric-Ab δ ε θ =
    let
      (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε
      (ε'' , 2ε''<ε') = bound-double-le-ℚ⁺ ε'
      (θ' , 2θ'<θ) = bound-double-le-ℚ⁺ θ
      (θ'' , 2θ''<θ') = bound-double-le-ℚ⁺ θ'
      xyz1 = add-Metric-Ab G (add-Metric-Ab G (x ε'') (y ε'')) (z ε')
      xyz2 = add-Metric-Ab G (add-Metric-Ab G (x θ') (y θ'')) (z θ'')
    in
      tr
        ( neighborhood-Metric-Ab G (ε +ℚ⁺ θ +ℚ⁺ δ) xyz1)
        ( associative-add-Metric-Ab G _ _ _)
        ( monotonic-neighborhood-Metric-Ab G
          ( xyz1)
          ( xyz2)
          ( (ε'' +ℚ⁺ θ') +ℚ⁺ (ε'' +ℚ⁺ θ'') +ℚ⁺ (ε' +ℚ⁺ θ''))
          ( ε +ℚ⁺ θ +ℚ⁺ δ)
          ( concat-eq-le-ℚ⁺
            { z = ε +ℚ⁺ θ +ℚ⁺ δ}
            ( equational-reasoning
              (ε'' +ℚ⁺ θ') +ℚ⁺ (ε'' +ℚ⁺ θ'') +ℚ⁺ (ε' +ℚ⁺ θ'')
              ＝ ((ε'' +ℚ⁺ ε'') +ℚ⁺ (θ' +ℚ⁺ θ'')) +ℚ⁺ (ε' +ℚ⁺ θ'')
                by ap-add-ℚ⁺ (interchange-law-add-add-ℚ⁺ _ _ _ _) refl
              ＝ ((ε'' +ℚ⁺ ε'') +ℚ⁺ ε') +ℚ⁺ ((θ' +ℚ⁺ θ'') +ℚ⁺ θ'')
                by interchange-law-add-add-ℚ⁺ _ _ _ _
              ＝ ((ε'' +ℚ⁺ ε'') +ℚ⁺ ε') +ℚ⁺ (θ' +ℚ⁺ (θ'' +ℚ⁺ θ''))
                by ap-add-ℚ⁺ refl (associative-add-ℚ⁺ _ _ _))
            ( transitive-le-ℚ⁺
              ( ((ε'' +ℚ⁺ ε'') +ℚ⁺ ε') +ℚ⁺ (θ' +ℚ⁺ (θ'' +ℚ⁺ θ'')))
              ( (ε' +ℚ⁺ ε') +ℚ⁺ (θ' +ℚ⁺ θ'))
              ( ε +ℚ⁺ θ +ℚ⁺ δ)
              ( transitive-le-ℚ⁺
                ( (ε' +ℚ⁺ ε') +ℚ⁺ (θ' +ℚ⁺ θ'))
                ( ε +ℚ⁺ θ)
                ( ε +ℚ⁺ θ +ℚ⁺ δ)
                ( le-left-add-ℚ⁺ (ε +ℚ⁺ θ) δ)
                ( preserves-le-add-ℚ 2ε'<ε 2θ'<θ))
              ( preserves-le-add-ℚ
                ( preserves-le-left-add-ℚ _ _ _ 2ε''<ε')
                ( preserves-le-right-add-ℚ _ _ _ 2θ''<θ'))))
          ( neighborhood-add-Metric-Ab G
            ( (ε'' +ℚ⁺ θ') +ℚ⁺ (ε'' +ℚ⁺ θ''))
            ( ε' +ℚ⁺ θ'')
            ( add-Metric-Ab G (x ε'') (y ε''))
            ( add-Metric-Ab G (x θ') (y θ''))
            ( z ε')
            ( z θ'')
            ( neighborhood-add-Metric-Ab G
              ( ε'' +ℚ⁺ θ')
              ( ε'' +ℚ⁺ θ'')
              ( x ε'')
              ( x θ')
              ( y ε'')
              ( y θ'')
              ( is-approx-x ε'' θ')
              ( is-approx-y ε'' θ''))
            ( is-approx-z ε' θ'')))
```

### Commutativity of addition

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (x y : cauchy-approximation-Metric-Ab G)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  commutative-add-cauchy-approximation-Metric-Ab :
    add-cauchy-approximation-Metric-Ab G x y ＝
    add-cauchy-approximation-Metric-Ab G y x
  commutative-add-cauchy-approximation-Metric-Ab =
    eq-type-subtype
      ( is-cauchy-approximation-prop-Metric-Ab G)
      ( eq-htpy (λ _ → commutative-add-Metric-Ab G _ _))
```

### Unit laws

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  (ax@(x , is-approx-x) : cauchy-approximation-Metric-Ab G)
  where abstract opaque

  unfolding map-add-cauchy-approximation-Metric-Ab

  sim-left-unit-law-add-cauchy-approximation-Metric-Ab :
    sim-cauchy-pseudocompletion-Metric-Ab G
      ( add-cauchy-approximation-Metric-Ab G
        ( zero-cauchy-approximation-Metric-Ab G)
        ( ax))
      ( ax)
  sim-left-unit-law-add-cauchy-approximation-Metric-Ab δ ε θ =
    let (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε in
    monotonic-neighborhood-Metric-Ab G
      ( add-Metric-Ab G (zero-Metric-Ab G) (x ε'))
      ( x θ)
      ( ε' +ℚ⁺ θ)
      ( ε +ℚ⁺ θ +ℚ⁺ δ)
      ( transitive-le-ℚ⁺
        ( ε' +ℚ⁺ θ)
        ( ε +ℚ⁺ θ)
        ( ε +ℚ⁺ θ +ℚ⁺ δ)
        ( le-left-add-ℚ⁺ (ε +ℚ⁺ θ) δ)
        ( preserves-le-left-add-ℚ _ _ _ (le-modulus-le-double-le-ℚ⁺ ε)))
      ( inv-tr
        ( λ y → neighborhood-Metric-Ab G (ε' +ℚ⁺ θ) y (x θ))
        ( left-unit-law-add-Metric-Ab G (x ε'))
        ( is-approx-x ε' θ))

  sim-right-unit-law-add-cauchy-approximation-Metric-Ab :
    sim-cauchy-pseudocompletion-Metric-Ab G
      ( add-cauchy-approximation-Metric-Ab G
        ( ax)
        ( zero-cauchy-approximation-Metric-Ab G))
      ( ax)
  sim-right-unit-law-add-cauchy-approximation-Metric-Ab =
    tr
      ( λ ay → sim-cauchy-pseudocompletion-Metric-Ab G ay ax)
      ( commutative-add-cauchy-approximation-Metric-Ab G
        ( zero-cauchy-approximation-Metric-Ab G)
        ( ax))
      ( sim-left-unit-law-add-cauchy-approximation-Metric-Ab)
```

### Left addition is a short map in the Cauchy pseudocompletion of a metric abelian group

```agda
module _
  {l1 l2 : Level}
  (G : Metric-Ab l1 l2)
  where

  abstract opaque
    unfolding map-add-cauchy-approximation-Metric-Ab

    preserves-neighborhood-left-add-cauchy-approximation-Metric-Ab :
      (x : cauchy-approximation-Metric-Ab G) →
      is-short-map-Pseudometric-Space
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( cauchy-pseudocompletion-Metric-Ab G)
        ( add-cauchy-approximation-Metric-Ab G x)
    preserves-neighborhood-left-add-cauchy-approximation-Metric-Ab
      (x , is-approx-x) d (y , is-approx-y) (z , is-approx-z) Ndyz δ ε =
      let
        (δ' , 2δ'<δ) = bound-double-le-ℚ⁺ δ
        (ε' , 2ε'<ε) = bound-double-le-ℚ⁺ ε
      in
        monotonic-neighborhood-Metric-Ab G
          ( add-Metric-Ab G (x δ') (y δ'))
          ( add-Metric-Ab G (x ε') (z ε'))
          ( (δ' +ℚ⁺ ε') +ℚ⁺ (δ' +ℚ⁺ ε' +ℚ⁺ d))
          ( δ +ℚ⁺ ε +ℚ⁺ d)
          ( concat-eq-le-ℚ⁺
            { z = δ +ℚ⁺ ε +ℚ⁺ d}
            ( equational-reasoning
              (δ' +ℚ⁺ ε') +ℚ⁺ (δ' +ℚ⁺ ε' +ℚ⁺ d)
              ＝ (δ' +ℚ⁺ ε') +ℚ⁺ (δ' +ℚ⁺ ε') +ℚ⁺ d
                by inv (associative-add-ℚ⁺ _ _ _)
              ＝ (δ' +ℚ⁺ δ') +ℚ⁺ (ε' +ℚ⁺ ε') +ℚ⁺ d
                by ap-add-ℚ⁺ (interchange-law-add-add-ℚ⁺ _ _ _ _) refl)
            ( preserves-le-left-add-ℚ _ _ _ (preserves-le-add-ℚ 2δ'<δ 2ε'<ε)))
          ( neighborhood-add-Metric-Ab G
            ( δ' +ℚ⁺ ε')
            ( δ' +ℚ⁺ ε' +ℚ⁺ d)
            ( x δ')
            ( x ε')
            ( y δ')
            ( z ε')
            ( is-approx-x δ' ε')
            ( Ndyz δ' ε'))

  short-map-left-add-cauchy-pseudocompletion-Metric-Ab :
    (x : cauchy-approximation-Metric-Ab G) →
    short-map-Pseudometric-Space
      ( cauchy-pseudocompletion-Metric-Ab G)
      ( cauchy-pseudocompletion-Metric-Ab G)
  short-map-left-add-cauchy-pseudocompletion-Metric-Ab x =
    ( add-cauchy-approximation-Metric-Ab G x ,
      preserves-neighborhood-left-add-cauchy-approximation-Metric-Ab x)
```
