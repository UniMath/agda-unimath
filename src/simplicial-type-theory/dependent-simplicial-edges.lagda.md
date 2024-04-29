# Dependent directed edges

```agda
module simplicial-type-theory.dependent-simplicial-edges where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.directed-edges
```

</details>

## Idea

Given a type family `B : A → 𝒰` and a
[directed edge](simplicial-type-theory.directed-edges.md) `α : x →₂ y` in `A`, a
{{#concept "dependent directed edge" Disambiguation="simplicial type theory" Agda=dependent-simplicial-hom}}
_over_ `α` from `x'` to `y'` is a simplicial arrow `β` in `B ∘ α : 𝟚 → 𝒰`. such
that `β 0₂ ＝ x'` over the identification `α 0₂ ＝ x` and `β 1₂ ＝ y'` over the
identification `α 1₂ ＝ y`.

Assuming for simplicity that the endpoints are strict, i.e., `α 0₂ ≐ x` and
`α 1₂ ≐ y`, the situation can be drawn as in the following diagram. The
dependent arrow `β` lives in the dependent type `B` varying over `A`, pointing
from an element in the fiber `B x` to an element in the fiber `B y`. On each end
of the dependent arrow, there is a correcting identification within the
respective fiber of `B`

```text
       B x           B y
   ~~~~~~~~~~~~~~~~~~~~~~~~~
  |     |             |     |
  |  x' ∙ ⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯> |     |      B
  |     |      β      ∙ y'  |
  |     |             |     |
   ~~~~~~~~~~~~~~~~~~~~~~~~~
        ↧             ↧
  ----- ∙ ----------> ∙ -----      A.
        x      α      y
```

## Definitions

### Dependent directed edges

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  {x y : A} (α : x →₂ y)
  where

  dependent-simplicial-hom : B x → B y → UU l2
  dependent-simplicial-hom x' y' =
    Σ ( simplicial-arrow' (B ∘ simplicial-arrow-simplicial-hom α))
      ( λ β →
        ( dependent-identification B (eq-source-simplicial-hom α) (β 0₂) x') ×
        ( dependent-identification B (eq-target-simplicial-hom α) (β 1₂) y'))

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {x y : A} (α : x →₂ y) {x' : B x} {y' : B y}
  (β : dependent-simplicial-hom B α x' y')
  where

  simplicial-arrow-dependent-simplicial-hom :
    simplicial-arrow' (B ∘ simplicial-arrow-simplicial-hom α)
  simplicial-arrow-dependent-simplicial-hom = pr1 β

  eq-source-dependent-simplicial-hom :
    dependent-identification B
      ( eq-source-simplicial-hom α)
      ( simplicial-arrow-dependent-simplicial-hom 0₂)
      ( x')
  eq-source-dependent-simplicial-hom = pr1 (pr2 β)

  eq-target-dependent-simplicial-hom :
    dependent-identification B
      ( eq-target-simplicial-hom α)
      ( simplicial-arrow-dependent-simplicial-hom 1₂)
      ( y')
  eq-target-dependent-simplicial-hom = pr2 (pr2 β)
```

### The identity/constant dependent directed edges

```agda
id-dependent-simplicial-hom :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x : A} (x' : B x) →
  dependent-simplicial-hom B (id-simplicial-hom x) x' x'
id-dependent-simplicial-hom = id-simplicial-hom
```

### Dependent directed edges arising from identifications

```agda
dependent-simplicial-hom-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A} (p : x ＝ y)
  {x' : B x} {y' : B y} → dependent-identification B p x' y' →
  dependent-simplicial-hom B (simplicial-hom-eq p) x' y'
dependent-simplicial-hom-eq refl = simplicial-hom-eq
```

### Characterizing equality of dependent directed edges over a fixed edge

Given a directed edge `α : x →₂ y` in `A` and elements `x' : B x` and
`y' : B y`, we want to characterize identifications of dependent directed edges
from `x'` to `y'` over `α`. The situation is as follows

```text
       B x                                     B y
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  |     |        |                     |        |     |
  |     |        |          β          |        |     |
  |     | ====== ∙ ⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯> ∙ ====== |     |
  |  x' ∙        |                     |        ∙ y'  |      B
  |     | ====== ∙ ⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯⋯> ∙ ====== |     |
  |     |        |          β'         |        |     |
  |     |        |                     |        |     |
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        ↧        ↧                     ↧        ↧
  ----- ∙ ====== ∙ ------------------> ∙ ====== ∙ -----      A.
        x       α 0₂        α         α 1₂      y
```

We are looking for coherence data to fill the area between `x'` and `y'`, and
the area is naturally subdivided into three sections. To fill the middle, we ask
for a homotopy of the underlying dependent arrows `H : β ~ β'`. Now, to also
fill the triangles at the end points, we require further coherences of the
dependent triangles depicted below

```text
            ---- ∙ β 0₂           β 1₂ ∙ ----
          /      |                     |      \
     x' ∙        | H 0₂           H 1₂ |        ∙ y'
          \      |                     |      /
            ---- ∙ β' 0₂         β' 1₂ ∙ ----

        ↧        ↧                     ↧        ↧

      x ∙ ------ ∙ α 0₂           α 1₂ ∙ ------ ∙ y.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {x y : A} (α : x →₂ y) {x' : B x} {y' : B y}
  where

  coherence-htpy-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') →
    simplicial-arrow-dependent-simplicial-hom α β ~
    simplicial-arrow-dependent-simplicial-hom α β' →
    UU l2
  coherence-htpy-dependent-simplicial-hom-over β β' H =
    ( ( eq-source-dependent-simplicial-hom α β) ＝
      ( concat-dependent-identification B refl
        ( eq-source-simplicial-hom α)
        ( H 0₂)
        ( eq-source-dependent-simplicial-hom α β'))) ×
    ( ( eq-target-dependent-simplicial-hom α β) ＝
      ( concat-dependent-identification B refl
        ( eq-target-simplicial-hom α)
        ( H 1₂)
        ( eq-target-dependent-simplicial-hom α β')))

  htpy-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') → UU l2
  htpy-dependent-simplicial-hom-over β β' =
    Σ ( simplicial-arrow-dependent-simplicial-hom α β ~
        simplicial-arrow-dependent-simplicial-hom α β')
      ( coherence-htpy-dependent-simplicial-hom-over β β')

  refl-htpy-dependent-simplicial-hom-over :
    (β : dependent-simplicial-hom B α x' y') →
    htpy-dependent-simplicial-hom-over β β
  refl-htpy-dependent-simplicial-hom-over β = (refl-htpy , refl , refl)

  htpy-eq-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') →
    β ＝ β' → htpy-dependent-simplicial-hom-over β β'
  htpy-eq-dependent-simplicial-hom-over β .β refl =
    refl-htpy-dependent-simplicial-hom-over β

  is-torsorial-htpy-dependent-simplicial-hom-over :
    (β : dependent-simplicial-hom B α x' y') →
    is-torsorial (htpy-dependent-simplicial-hom-over β)
  is-torsorial-htpy-dependent-simplicial-hom-over β =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (simplicial-arrow-dependent-simplicial-hom α β))
      ( simplicial-arrow-dependent-simplicial-hom α β , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-Id (eq-source-dependent-simplicial-hom α β))
        ( eq-source-dependent-simplicial-hom α β , refl)
        ( is-torsorial-Id (eq-target-dependent-simplicial-hom α β)))

  is-equiv-htpy-eq-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') →
    is-equiv (htpy-eq-dependent-simplicial-hom-over β β')
  is-equiv-htpy-eq-dependent-simplicial-hom-over β =
    fundamental-theorem-id
      ( is-torsorial-htpy-dependent-simplicial-hom-over β)
      ( htpy-eq-dependent-simplicial-hom-over β)

  extensionality-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') →
    (β ＝ β') ≃ htpy-dependent-simplicial-hom-over β β'
  extensionality-dependent-simplicial-hom-over β β' =
    ( htpy-eq-dependent-simplicial-hom-over β β' ,
      is-equiv-htpy-eq-dependent-simplicial-hom-over β β')

  eq-htpy-dependent-simplicial-hom-over :
    (β β' : dependent-simplicial-hom B α x' y') →
    htpy-dependent-simplicial-hom-over β β' → β ＝ β'
  eq-htpy-dependent-simplicial-hom-over β β' =
    map-inv-equiv (extensionality-dependent-simplicial-hom-over β β')
```
