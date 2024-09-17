# Free directed loops

```agda
module simplicial-type-theory.free-directed-loops where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.constant-type-families
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import simplicial-type-theory.dependent-directed-edges
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows

open import synthetic-homotopy-theory.free-loops
```

</details>

## Idea

A
{{#concept "free directed loop" Disambiguation="in a simplicial type" Agda=free-directed-loop}}
in a type `X` consists of a
[directed arrow](simplicial-type-theory.simplicial-arrows.md) `α : 𝟚 → X` and an
[identification](foundation-core.identity-types.md) `α 1₂ ＝ α 0₂`. Free
directed loops are classified by the
[directed circle](simplicial-type-theory.directed-circle.md), meaning that the
type of free directed loops in `X` is
[equivalent](foundation-core.equivalences.md) to the type of maps
`directed-circle → X`.

## Definitions

### Free directed loops

```agda
free-directed-loop : {l : Level} → UU l → UU l
free-directed-loop X = Σ (𝟚 → X) (λ α → α 1₂ ＝ α 0₂)

module _
  {l1 : Level} {X : UU l1}
  where

  arrow-free-directed-loop : free-directed-loop X → 𝟚 → X
  arrow-free-directed-loop = pr1

  base-free-directed-loop : free-directed-loop X → X
  base-free-directed-loop α = arrow-free-directed-loop α 0₂

  compute-target-free-directed-loop :
    (α : free-directed-loop X) →
    arrow-free-directed-loop α 1₂ ＝ base-free-directed-loop α
  compute-target-free-directed-loop = pr2

  loop-free-directed-loop :
    (α : free-directed-loop X) →
    base-free-directed-loop α →₂ base-free-directed-loop α
  loop-free-directed-loop α =
    ( arrow-free-directed-loop α , refl , compute-target-free-directed-loop α)
```

### Free dependent directed loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (P : X → UU l2)
  where

  free-dependent-directed-loop : UU l2
  free-dependent-directed-loop =
    Σ ( simplicial-arrow' (P ∘ arrow-free-directed-loop α))
      ( λ β →
        dependent-identification P
          ( compute-target-free-directed-loop α)
          ( β 1₂)
          ( β 0₂))

module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) {P : X → UU l2}
  ( β : free-dependent-directed-loop α P)
  where

  arrow-free-dependent-directed-loop :
    simplicial-arrow' (P ∘ arrow-free-directed-loop α)
  arrow-free-dependent-directed-loop = pr1 β

  base-free-dependent-directed-loop : P (base-free-directed-loop α)
  base-free-dependent-directed-loop = arrow-free-dependent-directed-loop 0₂

  compute-target-free-dependent-directed-loop :
    dependent-identification P
      ( compute-target-free-directed-loop α)
      ( arrow-free-dependent-directed-loop 1₂)
      ( arrow-free-dependent-directed-loop 0₂)
  compute-target-free-dependent-directed-loop = pr2 β

  loop-free-dependent-directed-loop :
    dependent-simplicial-hom P
      ( loop-free-directed-loop α)
      ( base-free-dependent-directed-loop)
      ( base-free-dependent-directed-loop)
  loop-free-dependent-directed-loop =
    ( arrow-free-dependent-directed-loop ,
      refl ,
      compute-target-free-dependent-directed-loop)
```

### Free directed loops from free loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  free-directed-loop-free-loop : free-loop X → free-directed-loop X
  pr1 (free-directed-loop-free-loop α) =
    simplicial-arrow-eq (loop-free-loop α)
  pr2 (free-directed-loop-free-loop α) =
    ( compute-target-simplicial-arrow-eq (loop-free-loop α) ∙
      inv (compute-source-simplicial-arrow-eq (loop-free-loop α)))
```

### Constant free directed loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  constant-free-directed-loop : X → free-directed-loop X
  constant-free-directed-loop x = (id-simplicial-arrow x , refl)
```

## Properties

### Characterization of the identity type of the type of free directed loops

```agda
module _
  {l1 : Level} {X : UU l1}
  where

  coherence-htpy-free-directed-loop :
    (α α' : free-directed-loop X) →
    arrow-free-directed-loop α ~ arrow-free-directed-loop α' →
    UU l1
  coherence-htpy-free-directed-loop α α' H =
    coherence-square-identifications
      ( compute-target-free-directed-loop α)
      ( H 1₂)
      ( H 0₂)
      ( compute-target-free-directed-loop α')

  htpy-free-directed-loop : (α α' : free-directed-loop X) → UU l1
  htpy-free-directed-loop α α' =
    Σ ( arrow-free-directed-loop α ~ arrow-free-directed-loop α')
      ( coherence-htpy-free-directed-loop α α')

  refl-htpy-free-directed-loop :
    (α : free-directed-loop X) → htpy-free-directed-loop α α
  refl-htpy-free-directed-loop α = (refl-htpy , inv right-unit)

  htpy-eq-free-directed-loop :
    (α α' : free-directed-loop X) → α ＝ α' → htpy-free-directed-loop α α'
  htpy-eq-free-directed-loop α .α refl = refl-htpy-free-directed-loop α

  is-torsorial-htpy-free-directed-loop :
    (α : free-directed-loop X) → is-torsorial (htpy-free-directed-loop α)
  is-torsorial-htpy-free-directed-loop α =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (arrow-free-directed-loop α))
      ( arrow-free-directed-loop α , refl-htpy)
      ( is-torsorial-Id' (compute-target-free-directed-loop α ∙ refl))

  is-equiv-htpy-eq-free-directed-loop :
    (α α' : free-directed-loop X) → is-equiv (htpy-eq-free-directed-loop α α')
  is-equiv-htpy-eq-free-directed-loop α =
    fundamental-theorem-id
      ( is-torsorial-htpy-free-directed-loop α)
      ( htpy-eq-free-directed-loop α)

  extensionality-free-directed-loop :
    (α α' : free-directed-loop X) → (α ＝ α') ≃ htpy-free-directed-loop α α'
  extensionality-free-directed-loop α α' =
    ( htpy-eq-free-directed-loop α α' ,
      is-equiv-htpy-eq-free-directed-loop α α')

  eq-htpy-free-directed-loop :
    (α α' : free-directed-loop X) → htpy-free-directed-loop α α' → α ＝ α'
  eq-htpy-free-directed-loop α α' =
    map-inv-equiv (extensionality-free-directed-loop α α')
```

### Characterization of the identity type of free dependent loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (P : X → UU l2)
  where

  coherence-htpy-free-dependent-directed-loop :
    (β β' : free-dependent-directed-loop α P) →
    arrow-free-dependent-directed-loop α β ~
    arrow-free-dependent-directed-loop α β' →
    UU l2
  coherence-htpy-free-dependent-directed-loop β β' H =
    ( right-strict-concat-dependent-identification P
      ( compute-target-free-directed-loop α)
      ( refl)
      ( compute-target-free-dependent-directed-loop α β)
      ( H 0₂)) ＝
    ( concat-dependent-identification P
      ( refl)
      ( compute-target-free-directed-loop α)
      ( H 1₂)
      ( compute-target-free-dependent-directed-loop α β'))

  htpy-free-dependent-directed-loop :
    (β β' : free-dependent-directed-loop α P) → UU l2
  htpy-free-dependent-directed-loop β β' =
    Σ ( arrow-free-dependent-directed-loop α β ~
        arrow-free-dependent-directed-loop α β')
      ( coherence-htpy-free-dependent-directed-loop β β')

  refl-htpy-free-dependent-directed-loop :
    (β : free-dependent-directed-loop α P) →
    htpy-free-dependent-directed-loop β β
  refl-htpy-free-dependent-directed-loop β = (refl-htpy , refl)

  htpy-free-dependent-directed-loop-eq :
    ( β β' : free-dependent-directed-loop α P) →
    β ＝ β' → htpy-free-dependent-directed-loop β β'
  htpy-free-dependent-directed-loop-eq β .β refl =
    refl-htpy-free-dependent-directed-loop β

  is-torsorial-htpy-free-dependent-directed-loop :
    ( β : free-dependent-directed-loop α P) →
    is-torsorial (htpy-free-dependent-directed-loop β)
  is-torsorial-htpy-free-dependent-directed-loop β =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (arrow-free-dependent-directed-loop α β))
      ( arrow-free-dependent-directed-loop α β , refl-htpy)
      (is-torsorial-Id (compute-target-free-dependent-directed-loop α β))

  is-equiv-htpy-free-dependent-directed-loop-eq :
    (β β' : free-dependent-directed-loop α P) →
    is-equiv (htpy-free-dependent-directed-loop-eq β β')
  is-equiv-htpy-free-dependent-directed-loop-eq β =
    fundamental-theorem-id
      ( is-torsorial-htpy-free-dependent-directed-loop β)
      ( htpy-free-dependent-directed-loop-eq β)

  eq-htpy-free-dependent-directed-loop :
    (β β' : free-dependent-directed-loop α P) →
    htpy-free-dependent-directed-loop β β' → β ＝ β'
  eq-htpy-free-dependent-directed-loop β β' =
    map-inv-is-equiv (is-equiv-htpy-free-dependent-directed-loop-eq β β')
```

### The type of free dependent loops in a constant family of types is equivalent to the type of ordinary free directed loops

```agda
module _
  {l1 l2 : Level} {X : UU l1} (α : free-directed-loop X) (Y : UU l2)
  where

  compute-free-dependent-directed-loop-constant-type-family :
    free-directed-loop Y ≃ free-dependent-directed-loop α (λ _ → Y)
  compute-free-dependent-directed-loop-constant-type-family =
    equiv-tot
      ( λ _ →
        compute-dependent-identification-constant-type-family
          ( compute-target-free-directed-loop α))

  map-compute-free-dependent-directed-loop-constant-type-family :
    free-directed-loop Y → free-dependent-directed-loop α (λ _ → Y)
  map-compute-free-dependent-directed-loop-constant-type-family =
    map-equiv compute-free-dependent-directed-loop-constant-type-family

  map-inv-compute-free-dependent-directed-loop-constant-type-family :
    free-dependent-directed-loop α (λ _ → Y) → free-directed-loop Y
  map-inv-compute-free-dependent-directed-loop-constant-type-family =
    map-inv-equiv compute-free-dependent-directed-loop-constant-type-family
```

### The type of free directed loops is equivalent to the type of directed edges with common source and target

```agda
module _
  {l : Level} {X : UU l}
  where

  compute-free-dependent-directed-loop :
    Σ X (λ x → x →₂ x) ≃ free-directed-loop X
  compute-free-dependent-directed-loop =
    ( equiv-tot
      ( λ α →
        ( left-unit-law-Σ-is-contr (is-torsorial-Id (α 0₂)) (α 0₂ , refl)) ∘e
        ( inv-associative-Σ X (α 0₂ ＝_) (λ z → α 1₂ ＝ pr1 z)))) ∘e
    ( equiv-left-swap-Σ)
```
