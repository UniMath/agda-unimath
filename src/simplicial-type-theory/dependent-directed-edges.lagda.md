# Dependent directed edges

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.dependent-directed-edges
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
```

</details>

## Idea

Given a type family `B : A → 𝒰` and a
[directed edge](simplicial-type-theory.directed-edges.md) `α : x →▵ y` in `A`, a
{{#concept "dependent directed edge" Disambiguation="simplicial type theory" Agda=dependent-hom▵}}
_over_ `α` from `x'` to `y'` is a simplicial arrow `β` in `B ∘ α : Δ¹ → 𝒰`. such
that `β 0▵ ＝ x'` over the identification `α 0▵ ＝ x` and `β 1▵ ＝ y'` over the
identification `α 1▵ ＝ y`.

Assuming for simplicity that the endpoints are strict, i.e., `α 0▵ ≐ x` and
`α 1▵ ≐ y`, the situation can be drawn as in the following diagram. The
dependent arrow `β` lives in the dependent type `B` varying over `A`, pointing
from an element in the fiber `B x` to an element in the fiber `B y`. On each end
of the dependent arrow, there is a correcting identification within the
respective fiber of `B`

```text
       B x           B y
   ~~~~~~~~~~~~~~~~~~~~~~~~~
  │     │             │     │
  │  x' ∙ ··········> │     │      B
  │     │      β      ∙ y'  │
  │     │             │     │
   ~~~~~~~~~~~~~~~~~~~~~~~~~
        ↧             ↧
  ───── ∙ ──────────> ∙ ─────      A.
        x      α      y
```

## Definitions

### Dependent directed edges

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  {x y : A} (α : x →▵ y)
  where

  dependent-hom▵ : B x → B y → UU (I1 ⊔ l2)
  dependent-hom▵ x' y' =
    Σ ( arrow▵' (B ∘ arrow-hom▵ α))
      ( λ β →
        ( dependent-identification B (eq-source-hom▵ α) (β 0▵) x') ×
        ( dependent-identification B (eq-target-hom▵ α) (β 1▵) y'))

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {x y : A} (α : x →▵ y) {x' : B x} {y' : B y}
  (β : dependent-hom▵ B α x' y')
  where

  arrow-dependent-hom▵ :
    arrow▵' (B ∘ arrow-hom▵ α)
  arrow-dependent-hom▵ = pr1 β

  eq-source-dependent-hom▵ :
    dependent-identification B
      ( eq-source-hom▵ α)
      ( arrow-dependent-hom▵ 0▵)
      ( x')
  eq-source-dependent-hom▵ = pr1 (pr2 β)

  eq-target-dependent-hom▵ :
    dependent-identification B
      ( eq-target-hom▵ α)
      ( arrow-dependent-hom▵ 1▵)
      ( y')
  eq-target-dependent-hom▵ = pr2 (pr2 β)
```

### The identity/constant dependent directed edges

```agda
id-dependent-hom▵ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x : A} (x' : B x) →
  dependent-hom▵ B (id-hom▵ x) x' x'
id-dependent-hom▵ = id-hom▵
```

### Dependent directed edges arising from identifications

```agda
dependent-hom▵-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A} (p : x ＝ y)
  {x' : B x} {y' : B y} → dependent-identification B p x' y' →
  dependent-hom▵ B (hom▵-eq p) x' y'
dependent-hom▵-eq refl = hom▵-eq
```

### Characterizing equality of dependent directed edges over a fixed edge

Given a directed edge `α : x →▵ y` in `A` and elements `x' : B x` and
`y' : B y`, we want to characterize identifications of dependent directed edges
from `x'` to `y'` over `α`. The situation is as follows

```text
       B x                                     B y
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  │     │        │                     │        │     │
  │     │        │          β          │        │     │
  │     │ ══════ ∙ ··················> ∙ ══════ │     │
  │  x' ∙        │                     │        ∙ y'  │      B
  │     │ ══════ ∙ ··················> ∙ ══════ │     │
  │     │        │          β'         │        │     │
  │     │        │                     │        │     │
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        ↧        ↧                     ↧        ↧
  ───── ∙ ══════ ∙ ──────────────────> ∙ ====== ∙ ─────      A.
        x       α 0▵        α         α 1▵      y
```

We are looking for coherence data to fill the area between `x'` and `y'`, and
the area is naturally subdivided into three sections. To fill the middle, we ask
for a homotopy of the underlying dependent arrows `H : β ~ β'`. Now, to also
fill the triangles at the end points, we require further coherences of the
dependent triangles depicted below

```text
            ──── ∙ β 0▵           β 1▵ ∙ ────
          ╱      │                     │      ╲
     x' ∙        │ H 0▵           H 1▵ │        ∙ y'
          ╲      │                     │      ╱
            ──── ∙ β' 0▵         β' 1▵ ∙ ────

        ↧        ↧                     ↧        ↧

      x ∙ ────── ∙ α 0▵           α 1▵ ∙ ────── ∙ y.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {x y : A} (α : x →▵ y) {x' : B x} {y' : B y}
  where

  coherence-htpy-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') →
    arrow-dependent-hom▵ α β ~
    arrow-dependent-hom▵ α β' →
    UU l2
  coherence-htpy-dependent-hom-over▵ β β' H =
    ( ( eq-source-dependent-hom▵ α β) ＝
      ( concat-dependent-identification B refl
        ( eq-source-hom▵ α)
        ( H 0▵)
        ( eq-source-dependent-hom▵ α β'))) ×
    ( ( eq-target-dependent-hom▵ α β) ＝
      ( concat-dependent-identification B refl
        ( eq-target-hom▵ α)
        ( H 1▵)
        ( eq-target-dependent-hom▵ α β')))

  htpy-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') → UU (I1 ⊔ l2)
  htpy-dependent-hom-over▵ β β' =
    Σ ( arrow-dependent-hom▵ α β ~
        arrow-dependent-hom▵ α β')
      ( coherence-htpy-dependent-hom-over▵ β β')

  refl-htpy-dependent-hom-over▵ :
    (β : dependent-hom▵ B α x' y') →
    htpy-dependent-hom-over▵ β β
  refl-htpy-dependent-hom-over▵ β = (refl-htpy , refl , refl)

  htpy-eq-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') →
    β ＝ β' → htpy-dependent-hom-over▵ β β'
  htpy-eq-dependent-hom-over▵ β .β refl =
    refl-htpy-dependent-hom-over▵ β

  is-torsorial-htpy-dependent-hom-over▵ :
    (β : dependent-hom▵ B α x' y') →
    is-torsorial (htpy-dependent-hom-over▵ β)
  is-torsorial-htpy-dependent-hom-over▵ β =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (arrow-dependent-hom▵ α β))
      ( arrow-dependent-hom▵ α β , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-Id (eq-source-dependent-hom▵ α β))
        ( eq-source-dependent-hom▵ α β , refl)
        ( is-torsorial-Id (eq-target-dependent-hom▵ α β)))

  is-equiv-htpy-eq-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') →
    is-equiv (htpy-eq-dependent-hom-over▵ β β')
  is-equiv-htpy-eq-dependent-hom-over▵ β =
    fundamental-theorem-id
      ( is-torsorial-htpy-dependent-hom-over▵ β)
      ( htpy-eq-dependent-hom-over▵ β)

  extensionality-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') →
    (β ＝ β') ≃ htpy-dependent-hom-over▵ β β'
  extensionality-dependent-hom-over▵ β β' =
    ( htpy-eq-dependent-hom-over▵ β β' ,
      is-equiv-htpy-eq-dependent-hom-over▵ β β')

  eq-htpy-dependent-hom-over▵ :
    (β β' : dependent-hom▵ B α x' y') →
    htpy-dependent-hom-over▵ β β' → β ＝ β'
  eq-htpy-dependent-hom-over▵ β β' =
    map-inv-equiv (extensionality-dependent-hom-over▵ β β')
```
