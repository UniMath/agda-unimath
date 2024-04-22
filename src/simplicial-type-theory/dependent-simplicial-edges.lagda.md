# Dependent simplicial edges

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
open import simplicial-type-theory.simplicial-edges
```

</details>

## Idea

Given a type family `B : A → 𝒰` and a
[directed edge](simplicial-type-theory.simplicial-edges.md) `α : x →₂ y` in `A`,
a
{{#concept "dependent directed edge" Disambiguation="simplicial type theory" Agda=dependent-simplicial-hom}}
_over_ `α` from `x'` to `y'` is a simplicial arrow in `B ∘ α : 𝟚 → 𝒰`. such that

## Definitions

### Dependent simplicial edges

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

### The identity/constant dependent simplicial edges

```agda
id-dependent-simplicial-hom :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x : A} (x' : B x) →
  dependent-simplicial-hom B (id-simplicial-hom x) x' x'
id-dependent-simplicial-hom x' = ( (λ _ → x') , refl , refl)
```

### Dependent simplicial edges arising from identifications

```agda
dependent-simplicial-hom-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A} (p : x ＝ y)
  {x' : B x} {y' : B y} → dependent-identification B p x' y' →
  dependent-simplicial-hom B (simplicial-hom-eq p) x' y'
dependent-simplicial-hom-eq refl = simplicial-hom-eq
```

### Characterizing equality of dependent simplicial edges

This remains to be formalized.

### The dependent homotopy of dependent simplicial edges associated to a dependent homotopy of dependent simplicial arrows

This remains to be formalized.
