# Simplicial edges

```agda
module simplicial-type-theory.simplicial-edges where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
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
```

</details>

## Idea

A
{{#concept "simplicial edge" Disambiguation="simplicial type theory" Agda=simplicial-hom}}
in a type `A` from `x : A` to `y : A` is a
[simplicial arrow](simplicial-type-theory.simplicial-arrows.md) `α` in `A`
together with [identifications](foundation-core.identity-types.md) `α 0₂ ＝ x`
and `α 1₂ ＝ y`. We call `x` the _source_, and `y` the _target_ of the edge.

## Definitions

### Dependent simplicial edges

```agda
module _
  {l : Level} {A : 𝟚 → UU l}
  where

  dependent-simplicial-hom : A 0₂ → A 1₂ → UU l
  dependent-simplicial-hom x y =
    Σ (dependent-simplicial-arrow A) (λ α → (α 0₂ ＝ x) × (α 1₂ ＝ y))

  simplicial-arrow-simplicial-hom :
    {x : A 0₂} {y : A 1₂} →
    dependent-simplicial-hom x y →
    dependent-simplicial-arrow A
  simplicial-arrow-simplicial-hom = pr1

  simplicial-hom-simplicial-arrow :
    (α : dependent-simplicial-arrow A) → dependent-simplicial-hom (α 0₂) (α 1₂)
  simplicial-hom-simplicial-arrow α = (α , refl , refl)
```

### Simplicial edges

```agda
module _
  {l : Level} {A : UU l}
  where

  simplicial-hom : A → A → UU l
  simplicial-hom = dependent-simplicial-hom {A = λ _ → A}

  eq-source-simplicial-hom :
    {x y : A} (f : simplicial-hom x y) →
    simplicial-arrow-simplicial-hom f 0₂ ＝ x
  eq-source-simplicial-hom f = pr1 (pr2 f)

  inv-eq-source-simplicial-hom :
    {x y : A} (f : simplicial-hom x y) →
    x ＝ simplicial-arrow-simplicial-hom f 0₂
  inv-eq-source-simplicial-hom f = inv (eq-source-simplicial-hom f)

  eq-target-simplicial-hom :
    {x y : A} (f : simplicial-hom x y) →
    simplicial-arrow-simplicial-hom f 1₂ ＝ y
  eq-target-simplicial-hom f = pr2 (pr2 f)

  eq-source-target-simplicial-hom :
    {x y z : A} (f : simplicial-hom x y) (g : simplicial-hom y z) →
    simplicial-arrow-simplicial-hom f 1₂ ＝ simplicial-arrow-simplicial-hom g 0₂
  eq-source-target-simplicial-hom f g =
    eq-target-simplicial-hom f ∙ inv-eq-source-simplicial-hom g

  eq-source-source-simplicial-hom :
    {x y z : A} (f : simplicial-hom x y) (g : simplicial-hom x z) →
    simplicial-arrow-simplicial-hom f 0₂ ＝ simplicial-arrow-simplicial-hom g 0₂
  eq-source-source-simplicial-hom f g =
    eq-source-simplicial-hom f ∙ inv-eq-source-simplicial-hom g

  eq-target-target-simplicial-hom :
    {x y z : A} (f : simplicial-hom x y) (g : simplicial-hom z y) →
    simplicial-arrow-simplicial-hom f 1₂ ＝ simplicial-arrow-simplicial-hom g 1₂
  eq-target-target-simplicial-hom f g =
    eq-target-simplicial-hom f ∙ inv (eq-target-simplicial-hom g)
```

### The identity/constant simplicial edges

```agda
id-simplicial-hom : {l : Level} {A : UU l} (x : A) → simplicial-hom x x
id-simplicial-hom = simplicial-hom-simplicial-arrow ∘ id-simplicial-arrow
```

### Simplicial edges arising from equalities

```agda
simplicial-hom-eq :
  {l : Level} {A : UU l} {x y : A} → x ＝ y → simplicial-hom x y
pr1 (simplicial-hom-eq p) = simplicial-arrow-eq p
pr2 (simplicial-hom-eq refl) = (refl , refl)
```

### Characterizing equality of homomorphisms

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  coherence-htpy-simplicial-hom :
    (f g : simplicial-hom x y) →
    simplicial-arrow-simplicial-hom f ~ simplicial-arrow-simplicial-hom g →
    UU l
  coherence-htpy-simplicial-hom f g H =
    ( eq-source-simplicial-hom f ＝ H 0₂ ∙ eq-source-simplicial-hom g) ×
    ( eq-target-simplicial-hom f ＝ H 1₂ ∙ eq-target-simplicial-hom g)

  htpy-simplicial-hom : (f g : simplicial-hom x y) → UU l
  htpy-simplicial-hom f g =
    Σ ( simplicial-arrow-simplicial-hom f ~ simplicial-arrow-simplicial-hom g)
    ( coherence-htpy-simplicial-hom f g)

  refl-htpy-simplicial-hom :
    (f : simplicial-hom x y) → htpy-simplicial-hom f f
  refl-htpy-simplicial-hom f = (refl-htpy , refl , refl)

  htpy-eq-simplicial-hom :
    (f g : simplicial-hom x y) → f ＝ g → htpy-simplicial-hom f g
  htpy-eq-simplicial-hom f .f refl = refl-htpy-simplicial-hom f

  abstract
    is-torsorial-htpy-simplicial-hom :
      (f : simplicial-hom x y) →
      is-contr (Σ (simplicial-hom x y) (htpy-simplicial-hom f))
    is-torsorial-htpy-simplicial-hom f =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (simplicial-arrow-simplicial-hom f))
        ( simplicial-arrow-simplicial-hom f , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Id (eq-source-simplicial-hom f))
          ( eq-source-simplicial-hom f , refl)
          ( is-torsorial-Id (eq-target-simplicial-hom f)))

  is-equiv-htpy-eq-simplicial-hom :
    (f g : simplicial-hom x y) → is-equiv (htpy-eq-simplicial-hom f g)
  is-equiv-htpy-eq-simplicial-hom f =
    fundamental-theorem-id
      ( is-torsorial-htpy-simplicial-hom f)
      ( htpy-eq-simplicial-hom f)

  extensionality-simplicial-hom :
    (f g : simplicial-hom x y) → (f ＝ g) ≃ (htpy-simplicial-hom f g)
  extensionality-simplicial-hom f g =
    ( htpy-eq-simplicial-hom f g , is-equiv-htpy-eq-simplicial-hom f g)

  eq-htpy-simplicial-hom :
    (f g : simplicial-hom x y) → htpy-simplicial-hom f g → f ＝ g
  eq-htpy-simplicial-hom f g =
    map-inv-equiv (extensionality-simplicial-hom f g)
```

### The homotopy of simplicial edges associated to a homotopy of simplicial arrows

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  {f : simplicial-arrow A} (g : simplicial-hom x y)
  (H : f ~ simplicial-arrow-simplicial-hom g)
  where

  simplicial-hom-htpy-simplicial-arrow : simplicial-hom x y
  simplicial-hom-htpy-simplicial-arrow =
    ( f ,
      H 0₂ ∙ eq-source-simplicial-hom g ,
      H 1₂ ∙ eq-target-simplicial-hom g)

  htpy-simplicial-hom-htpy-simplicial-arrow :
    htpy-simplicial-hom simplicial-hom-htpy-simplicial-arrow g
  htpy-simplicial-hom-htpy-simplicial-arrow = (H , refl , refl)

  eq-simplicial-hom-htpy-simplicial-arrow :
    simplicial-hom-htpy-simplicial-arrow ＝ g
  eq-simplicial-hom-htpy-simplicial-arrow =
      eq-htpy-simplicial-hom
        ( simplicial-hom-htpy-simplicial-arrow)
        ( g)
        ( htpy-simplicial-hom-htpy-simplicial-arrow)
```
