# Directed edges

```agda
module simplicial-type-theory.directed-edges where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

A {{#concept "directed edge" Disambiguation="simplicial type theory" Agda=hom▵}}
in a type `A` from `x : A` to `y : A` is a
[simplicial arrow](simplicial-type-theory.simplicial-arrows.md) `α` in `A`
together with [identifications](foundation-core.identity-types.md) `α 0₂ ＝ x`
and `α 1₂ ＝ y`. We call `x` the _source_, and `y` the _target_ of the edge.

We introduce the notation `x →▵ y` for the type of directed edges from `x` to
`y`.

## Definitions

### Directed edges in types dependent over the directed interval

```agda
module _
  {l : Level} {A : 𝟚 → UU l}
  where

  hom▵' : A 0₂ → A 1₂ → UU l
  hom▵' x y =
    Σ (arrow▵' A) (λ α → (α 0₂ ＝ x) × (α 1₂ ＝ y))

  arrow-hom▵ :
    {x : A 0₂} {y : A 1₂} →
    hom▵' x y →
    arrow▵' A
  arrow-hom▵ = pr1

  hom▵-arrow▵ :
    (α : arrow▵' A) → hom▵' (α 0₂) (α 1₂)
  hom▵-arrow▵ α = (α , refl , refl)
```

### Directed edges

```agda
module _
  {l : Level} {A : UU l}
  where

  _→▵_ : A → A → UU l
  _→▵_ = hom▵' {A = λ _ → A}

  infix 7 _→▵_

  hom▵ : A → A → UU l
  hom▵ = _→▵_

  hom▵ : A → A → UU l
  hom▵ = _→▵_

  eq-source-hom▵ :
    {x y : A} (f : x →▵ y) → arrow-hom▵ f 0₂ ＝ x
  eq-source-hom▵ f = pr1 (pr2 f)

  inv-eq-source-hom▵ :
    {x y : A} (f : x →▵ y) → x ＝ arrow-hom▵ f 0₂
  inv-eq-source-hom▵ f = inv (eq-source-hom▵ f)

  eq-target-hom▵ :
    {x y : A} (f : x →▵ y) → arrow-hom▵ f 1₂ ＝ y
  eq-target-hom▵ f = pr2 (pr2 f)

  eq-source-target-hom▵ :
    {x y z : A} (f : x →▵ y) (g : y →▵ z) →
    arrow-hom▵ f 1₂ ＝ arrow-hom▵ g 0₂
  eq-source-target-hom▵ f g =
    eq-target-hom▵ f ∙ inv-eq-source-hom▵ g

  eq-source-source-hom▵ :
    {x y z : A} (f : x →▵ y) (g : x →▵ z) →
    arrow-hom▵ f 0₂ ＝ arrow-hom▵ g 0₂
  eq-source-source-hom▵ f g =
    eq-source-hom▵ f ∙ inv-eq-source-hom▵ g

  eq-target-target-hom▵ :
    {x y z : A} (f : x →▵ y) (g : z →▵ y) →
    arrow-hom▵ f 1₂ ＝ arrow-hom▵ g 1₂
  eq-target-target-hom▵ f g =
    eq-target-hom▵ f ∙ inv (eq-target-hom▵ g)
```

### The identity/constant directed edges

```agda
id-hom▵ : {l : Level} {A : UU l} (x : A) → x →▵ x
id-hom▵ = hom▵-arrow▵ ∘ id-arrow▵
```

### The representing edge of the directed interval

```agda
representing-hom-𝟚 : 0₂ →▵ 1₂
representing-hom-𝟚 = (id , refl , refl)
```

### Directed edges arising from equalities

```agda
hom▵-eq :
  {l : Level} {A : UU l} {x y : A} → x ＝ y → x →▵ y
hom▵-eq p =
  ( arrow▵-eq p ,
    compute-source-arrow▵-eq p ,
    compute-target-arrow▵-eq p)
```

## Properties

### Characterizing equality of homomorphisms

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  coherence-htpy-hom▵ :
    (f g : x →▵ y) →
    arrow-hom▵ f ~ arrow-hom▵ g →
    UU l
  coherence-htpy-hom▵ f g H =
    ( eq-source-hom▵ f ＝ H 0₂ ∙ eq-source-hom▵ g) ×
    ( eq-target-hom▵ f ＝ H 1₂ ∙ eq-target-hom▵ g)

  htpy-hom▵ : (f g : x →▵ y) → UU l
  htpy-hom▵ f g =
    Σ ( arrow-hom▵ f ~ arrow-hom▵ g)
      ( coherence-htpy-hom▵ f g)

  refl-htpy-hom▵ :
    (f : x →▵ y) → htpy-hom▵ f f
  refl-htpy-hom▵ f = (refl-htpy , refl , refl)

  htpy-eq-hom▵ :
    (f g : x →▵ y) → f ＝ g → htpy-hom▵ f g
  htpy-eq-hom▵ f .f refl = refl-htpy-hom▵ f

  abstract
    is-torsorial-htpy-hom▵ :
      (f : x →▵ y) →
      is-contr (Σ (x →▵ y) (htpy-hom▵ f))
    is-torsorial-htpy-hom▵ f =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (arrow-hom▵ f))
        ( arrow-hom▵ f , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Id (eq-source-hom▵ f))
          ( eq-source-hom▵ f , refl)
          ( is-torsorial-Id (eq-target-hom▵ f)))

  is-equiv-htpy-eq-hom▵ :
    (f g : x →▵ y) → is-equiv (htpy-eq-hom▵ f g)
  is-equiv-htpy-eq-hom▵ f =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom▵ f)
      ( htpy-eq-hom▵ f)

  extensionality-hom▵ :
    (f g : x →▵ y) → (f ＝ g) ≃ (htpy-hom▵ f g)
  extensionality-hom▵ f g =
    ( htpy-eq-hom▵ f g , is-equiv-htpy-eq-hom▵ f g)

  eq-htpy-hom▵ :
    (f g : x →▵ y) → htpy-hom▵ f g → f ＝ g
  eq-htpy-hom▵ f g =
    map-inv-equiv (extensionality-hom▵ f g)
```

### The homotopy of directed edges associated to a homotopy of simplicial arrows

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  {f : arrow▵ A} (g : x →▵ y)
  (H : f ~ arrow-hom▵ g)
  where

  hom▵-htpy-arrow▵ : x →▵ y
  hom▵-htpy-arrow▵ =
    ( f ,
      H 0₂ ∙ eq-source-hom▵ g ,
      H 1₂ ∙ eq-target-hom▵ g)

  htpy-hom▵-htpy-arrow▵ :
    htpy-hom▵ hom▵-htpy-arrow▵ g
  htpy-hom▵-htpy-arrow▵ = (H , refl , refl)

  eq-hom▵-htpy-arrow▵ :
    hom▵-htpy-arrow▵ ＝ g
  eq-hom▵-htpy-arrow▵ =
    eq-htpy-hom▵
      ( hom▵-htpy-arrow▵)
      ( g)
      ( htpy-hom▵-htpy-arrow▵)
```

### Computing the based total type of directed edges

```text
  Σ (𝟚 → A) (λ α → α 0₂ ＝ x) ≃ Σ (y : A), (x →▵ y)
```

```agda
module _
  {l : Level} {A : UU l} (x : A)
  where

  based-hom▵ : UU l
  based-hom▵ = Σ A (λ y → (x →▵ y))

  map-compute-based-hom▵ :
    Σ (𝟚 → A) (λ α → α 0₂ ＝ x) → based-hom▵
  map-compute-based-hom▵ (α , p) = (α 1₂ , α , p , refl)

  map-inv-compute-based-hom▵ :
    based-hom▵ → Σ (𝟚 → A) (λ α → α 0₂ ＝ x)
  map-inv-compute-based-hom▵ (y , α , p , q) = (α , p)

  is-section-map-inv-compute-based-hom▵ :
    is-section
      ( map-compute-based-hom▵)
      ( map-inv-compute-based-hom▵)
  is-section-map-inv-compute-based-hom▵
    (.(α 1₂) , α , p , refl) = refl

  is-retraction-map-inv-compute-based-hom▵ :
    is-retraction
      ( map-compute-based-hom▵)
      ( map-inv-compute-based-hom▵)
  is-retraction-map-inv-compute-based-hom▵ = refl-htpy

  is-equiv-map-compute-based-hom▵ :
    is-equiv map-compute-based-hom▵
  is-equiv-map-compute-based-hom▵ =
    is-equiv-is-invertible
      ( map-inv-compute-based-hom▵)
      ( is-section-map-inv-compute-based-hom▵)
      ( is-retraction-map-inv-compute-based-hom▵)

  is-equiv-map-inv-compute-based-hom▵ :
    is-equiv map-inv-compute-based-hom▵
  is-equiv-map-inv-compute-based-hom▵ =
    is-equiv-is-invertible
      ( map-compute-based-hom▵)
      ( is-retraction-map-inv-compute-based-hom▵)
      ( is-section-map-inv-compute-based-hom▵)

  compute-based-hom▵ :
    Σ (𝟚 → A) (λ α → α 0₂ ＝ x) ≃ based-hom▵
  compute-based-hom▵ =
    ( map-compute-based-hom▵ ,
      is-equiv-map-compute-based-hom▵)

  inv-compute-based-hom▵ :
    based-hom▵ ≃ Σ (𝟚 → A) (λ α → α 0₂ ＝ x)
  inv-compute-based-hom▵ =
    ( map-inv-compute-based-hom▵ ,
      is-equiv-map-inv-compute-based-hom▵)
```

### Computing the total type of directed edges

The directed interval type classifies the total type of directed edges in a
type.

```text
  (𝟚 → A) ≃ Σ (x y : A), (x →▵ y)
```

```agda
module _
  {l : Level} {A : UU l}
  where

  total-hom▵ : UU l
  total-hom▵ = Σ A based-hom▵

  map-compute-total-hom▵ :
    (𝟚 → A) → total-hom▵
  map-compute-total-hom▵ α = (α 0₂ , α 1₂ , α , refl , refl)

  map-inv-compute-total-hom▵ :
    total-hom▵ → 𝟚 → A
  map-inv-compute-total-hom▵ (x , y , α , p , q) = α

  is-section-map-inv-compute-total-hom▵ :
    is-section
      ( map-compute-total-hom▵)
      ( map-inv-compute-total-hom▵)
  is-section-map-inv-compute-total-hom▵
    (.(α 0₂) , .(α 1₂) , α , refl , refl) = refl

  is-retraction-map-inv-compute-total-hom▵ :
    is-retraction
      ( map-compute-total-hom▵)
      ( map-inv-compute-total-hom▵)
  is-retraction-map-inv-compute-total-hom▵ = refl-htpy

  is-equiv-map-compute-total-hom▵ :
    is-equiv map-compute-total-hom▵
  is-equiv-map-compute-total-hom▵ =
    is-equiv-is-invertible
      ( map-inv-compute-total-hom▵)
      ( is-section-map-inv-compute-total-hom▵)
      ( is-retraction-map-inv-compute-total-hom▵)

  is-equiv-map-inv-compute-total-hom▵ :
    is-equiv map-inv-compute-total-hom▵
  is-equiv-map-inv-compute-total-hom▵ =
    is-equiv-is-invertible
      ( map-compute-total-hom▵)
      ( is-retraction-map-inv-compute-total-hom▵)
      ( is-section-map-inv-compute-total-hom▵)

  compute-total-hom▵ :
    (𝟚 → A) ≃ total-hom▵
  compute-total-hom▵ =
    ( map-compute-total-hom▵ ,
      is-equiv-map-compute-total-hom▵)

  inv-compute-total-hom▵ :
    total-hom▵ ≃ (𝟚 → A)
  inv-compute-total-hom▵ =
    ( map-inv-compute-total-hom▵ ,
      is-equiv-map-inv-compute-total-hom▵)
```

### The hom type is an extension type

The hom-type `x →▵ y` is equivalent to the
[type of extensions](orthogonal-factorization-systems.extensions-maps.md) of
`[x , y] : ∂𝟚 → A` along the inclusion `∂𝟚 ↪ 𝟚`.

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  compute-extension-type-hom▵ :
    (x →▵ y) ≃ extension map-directed-interval-bool (rec-bool y x)
  compute-extension-type-hom▵ =
    equiv-tot
      ( λ α →
        ( inv-equiv-Π-bool-product
          ( λ b → rec-bool y x b ＝ α (map-directed-interval-bool b))) ∘e
        ( commutative-product) ∘e
        ( equiv-product (equiv-inv (α 0₂) x) (equiv-inv (α 1₂) y)))
```

### The hom-types of a truncated type are truncated

```agda
module _
  {l : Level} (k : 𝕋) {A : UU l} (x y : A)
  where

  is-trunc-hom▵ : is-trunc k A → is-trunc k (x →▵ y)
  is-trunc-hom▵ is-trunc-A =
    is-trunc-equiv k
      ( extension map-directed-interval-bool (rec-bool y x))
      ( compute-extension-type-hom▵ x y)
      ( is-trunc-extension-dependent-type k
        ( map-directed-interval-bool)
        ( rec-bool y x)
        ( λ _ → is-trunc-A))
```
