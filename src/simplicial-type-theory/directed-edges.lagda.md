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
open import foundation.truncation-levels
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.truncated-types
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-booleans
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-of-maps

open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.simplicial-arrows
```

</details>

## Idea

A
{{#concept "directed edge" Disambiguation="simplicial type theory" Agda=simplicial-hom}}
in a type `A` from `x : A` to `y : A` is a
[simplicial arrow](simplicial-type-theory.simplicial-arrows.md) `α` in `A`
together with [identifications](foundation-core.identity-types.md) `α 0₂ ＝ x`
and `α 1₂ ＝ y`. We call `x` the _source_, and `y` the _target_ of the edge.

We introduce the notation `x →₂ y` for the type of directed edges from `x` to
`y`.

## Definitions

### Directed edges in types dependent over the directed interval

```agda
module _
  {l : Level} {A : 𝟚 → UU l}
  where

  simplicial-hom' : A 0₂ → A 1₂ → UU l
  simplicial-hom' x y =
    Σ (simplicial-arrow' A) (λ α → (α 0₂ ＝ x) × (α 1₂ ＝ y))

  simplicial-arrow-simplicial-hom :
    {x : A 0₂} {y : A 1₂} →
    simplicial-hom' x y →
    simplicial-arrow' A
  simplicial-arrow-simplicial-hom = pr1

  simplicial-hom-simplicial-arrow :
    (α : simplicial-arrow' A) → simplicial-hom' (α 0₂) (α 1₂)
  simplicial-hom-simplicial-arrow α = (α , refl , refl)
```

### Directed edges

```agda
module _
  {l : Level} {A : UU l}
  where

  _→₂_ : A → A → UU l
  _→₂_ = simplicial-hom' {A = λ _ → A}

  infix 7 _→₂_

  simplicial-hom : A → A → UU l
  simplicial-hom = _→₂_

  eq-source-simplicial-hom :
    {x y : A} (f : x →₂ y) → simplicial-arrow-simplicial-hom f 0₂ ＝ x
  eq-source-simplicial-hom f = pr1 (pr2 f)

  inv-eq-source-simplicial-hom :
    {x y : A} (f : x →₂ y) → x ＝ simplicial-arrow-simplicial-hom f 0₂
  inv-eq-source-simplicial-hom f = inv (eq-source-simplicial-hom f)

  eq-target-simplicial-hom :
    {x y : A} (f : x →₂ y) → simplicial-arrow-simplicial-hom f 1₂ ＝ y
  eq-target-simplicial-hom f = pr2 (pr2 f)

  eq-source-target-simplicial-hom :
    {x y z : A} (f : x →₂ y) (g : y →₂ z) →
    simplicial-arrow-simplicial-hom f 1₂ ＝ simplicial-arrow-simplicial-hom g 0₂
  eq-source-target-simplicial-hom f g =
    eq-target-simplicial-hom f ∙ inv-eq-source-simplicial-hom g

  eq-source-source-simplicial-hom :
    {x y z : A} (f : x →₂ y) (g : x →₂ z) →
    simplicial-arrow-simplicial-hom f 0₂ ＝ simplicial-arrow-simplicial-hom g 0₂
  eq-source-source-simplicial-hom f g =
    eq-source-simplicial-hom f ∙ inv-eq-source-simplicial-hom g

  eq-target-target-simplicial-hom :
    {x y z : A} (f : x →₂ y) (g : z →₂ y) →
    simplicial-arrow-simplicial-hom f 1₂ ＝ simplicial-arrow-simplicial-hom g 1₂
  eq-target-target-simplicial-hom f g =
    eq-target-simplicial-hom f ∙ inv (eq-target-simplicial-hom g)
```

### The identity/constant directed edges

```agda
id-simplicial-hom : {l : Level} {A : UU l} (x : A) → x →₂ x
id-simplicial-hom = simplicial-hom-simplicial-arrow ∘ id-simplicial-arrow
```

### The representing edge of the directed interval

```agda
representing-hom-𝟚 : 0₂ →₂ 1₂
representing-hom-𝟚 = (id , refl , refl)
```

### Directed edges arising from equalities

```agda
simplicial-hom-eq :
  {l : Level} {A : UU l} {x y : A} → x ＝ y → x →₂ y
simplicial-hom-eq p =
  ( simplicial-arrow-eq p ,
    compute-source-simplicial-arrow-eq p ,
    compute-target-simplicial-arrow-eq p)
```

## Properties

### Characterizing equality of homomorphisms

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  coherence-htpy-simplicial-hom :
    (f g : x →₂ y) →
    simplicial-arrow-simplicial-hom f ~ simplicial-arrow-simplicial-hom g →
    UU l
  coherence-htpy-simplicial-hom f g H =
    ( eq-source-simplicial-hom f ＝ H 0₂ ∙ eq-source-simplicial-hom g) ×
    ( eq-target-simplicial-hom f ＝ H 1₂ ∙ eq-target-simplicial-hom g)

  htpy-simplicial-hom : (f g : x →₂ y) → UU l
  htpy-simplicial-hom f g =
    Σ ( simplicial-arrow-simplicial-hom f ~ simplicial-arrow-simplicial-hom g)
      ( coherence-htpy-simplicial-hom f g)

  refl-htpy-simplicial-hom :
    (f : x →₂ y) → htpy-simplicial-hom f f
  refl-htpy-simplicial-hom f = (refl-htpy , refl , refl)

  htpy-eq-simplicial-hom :
    (f g : x →₂ y) → f ＝ g → htpy-simplicial-hom f g
  htpy-eq-simplicial-hom f .f refl = refl-htpy-simplicial-hom f

  abstract
    is-torsorial-htpy-simplicial-hom :
      (f : x →₂ y) →
      is-contr (Σ (x →₂ y) (htpy-simplicial-hom f))
    is-torsorial-htpy-simplicial-hom f =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (simplicial-arrow-simplicial-hom f))
        ( simplicial-arrow-simplicial-hom f , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-Id (eq-source-simplicial-hom f))
          ( eq-source-simplicial-hom f , refl)
          ( is-torsorial-Id (eq-target-simplicial-hom f)))

  is-equiv-htpy-eq-simplicial-hom :
    (f g : x →₂ y) → is-equiv (htpy-eq-simplicial-hom f g)
  is-equiv-htpy-eq-simplicial-hom f =
    fundamental-theorem-id
      ( is-torsorial-htpy-simplicial-hom f)
      ( htpy-eq-simplicial-hom f)

  extensionality-simplicial-hom :
    (f g : x →₂ y) → (f ＝ g) ≃ (htpy-simplicial-hom f g)
  extensionality-simplicial-hom f g =
    ( htpy-eq-simplicial-hom f g , is-equiv-htpy-eq-simplicial-hom f g)

  eq-htpy-simplicial-hom :
    (f g : x →₂ y) → htpy-simplicial-hom f g → f ＝ g
  eq-htpy-simplicial-hom f g =
    map-inv-equiv (extensionality-simplicial-hom f g)
```

### The homotopy of directed edges associated to a homotopy of simplicial arrows

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  {f : simplicial-arrow A} (g : x →₂ y)
  (H : f ~ simplicial-arrow-simplicial-hom g)
  where

  simplicial-hom-htpy-simplicial-arrow : x →₂ y
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

### Computing the based total type of directed edges

```text
  Σ (𝟚 → A) (λ α → α 0₂ ＝ x) ≃ Σ (y : A), (x →₂ y)
```

```agda
module _
  {l : Level} {A : UU l} (x : A)
  where

  based-simplicial-hom : UU l
  based-simplicial-hom = Σ A (λ y → (x →₂ y))

  map-compute-based-simplicial-hom :
    Σ (𝟚 → A) (λ α → α 0₂ ＝ x) → based-simplicial-hom
  map-compute-based-simplicial-hom (α , p) = (α 1₂ , α , p , refl)

  map-inv-compute-based-simplicial-hom :
    based-simplicial-hom → Σ (𝟚 → A) (λ α → α 0₂ ＝ x)
  map-inv-compute-based-simplicial-hom (y , α , p , q) = (α , p)

  is-section-map-inv-compute-based-simplicial-hom :
    is-section
      ( map-compute-based-simplicial-hom)
      ( map-inv-compute-based-simplicial-hom)
  is-section-map-inv-compute-based-simplicial-hom
    (.(α 1₂) , α , p , refl) = refl

  is-retraction-map-inv-compute-based-simplicial-hom :
    is-retraction
      ( map-compute-based-simplicial-hom)
      ( map-inv-compute-based-simplicial-hom)
  is-retraction-map-inv-compute-based-simplicial-hom = refl-htpy

  is-equiv-map-compute-based-simplicial-hom :
    is-equiv map-compute-based-simplicial-hom
  is-equiv-map-compute-based-simplicial-hom =
    is-equiv-is-invertible
      ( map-inv-compute-based-simplicial-hom)
      ( is-section-map-inv-compute-based-simplicial-hom)
      ( is-retraction-map-inv-compute-based-simplicial-hom)

  is-equiv-map-inv-compute-based-simplicial-hom :
    is-equiv map-inv-compute-based-simplicial-hom
  is-equiv-map-inv-compute-based-simplicial-hom =
    is-equiv-is-invertible
      ( map-compute-based-simplicial-hom)
      ( is-retraction-map-inv-compute-based-simplicial-hom)
      ( is-section-map-inv-compute-based-simplicial-hom)

  compute-based-simplicial-hom :
    Σ (𝟚 → A) (λ α → α 0₂ ＝ x) ≃ based-simplicial-hom
  compute-based-simplicial-hom =
    ( map-compute-based-simplicial-hom ,
      is-equiv-map-compute-based-simplicial-hom)

  inv-compute-based-simplicial-hom :
    based-simplicial-hom ≃ Σ (𝟚 → A) (λ α → α 0₂ ＝ x)
  inv-compute-based-simplicial-hom =
    ( map-inv-compute-based-simplicial-hom ,
      is-equiv-map-inv-compute-based-simplicial-hom)
```

### Computing the total type of directed edges

The directed interval type classifies the total type of directed edges in a
type.

```text
  (𝟚 → A) ≃ Σ (x y : A), (x →₂ y)
```

```agda
module _
  {l : Level} {A : UU l}
  where

  total-simplicial-hom : UU l
  total-simplicial-hom = Σ A based-simplicial-hom

  map-compute-total-simplicial-hom :
    (𝟚 → A) → total-simplicial-hom
  map-compute-total-simplicial-hom α = (α 0₂ , α 1₂ , α , refl , refl)

  map-inv-compute-total-simplicial-hom :
    total-simplicial-hom → 𝟚 → A
  map-inv-compute-total-simplicial-hom (x , y , α , p , q) = α

  is-section-map-inv-compute-total-simplicial-hom :
    is-section
      ( map-compute-total-simplicial-hom)
      ( map-inv-compute-total-simplicial-hom)
  is-section-map-inv-compute-total-simplicial-hom
    (.(α 0₂) , .(α 1₂) , α , refl , refl) = refl

  is-retraction-map-inv-compute-total-simplicial-hom :
    is-retraction
      ( map-compute-total-simplicial-hom)
      ( map-inv-compute-total-simplicial-hom)
  is-retraction-map-inv-compute-total-simplicial-hom = refl-htpy

  is-equiv-map-compute-total-simplicial-hom :
    is-equiv map-compute-total-simplicial-hom
  is-equiv-map-compute-total-simplicial-hom =
    is-equiv-is-invertible
      ( map-inv-compute-total-simplicial-hom)
      ( is-section-map-inv-compute-total-simplicial-hom)
      ( is-retraction-map-inv-compute-total-simplicial-hom)

  is-equiv-map-inv-compute-total-simplicial-hom :
    is-equiv map-inv-compute-total-simplicial-hom
  is-equiv-map-inv-compute-total-simplicial-hom =
    is-equiv-is-invertible
      ( map-compute-total-simplicial-hom)
      ( is-retraction-map-inv-compute-total-simplicial-hom)
      ( is-section-map-inv-compute-total-simplicial-hom)

  compute-total-simplicial-hom :
    (𝟚 → A) ≃ total-simplicial-hom
  compute-total-simplicial-hom =
    ( map-compute-total-simplicial-hom ,
      is-equiv-map-compute-total-simplicial-hom)

  inv-compute-total-simplicial-hom :
    total-simplicial-hom ≃ (𝟚 → A)
  inv-compute-total-simplicial-hom =
    ( map-inv-compute-total-simplicial-hom ,
      is-equiv-map-inv-compute-total-simplicial-hom)
```

### The hom type is an extension type

The hom-type `x →₂ y` is equivalent to the
[type of extensions](orthogonal-factorization-systems.extensions-of-maps.md) of
`[x , y] : ∂𝟚 → A` along the inclusion `∂𝟚 ↪ 𝟚`.

```agda
module _
  {l : Level} {A : UU l} (x y : A)
  where

  compute-extension-type-simplicial-hom :
    (x →₂ y) ≃ extension map-directed-interval-bool (rec-bool y x)
  compute-extension-type-simplicial-hom =
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

  is-trunc-simplicial-hom : is-trunc k A → is-trunc k (x →₂ y)
  is-trunc-simplicial-hom is-trunc-A =
    is-trunc-equiv k
      ( extension map-directed-interval-bool (rec-bool y x))
      ( compute-extension-type-simplicial-hom x y)
      ( is-trunc-extension-dependent-type k
        ( map-directed-interval-bool)
        ( rec-bool y x)
        ( λ _ → is-trunc-A))
```
