# Morphisms in the slice above a type

```agda
module foundation.morphisms-slice where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.logical-equivalences
open import foundation.slice
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.embeddings
open import foundation-core.equality-dependent-pair-types
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice

open import trees.polynomial-endofunctors
open import trees.universal-polynomial-endofunctor
```

</details>

## Idea

The slice of a category over an object X is the category of morphisms into X. A
{{#concept "morphism" Agda=hom-slice}} in the slice from `f : A → X` to
`g : B → X` consists of a function `h : A → B` such that the triangle
`f ~ g ∘ h` commutes. We make these definitions for types.

## Definitions

### Morphisms in the slice above a type

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  hom-slice :
    (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  hom-slice f g = Σ (A → B) (λ h → f ~ g ∘ h)

  map-hom-slice :
    (f : A → X) (g : B → X) → hom-slice f g → A → B
  map-hom-slice f g h = pr1 h

  triangle-hom-slice :
    (f : A → X) (g : B → X) (h : hom-slice f g) →
    f ~ g ∘ map-hom-slice f g h
  triangle-hom-slice f g h = pr2 h
```

## Properties

### Chharacterizing the identity type of morphisms in the slice above a type

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  coherence-htpy-hom-slice :
    (h h' : hom-slice f g) →
    map-hom-slice f g h ~ map-hom-slice f g h' →
    UU (l1 ⊔ l2)
  coherence-htpy-hom-slice h h' H =
      coherence-triangle-homotopies'
        ( triangle-hom-slice f g h')
        ( g ·l H)
        ( triangle-hom-slice f g h)

  htpy-hom-slice : (h h' : hom-slice f g) → UU (l1 ⊔ l2 ⊔ l3)
  htpy-hom-slice h h' =
    Σ ( map-hom-slice f g h ~ map-hom-slice f g h')
      ( coherence-htpy-hom-slice h h')

  extensionality-hom-slice :
    (h h' : hom-slice f g) → (h ＝ h') ≃ htpy-hom-slice h h'
  extensionality-hom-slice (h , H) =
    extensionality-Σ
      ( λ {h'} H' (K : h ~ h') → (H ∙h (g ·l K)) ~ H')
      ( refl-htpy)
      ( right-unit-htpy)
      ( λ h' → equiv-funext)
      ( λ H' → equiv-concat-htpy right-unit-htpy H' ∘e equiv-funext)

  eq-htpy-hom-slice :
    (h h' : hom-slice f g) → htpy-hom-slice h h' → h ＝ h'
  eq-htpy-hom-slice h h' = map-inv-equiv (extensionality-hom-slice h h')
```

### Composition of morphisms in the slice

```agda
comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
pr1 (comp-hom-slice f g h j i) = map-hom-slice g h j ∘ map-hom-slice f g i
pr2 (comp-hom-slice f g h j i) =
  ( triangle-hom-slice f g i) ∙h
  ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i))
```

### The identity morphism

```agda
id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
pr1 (id-hom-slice f) = id
pr2 (id-hom-slice f) = refl-htpy
```

### Morphisms in the slice are equivalently described as families of maps between fibers

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  fiberwise-hom : (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  fiberwise-hom f g = (x : X) → fiber f x → fiber g x

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  fiberwise-hom-hom-slice : hom-slice f g → fiberwise-hom f g
  fiberwise-hom-hom-slice (h , H) = fiber-triangle f g h H

  hom-slice-fiberwise-hom : fiberwise-hom f g → hom-slice f g
  pr1 (hom-slice-fiberwise-hom α) a = pr1 (α (f a) (a , refl))
  pr2 (hom-slice-fiberwise-hom α) a = inv (pr2 (α (f a) (a , refl)))

  is-section-hom-slice-fiberwise-hom-eq-htpy :
    (α : fiberwise-hom f g) (x : X) →
    fiberwise-hom-hom-slice (hom-slice-fiberwise-hom α) x ~ α x
  is-section-hom-slice-fiberwise-hom-eq-htpy α .(f a) (a , refl) =
    eq-pair-eq-fiber (inv-inv (pr2 (α (f a) (a , refl))))

  is-section-hom-slice-fiberwise-hom :
    is-section fiberwise-hom-hom-slice hom-slice-fiberwise-hom
  is-section-hom-slice-fiberwise-hom α =
    eq-htpy (λ x → eq-htpy (is-section-hom-slice-fiberwise-hom-eq-htpy α x))

  is-retraction-hom-slice-fiberwise-hom :
    is-retraction fiberwise-hom-hom-slice hom-slice-fiberwise-hom
  is-retraction-hom-slice-fiberwise-hom (h , H) =
    eq-pair-eq-fiber (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-hom-hom-slice : is-equiv fiberwise-hom-hom-slice
    is-equiv-fiberwise-hom-hom-slice =
      is-equiv-is-invertible
        ( hom-slice-fiberwise-hom)
        ( is-section-hom-slice-fiberwise-hom)
        ( is-retraction-hom-slice-fiberwise-hom)

  equiv-fiberwise-hom-hom-slice : hom-slice f g ≃ fiberwise-hom f g
  pr1 equiv-fiberwise-hom-hom-slice = fiberwise-hom-hom-slice
  pr2 equiv-fiberwise-hom-hom-slice = is-equiv-fiberwise-hom-hom-slice

  abstract
    is-equiv-hom-slice-fiberwise-hom : is-equiv hom-slice-fiberwise-hom
    is-equiv-hom-slice-fiberwise-hom =
      is-equiv-is-invertible
        ( fiberwise-hom-hom-slice)
        ( is-retraction-hom-slice-fiberwise-hom)
        ( is-section-hom-slice-fiberwise-hom)

  equiv-hom-slice-fiberwise-hom :
    fiberwise-hom f g ≃ hom-slice f g
  pr1 equiv-hom-slice-fiberwise-hom = hom-slice-fiberwise-hom
  pr2 equiv-hom-slice-fiberwise-hom = is-equiv-hom-slice-fiberwise-hom
```

### The type of slice morphisms into an embedding is a proposition

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-prop-hom-slice :
      (f : A → X) (i : B ↪ X) → is-prop (hom-slice f (map-emb i))
    is-prop-hom-slice f i =
      is-prop-is-equiv
        ( is-equiv-fiberwise-hom-hom-slice f (map-emb i))
        ( is-prop-Π
          ( λ x → is-prop-Π
            ( λ p → is-prop-map-is-emb (is-emb-map-emb i) x)))
```

## See also

- For slices in the context of category theory see
  [`category-theory.slice-precategories`](category-theory.slice-precategories.md).
- For the formally dual notion see
  [`foundation.morphisms-coslice`](foundation.morphisms-coslice.md).
