# Equivalences in the slice above a type

```agda
module foundation.equivalences-slice where
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
open import foundation.morphisms-slice
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
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice

open import trees.polynomial-endofunctors
open import trees.universal-polynomial-endofunctor
```

</details>

## Idea

The slice of a category over an object X is the category of morphisms into X. A
{{#concept "morphism"}} in the slice from `f : A → X` to `g : B → X` consists of
a function `h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make
these definitions for types.

## Definitions

### The predicate on a morphism in the slice of being an equivalence

```agda
is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)
```

### The type of equivalences in the slice

```agda
equiv-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3} →
  (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
equiv-slice {A = A} {B = B} f g = Σ (A ≃ B) (λ e → f ~ g ∘ map-equiv e)

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (e : equiv-slice f g)
  where

  equiv-equiv-slice : A ≃ B
  equiv-equiv-slice = pr1 e

  map-equiv-slice : A → B
  map-equiv-slice = map-equiv equiv-equiv-slice

  is-equiv-map-equiv-slice : is-equiv map-equiv-slice
  is-equiv-map-equiv-slice = is-equiv-map-equiv equiv-equiv-slice

  coh-equiv-slice : f ~ g ∘ map-equiv-slice
  coh-equiv-slice = pr2 e

  hom-equiv-slice : hom-slice f g
  hom-equiv-slice = (map-equiv-slice , coh-equiv-slice)
```

## Properties

### A morphism in the slice over `X` is an equivalence if and only if the induced map between fibers is a fiberwise equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  abstract
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
      (t : hom-slice f g) → is-equiv (map-hom-slice f g t) →
      is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice (h , H) =
      is-fiberwise-equiv-is-equiv-triangle f g h H

  abstract
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
      (t : hom-slice f g) →
      ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
      is-equiv (map-hom-slice f g t)
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice (h , H) =
      is-equiv-triangle-is-fiberwise-equiv f g h H

  equiv-fiberwise-equiv-equiv-slice :
    equiv-slice f g ≃ fiberwise-equiv (fiber f) (fiber g)
  equiv-fiberwise-equiv-equiv-slice =
    equiv-Σ is-fiberwise-equiv (equiv-fiberwise-hom-hom-slice f g) α ∘e
    equiv-right-swap-Σ
    where
    α :
      (h : hom-slice f g) →
      is-equiv (map-hom-slice f g h) ≃
      is-fiberwise-equiv (map-equiv (equiv-fiberwise-hom-hom-slice f g) h)
    α h =
      equiv-iff-is-prop
        ( is-property-is-equiv _)
        ( is-prop-Π (λ _ → is-property-is-equiv _))
        ( is-fiberwise-equiv-fiberwise-equiv-equiv-slice h)
        ( is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice h)

  equiv-equiv-slice-fiberwise-equiv :
    fiberwise-equiv (fiber f) (fiber g) ≃ equiv-slice f g
  equiv-equiv-slice-fiberwise-equiv =
    inv-equiv equiv-fiberwise-equiv-equiv-slice

  fiberwise-equiv-equiv-slice :
    equiv-slice f g → fiberwise-equiv (fiber f) (fiber g)
  fiberwise-equiv-equiv-slice =
    map-equiv equiv-fiberwise-equiv-equiv-slice

  equiv-fam-equiv-equiv-slice :
    equiv-slice f g ≃ fam-equiv (fiber f) (fiber g)
  equiv-fam-equiv-equiv-slice =
    inv-distributive-Π-Σ ∘e equiv-fiberwise-equiv-equiv-slice
```

### Logically equivalent embeddings into a type are equivalent slices over that type

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  abstract
    is-equiv-hom-slice-emb :
      (f : A ↪ X) (g : B ↪ X)
      (h : hom-slice (map-emb f) (map-emb g)) →
      hom-slice (map-emb g) (map-emb f) →
      is-equiv-hom-slice (map-emb f) (map-emb g) h
    is-equiv-hom-slice-emb f g h i =
      is-equiv-is-invertible
        ( map-hom-slice (map-emb g) (map-emb f) i)
        ( λ y →
          is-injective-emb g
            ( inv
              ( ( triangle-hom-slice (map-emb g) (map-emb f) i y) ∙
                ( triangle-hom-slice
                  ( map-emb f)
                  ( map-emb g)
                  ( h)
                  ( map-hom-slice (map-emb g) (map-emb f) i y)))))
        ( λ x →
          is-injective-emb f
            ( inv
              ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
                ( triangle-hom-slice
                  ( map-emb g)
                  ( map-emb f)
                  ( i)
                  ( map-hom-slice (map-emb f) (map-emb g) h x)))))
```

### Characterization of the identity type of `Slice l A`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-Slice : (f g : Slice l2 A) → UU (l1 ⊔ l2)
  equiv-Slice f g = equiv-slice (map-Slice f) (map-Slice g)

  id-equiv-Slice : (f : Slice l2 A) → equiv-Slice f f
  id-equiv-Slice f = (id-equiv , refl-htpy)

  equiv-eq-Slice : (f g : Slice l2 A) → f ＝ g → equiv-Slice f g
  equiv-eq-Slice f .f refl = id-equiv-Slice f
```

### Univalence in a slice

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-torsorial-equiv-Slice : (f : Slice l2 A) → is-torsorial (equiv-Slice f)
    is-torsorial-equiv-Slice (X , f) =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv X)
        ( X , id-equiv)
        ( is-torsorial-htpy f)

  abstract
    is-equiv-equiv-eq-Slice : (f g : Slice l2 A) → is-equiv (equiv-eq-Slice f g)
    is-equiv-equiv-eq-Slice f =
      fundamental-theorem-id
        ( is-torsorial-equiv-Slice f)
        ( equiv-eq-Slice f)

  extensionality-Slice : (f g : Slice l2 A) → (f ＝ g) ≃ equiv-Slice f g
  extensionality-Slice f g = (equiv-eq-Slice f g , is-equiv-equiv-eq-Slice f g)

  eq-equiv-Slice : (f g : Slice l2 A) → equiv-Slice f g → f ＝ g
  eq-equiv-Slice f g = map-inv-equiv (extensionality-Slice f g)
```
