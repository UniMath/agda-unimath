# Morphisms in the slice category of types

```agda
module foundation.slice where
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
morphism in the slice from `f : A → X` to `g : B → X` consists of a function
`h : A → B` such that the triangle `f ~ g ∘ h` commutes. We make these
definitions for types.

## Definition

### The objects of the slice category of types

```agda
Slice : (l : Level) {l1 : Level} (A : UU l1) → UU (l1 ⊔ lsuc l)
Slice l = type-polynomial-endofunctor (universal-polynomial-endofunctor l)
```

### The morphisms in the slice category of types

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  hom-slice :
    (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  hom-slice f g = Σ (A → B) (λ h → f ~ (g ∘ h))

  map-hom-slice :
    (f : A → X) (g : B → X) → hom-slice f g → A → B
  map-hom-slice f g h = pr1 h

  triangle-hom-slice :
    (f : A → X) (g : B → X) (h : hom-slice f g) →
    f ~ g ∘ map-hom-slice f g h
  triangle-hom-slice f g h = pr2 h
```

## Properties

### We characterize the identity type of hom-slice

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
  extensionality-hom-slice (pair h H) =
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

```agda
comp-hom-slice :
  {l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4}
  (f : A → X) (g : B → X) (h : C → X) →
  hom-slice g h → hom-slice f g → hom-slice f h
pr1 (comp-hom-slice f g h j i) = map-hom-slice g h j ∘ map-hom-slice f g i
pr2 (comp-hom-slice f g h j i) =
  ( triangle-hom-slice f g i) ∙h
  ( (triangle-hom-slice g h j) ·r (map-hom-slice f g i))

id-hom-slice :
  {l1 l2 : Level} {X : UU l1} {A : UU l2} (f : A → X) → hom-slice f f
pr1 (id-hom-slice f) = id
pr2 (id-hom-slice f) = refl-htpy

is-equiv-hom-slice :
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) → hom-slice f g → UU (l2 ⊔ l3)
is-equiv-hom-slice f g h = is-equiv (map-hom-slice f g h)
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
  fiberwise-hom-hom-slice (pair h H) = fiber-triangle f g h H

  hom-slice-fiberwise-hom : fiberwise-hom f g → hom-slice f g
  pr1 (hom-slice-fiberwise-hom α) a = pr1 (α (f a) (pair a refl))
  pr2 (hom-slice-fiberwise-hom α) a = inv (pr2 (α (f a) (pair a refl)))

  is-section-hom-slice-fiberwise-hom-eq-htpy :
    (α : fiberwise-hom f g) (x : X) →
    (fiberwise-hom-hom-slice (hom-slice-fiberwise-hom α) x) ~ (α x)
  is-section-hom-slice-fiberwise-hom-eq-htpy α .(f a) (pair a refl) =
    eq-pair-eq-fiber (inv-inv (pr2 (α (f a) (pair a refl))))

  is-section-hom-slice-fiberwise-hom :
    (fiberwise-hom-hom-slice ∘ hom-slice-fiberwise-hom) ~ id
  is-section-hom-slice-fiberwise-hom α =
    eq-htpy (λ x → eq-htpy (is-section-hom-slice-fiberwise-hom-eq-htpy α x))

  is-retraction-hom-slice-fiberwise-hom :
    (hom-slice-fiberwise-hom ∘ fiberwise-hom-hom-slice) ~ id
  is-retraction-hom-slice-fiberwise-hom (pair h H) =
    eq-pair-eq-fiber (eq-htpy (inv-inv ∘ H))

  abstract
    is-equiv-fiberwise-hom-hom-slice : is-equiv (fiberwise-hom-hom-slice)
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

### A morphism in the slice over `X` is an equivalence if and only if the induced map between fibers is a fiberwise equivalence

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  where

  equiv-slice : (A → X) → (B → X) → UU (l1 ⊔ l2 ⊔ l3)
  equiv-slice f g = Σ (A ≃ B) (λ e → f ~ (g ∘ map-equiv e))

  hom-equiv-slice :
    (f : A → X) (g : B → X) → equiv-slice f g → hom-slice f g
  pr1 (hom-equiv-slice f g e) = pr1 (pr1 e)
  pr2 (hom-equiv-slice f g e) = pr2 e

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X)
  where

  abstract
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice :
      (t : hom-slice f g) → is-equiv (pr1 t) →
      is-fiberwise-equiv (fiberwise-hom-hom-slice f g t)
    is-fiberwise-equiv-fiberwise-equiv-equiv-slice (pair h H) =
      is-fiberwise-equiv-is-equiv-triangle f g h H

  abstract
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice :
      (t : hom-slice f g) →
      ((x : X) → is-equiv (fiberwise-hom-hom-slice f g t x)) →
      is-equiv (pr1 t)
    is-equiv-hom-slice-is-fiberwise-equiv-fiberwise-hom-hom-slice
      (pair h H) =
      is-equiv-triangle-is-fiberwise-equiv f g h H

  equiv-fiberwise-equiv-equiv-slice :
    equiv-slice f g ≃ fiberwise-equiv (fiber f) (fiber g)
  equiv-fiberwise-equiv-equiv-slice =
    equiv-Σ is-fiberwise-equiv (equiv-fiberwise-hom-hom-slice f g) α ∘e
    equiv-right-swap-Σ
    where
    α :
      (h : hom-slice f g) →
      is-equiv (pr1 h) ≃
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
    equiv-slice f g ≃ ((x : X) → fiber f x ≃ fiber g x) -- fam-equiv (fiber f) (fiber g)
  equiv-fam-equiv-equiv-slice =
    inv-distributive-Π-Σ ∘e equiv-fiberwise-equiv-equiv-slice
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

  abstract
    is-equiv-hom-slice-emb :
      (f : A ↪ X) (g : B ↪ X) (h : hom-slice (map-emb f) (map-emb g)) →
      hom-slice (map-emb g) (map-emb f) →
      is-equiv-hom-slice (map-emb f) (map-emb g) h
    is-equiv-hom-slice-emb f g h i =
      is-equiv-is-invertible
        ( map-hom-slice (map-emb g) (map-emb f) i)
        ( λ y →
          is-injective-emb g
          ( inv
            ( ( triangle-hom-slice
                ( map-emb g)
                ( map-emb f)
                ( i)
                ( y)) ∙
              ( triangle-hom-slice
                ( map-emb f)
                ( map-emb g)
                ( h)
                ( map-hom-slice (map-emb g) (map-emb f) i y)))))
        ( λ x →
          is-injective-emb f
          ( inv
            ( ( triangle-hom-slice (map-emb f) (map-emb g) h x) ∙
              ( triangle-hom-slice (map-emb g) (map-emb f) i
                ( map-hom-slice
                  ( map-emb f)
                  ( map-emb g)
                  ( h)
                  ( x))))))
```

### Characterization of the identity type of `Slice l A`

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  equiv-slice' : (f g : Slice l2 A) → UU (l1 ⊔ l2)
  equiv-slice' f g = equiv-slice (pr2 f) (pr2 g)

  id-equiv-Slice : (f : Slice l2 A) → equiv-slice' f f
  pr1 (id-equiv-Slice f) = id-equiv
  pr2 (id-equiv-Slice f) = refl-htpy

  equiv-eq-Slice : (f g : Slice l2 A) → f ＝ g → equiv-slice' f g
  equiv-eq-Slice f .f refl = id-equiv-Slice f
```

### Univalence in a slice

```agda
module _
  {l1 l2 : Level} {A : UU l1}
  where

  abstract
    is-torsorial-equiv-slice' :
      (f : Slice l2 A) → is-torsorial (equiv-slice' f)
    is-torsorial-equiv-slice' (pair X f) =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv X)
        ( pair X id-equiv)
        ( is-torsorial-htpy f)

  abstract
    is-equiv-equiv-eq-Slice :
      (f g : Slice l2 A) → is-equiv (equiv-eq-Slice f g)
    is-equiv-equiv-eq-Slice f =
      fundamental-theorem-id
        ( is-torsorial-equiv-slice' f)
        ( equiv-eq-Slice f)

  extensionality-Slice :
    (f g : Slice l2 A) → (f ＝ g) ≃ equiv-slice' f g
  pr1 (extensionality-Slice f g) = equiv-eq-Slice f g
  pr2 (extensionality-Slice f g) = is-equiv-equiv-eq-Slice f g

  eq-equiv-slice :
    (f g : Slice l2 A) → equiv-slice' f g → f ＝ g
  eq-equiv-slice f g =
    map-inv-is-equiv (is-equiv-equiv-eq-Slice f g)
```

## See also

- For the formally dual notion see
  [`foundation.coslice`](foundation.coslice.md).
- For slices in the context of category theory see
  [`category-theory.slice-precategories`](category-theory.slice-precategories.md).
- For fibered maps see [`foundation.fibered-maps`](foundation.fibered-maps.md).
