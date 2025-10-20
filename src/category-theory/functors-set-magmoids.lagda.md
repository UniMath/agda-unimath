# Functors between set-magmoids

```agda
module category-theory.functors-set-magmoids where
```

<details><summary>Imports</summary>

```agda
open import category-theory.maps-set-magmoids
open import category-theory.set-magmoids

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor between [set-magmoids](category-theory.set-magmoids.md)** is a
family of maps on the hom-[sets](foundation-core.sets.md) that preserve the
[composition operation](category-theory.composition-operations-on-binary-families-of-sets.md).

These objects serve as our starting point in the study of
[structure](foundation.structure.md)-preserving maps of
[categories](category-theory.categories.md). Indeed, categories form a
[subtype](foundation-core.subtypes.md) of set-magmoids, although functors of
set-magmoids do not automatically preserve identity-morphisms.

## Definitions

### The predicate of being a functor of set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F₀ : obj-Set-Magmoid A → obj-Set-Magmoid B)
  (F₁ :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y → hom-Set-Magmoid B (F₀ x) (F₀ y))
  where

  preserves-comp-hom-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-Set-Magmoid =
    {x y z : obj-Set-Magmoid A}
    (g : hom-Set-Magmoid A y z) (f : hom-Set-Magmoid A x y) →
    F₁ (comp-hom-Set-Magmoid A g f) ＝ comp-hom-Set-Magmoid B (F₁ g) (F₁ f)

  is-prop-preserves-comp-hom-Set-Magmoid :
    is-prop preserves-comp-hom-Set-Magmoid
  is-prop-preserves-comp-hom-Set-Magmoid =
    is-prop-iterated-implicit-Π 3
      ( λ x y z →
        is-prop-iterated-Π 2
          ( λ g f →
            is-set-hom-Set-Magmoid B (F₀ x) (F₀ z)
              ( F₁ (comp-hom-Set-Magmoid A g f))
              ( comp-hom-Set-Magmoid B (F₁ g) (F₁ f))))

  preserves-comp-hom-prop-Set-Magmoid : Prop (l1 ⊔ l2 ⊔ l4)
  pr1 preserves-comp-hom-prop-Set-Magmoid =
    preserves-comp-hom-Set-Magmoid
  pr2 preserves-comp-hom-prop-Set-Magmoid =
    is-prop-preserves-comp-hom-Set-Magmoid
```

### The predicate on maps of set-magmoids of being a functor

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : map-Set-Magmoid A B)
  where

  preserves-comp-hom-prop-map-Set-Magmoid : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-map-Set-Magmoid =
    preserves-comp-hom-prop-Set-Magmoid A B
      ( obj-map-Set-Magmoid A B F)
      ( hom-map-Set-Magmoid A B F)

  preserves-comp-hom-map-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-map-Set-Magmoid =
    type-Prop preserves-comp-hom-prop-map-Set-Magmoid

  is-prop-preserves-comp-hom-map-Set-Magmoid :
    is-prop preserves-comp-hom-map-Set-Magmoid
  is-prop-preserves-comp-hom-map-Set-Magmoid =
    is-prop-type-Prop preserves-comp-hom-prop-map-Set-Magmoid
```

### The type of functors between set-magmoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  where

  functor-Set-Magmoid : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Set-Magmoid =
    Σ ( obj-Set-Magmoid A → obj-Set-Magmoid B)
      ( λ F₀ →
        Σ ( {x y : obj-Set-Magmoid A} →
            hom-Set-Magmoid A x y → hom-Set-Magmoid B (F₀ x) (F₀ y))
          ( preserves-comp-hom-Set-Magmoid A B F₀))

module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : functor-Set-Magmoid A B)
  where

  obj-functor-Set-Magmoid : obj-Set-Magmoid A → obj-Set-Magmoid B
  obj-functor-Set-Magmoid = pr1 F

  hom-functor-Set-Magmoid :
    {x y : obj-Set-Magmoid A} →
    (f : hom-Set-Magmoid A x y) →
    hom-Set-Magmoid B
      ( obj-functor-Set-Magmoid x)
      ( obj-functor-Set-Magmoid y)
  hom-functor-Set-Magmoid = pr1 (pr2 F)

  map-functor-Set-Magmoid : map-Set-Magmoid A B
  pr1 map-functor-Set-Magmoid = obj-functor-Set-Magmoid
  pr2 map-functor-Set-Magmoid = hom-functor-Set-Magmoid

  preserves-comp-functor-Set-Magmoid :
    {x y z : obj-Set-Magmoid A}
    (g : hom-Set-Magmoid A y z)
    (f : hom-Set-Magmoid A x y) →
    ( hom-functor-Set-Magmoid
      ( comp-hom-Set-Magmoid A g f)) ＝
    ( comp-hom-Set-Magmoid B
      ( hom-functor-Set-Magmoid g)
      ( hom-functor-Set-Magmoid f))
  preserves-comp-functor-Set-Magmoid = pr2 (pr2 F)
```

### The identity functor on a set-magmoid

```agda
module _
  {l1 l2 : Level} (A : Set-Magmoid l1 l2)
  where

  id-functor-Set-Magmoid : functor-Set-Magmoid A A
  pr1 id-functor-Set-Magmoid = id
  pr1 (pr2 id-functor-Set-Magmoid) = id
  pr2 (pr2 id-functor-Set-Magmoid) g f = refl
```

### Composition of functors on set-magmoids

Any two compatible functors can be composed to a new functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Set-Magmoid l1 l2)
  (B : Set-Magmoid l3 l4)
  (C : Set-Magmoid l5 l6)
  (G : functor-Set-Magmoid B C)
  (F : functor-Set-Magmoid A B)
  where

  obj-comp-functor-Set-Magmoid : obj-Set-Magmoid A → obj-Set-Magmoid C
  obj-comp-functor-Set-Magmoid =
    obj-functor-Set-Magmoid B C G ∘ obj-functor-Set-Magmoid A B F

  hom-comp-functor-Set-Magmoid :
    {x y : obj-Set-Magmoid A} →
    hom-Set-Magmoid A x y →
    hom-Set-Magmoid C
      ( obj-comp-functor-Set-Magmoid x)
      ( obj-comp-functor-Set-Magmoid y)
  hom-comp-functor-Set-Magmoid =
    hom-functor-Set-Magmoid B C G ∘ hom-functor-Set-Magmoid A B F

  map-comp-functor-Set-Magmoid : map-Set-Magmoid A C
  pr1 map-comp-functor-Set-Magmoid = obj-comp-functor-Set-Magmoid
  pr2 map-comp-functor-Set-Magmoid = hom-comp-functor-Set-Magmoid

  preserves-comp-comp-functor-Set-Magmoid :
    preserves-comp-hom-Set-Magmoid A C
      obj-comp-functor-Set-Magmoid
      hom-comp-functor-Set-Magmoid
  preserves-comp-comp-functor-Set-Magmoid g f =
    ( ap
      ( hom-functor-Set-Magmoid B C G)
      ( preserves-comp-functor-Set-Magmoid A B F g f)) ∙
    ( preserves-comp-functor-Set-Magmoid B C G
      ( hom-functor-Set-Magmoid A B F g)
      ( hom-functor-Set-Magmoid A B F f))

  comp-functor-Set-Magmoid : functor-Set-Magmoid A C
  pr1 comp-functor-Set-Magmoid = obj-comp-functor-Set-Magmoid
  pr1 (pr2 comp-functor-Set-Magmoid) =
    hom-functor-Set-Magmoid B C G ∘ hom-functor-Set-Magmoid A B F
  pr2 (pr2 comp-functor-Set-Magmoid) = preserves-comp-comp-functor-Set-Magmoid
```

## Properties

### Extensionality of functors between set-magmoids

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F G : functor-Set-Magmoid A B)
  where

  equiv-eq-map-eq-functor-Set-Magmoid :
    (F ＝ G) ≃ (map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G)
  equiv-eq-map-eq-functor-Set-Magmoid =
    equiv-ap-emb
      ( comp-emb
        ( emb-subtype (preserves-comp-hom-prop-map-Set-Magmoid A B))
        ( emb-equiv inv-associative-Σ))

  eq-map-eq-functor-Set-Magmoid :
    F ＝ G → map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G
  eq-map-eq-functor-Set-Magmoid = map-equiv equiv-eq-map-eq-functor-Set-Magmoid

  eq-eq-map-functor-Set-Magmoid :
    map-functor-Set-Magmoid A B F ＝ map-functor-Set-Magmoid A B G → F ＝ G
  eq-eq-map-functor-Set-Magmoid =
    map-inv-equiv equiv-eq-map-eq-functor-Set-Magmoid

  is-section-eq-eq-map-functor-Set-Magmoid :
    eq-map-eq-functor-Set-Magmoid ∘ eq-eq-map-functor-Set-Magmoid ~ id
  is-section-eq-eq-map-functor-Set-Magmoid =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Set-Magmoid

  is-retraction-eq-eq-map-functor-Set-Magmoid :
    eq-eq-map-functor-Set-Magmoid ∘ eq-map-eq-functor-Set-Magmoid ~ id
  is-retraction-eq-eq-map-functor-Set-Magmoid =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Set-Magmoid
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (A : Set-Magmoid l1 l2) (B : Set-Magmoid l3 l4)
  (F : functor-Set-Magmoid A B)
  where

  left-unit-law-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A B B (id-functor-Set-Magmoid B) F ＝ F
  left-unit-law-comp-functor-Set-Magmoid =
    eq-eq-map-functor-Set-Magmoid A B _ _ refl

  right-unit-law-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A A B F (id-functor-Set-Magmoid A) ＝ F
  right-unit-law-comp-functor-Set-Magmoid = refl
```

#### Associativity of functor composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (F : functor-Set-Magmoid A B)
  (G : functor-Set-Magmoid B C)
  (H : functor-Set-Magmoid C D)
  where

  associative-comp-functor-Set-Magmoid :
    comp-functor-Set-Magmoid A B D (comp-functor-Set-Magmoid B C D H G) F ＝
    comp-functor-Set-Magmoid A C D H (comp-functor-Set-Magmoid A B C G F)
  associative-comp-functor-Set-Magmoid =
    eq-eq-map-functor-Set-Magmoid A D _ _ refl
```

#### Mac Lane pentagon for functor composition

```text
    (I(GH))F ---- I((GH)F)
          /        \
         /          \
  ((IH)G)F          I(H(GF))
          \        /
            \    /
           (IH)(GF)
```

The proof remains to be formalized.

```text
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Set-Magmoid l1 l1')
  (B : Set-Magmoid l2 l2')
  (C : Set-Magmoid l3 l3')
  (D : Set-Magmoid l4 l4')
  (E : Set-Magmoid l4 l4')
  (F : functor-Set-Magmoid A B)
  (G : functor-Set-Magmoid B C)
  (H : functor-Set-Magmoid C D)
  (I : functor-Set-Magmoid D E)
  where

  mac-lane-pentagon-comp-functor-Set-Magmoid :
    coherence-pentagon-identifications
      { x =
        comp-functor-Set-Magmoid A B E
        ( comp-functor-Set-Magmoid B D E I
          ( comp-functor-Set-Magmoid B C D H G))
        ( F)}
      { comp-functor-Set-Magmoid A D E I
        ( comp-functor-Set-Magmoid A B D
          ( comp-functor-Set-Magmoid B C D H G)
          ( F))}
      { comp-functor-Set-Magmoid A B E
        ( comp-functor-Set-Magmoid B C E
          ( comp-functor-Set-Magmoid C D E I H)
          ( G))
        ( F)}
      { comp-functor-Set-Magmoid A D E
        ( I)
        ( comp-functor-Set-Magmoid A C D
          ( H)
          ( comp-functor-Set-Magmoid A B C G F))}
      { comp-functor-Set-Magmoid A C E
        ( comp-functor-Set-Magmoid C D E I H)
        ( comp-functor-Set-Magmoid A B C G F)}
      ( associative-comp-functor-Set-Magmoid A B D E
        ( F) (comp-functor-Set-Magmoid B C D H G) (I))
      ( ap
        ( λ p → comp-functor-Set-Magmoid A B E p F)
        ( inv (associative-comp-functor-Set-Magmoid B C D E G H I)))
      ( ap
        ( λ p → comp-functor-Set-Magmoid A D E I p)
        ( associative-comp-functor-Set-Magmoid A B C D F G H))
      ( associative-comp-functor-Set-Magmoid A B C E
        ( F) (G) (comp-functor-Set-Magmoid C D E I H))
      ( inv
        ( associative-comp-functor-Set-Magmoid A C D E
          (comp-functor-Set-Magmoid A B C G F) H I))
  mac-lane-pentagon-comp-functor-Set-Magmoid = {!!}
```
