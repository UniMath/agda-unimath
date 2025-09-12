# Functors between precategories

```agda
module category-theory.functors-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-set-magmoids
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.opposite-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A **functor** from a [precategory](category-theory.precategories.md) `C` to a
precategory `D` consists of:

- a map `F₀ : C → D` on objects,
- a map `F₁ : hom x y → hom (F₀ x) (F₀ y)` on morphisms, such that the following
  identities hold:
- `F₁ id_x = id_(F₀ x)`,
- `F₁ (g ∘ f) = F₁ g ∘ F₁ f`.

## Definition

### The predicate on maps between precategories of being a functor

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : map-Precategory C D)
  where

  preserves-comp-hom-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-prop-map-Precategory =
    preserves-comp-hom-prop-map-Set-Magmoid
      ( set-magmoid-Precategory C)
      ( set-magmoid-Precategory D)
      (F)

  preserves-comp-hom-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  preserves-comp-hom-map-Precategory =
    type-Prop preserves-comp-hom-prop-map-Precategory

  is-prop-preserves-comp-hom-map-Precategory :
    is-prop preserves-comp-hom-map-Precategory
  is-prop-preserves-comp-hom-map-Precategory =
    is-prop-type-Prop preserves-comp-hom-prop-map-Precategory

  preserves-id-hom-map-Precategory : UU (l1 ⊔ l4)
  preserves-id-hom-map-Precategory =
    (x : obj-Precategory C) →
    ( hom-map-Precategory C D F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-map-Precategory C D F x})

  is-prop-preserves-id-hom-map-Precategory :
    is-prop preserves-id-hom-map-Precategory
  is-prop-preserves-id-hom-map-Precategory =
    is-prop-Π
      ( λ x →
        is-set-hom-Precategory D
          ( obj-map-Precategory C D F x)
          ( obj-map-Precategory C D F x)
          ( hom-map-Precategory C D F (id-hom-Precategory C {x}))
          ( id-hom-Precategory D {obj-map-Precategory C D F x}))

  preserves-id-hom-prop-map-Precategory : Prop (l1 ⊔ l4)
  pr1 preserves-id-hom-prop-map-Precategory =
    preserves-id-hom-map-Precategory
  pr2 preserves-id-hom-prop-map-Precategory =
    is-prop-preserves-id-hom-map-Precategory

  is-functor-prop-map-Precategory : Prop (l1 ⊔ l2 ⊔ l4)
  is-functor-prop-map-Precategory =
    product-Prop
      preserves-comp-hom-prop-map-Precategory
      preserves-id-hom-prop-map-Precategory

  is-functor-map-Precategory : UU (l1 ⊔ l2 ⊔ l4)
  is-functor-map-Precategory = type-Prop is-functor-prop-map-Precategory

  is-prop-is-functor-map-Precategory :
    is-prop is-functor-map-Precategory
  is-prop-is-functor-map-Precategory =
    is-prop-type-Prop is-functor-prop-map-Precategory

  preserves-comp-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-comp-hom-map-Precategory
  preserves-comp-is-functor-map-Precategory = pr1

  preserves-id-is-functor-map-Precategory :
    is-functor-map-Precategory → preserves-id-hom-map-Precategory
  preserves-id-is-functor-map-Precategory = pr2
```

### Functors between precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  where

  functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  functor-Precategory =
    Σ ( obj-Precategory C → obj-Precategory D)
      ( λ F₀ →
        Σ ( {x y : obj-Precategory C}
            (f : hom-Precategory C x y) →
            hom-Precategory D (F₀ x) (F₀ y))
          ( λ F₁ → is-functor-map-Precategory C D (F₀ , F₁)))

  obj-functor-Precategory :
    functor-Precategory → obj-Precategory C → obj-Precategory D
  obj-functor-Precategory = pr1

  hom-functor-Precategory :
    (F : functor-Precategory) →
    {x y : obj-Precategory C} →
    (f : hom-Precategory C x y) →
    hom-Precategory D
      ( obj-functor-Precategory F x)
      ( obj-functor-Precategory F y)
  hom-functor-Precategory F = pr1 (pr2 F)

  map-functor-Precategory : functor-Precategory → map-Precategory C D
  pr1 (map-functor-Precategory F) = obj-functor-Precategory F
  pr2 (map-functor-Precategory F) = hom-functor-Precategory F

  is-functor-functor-Precategory :
    (F : functor-Precategory) →
    is-functor-map-Precategory C D (map-functor-Precategory F)
  is-functor-functor-Precategory = pr2 ∘ pr2

  preserves-comp-functor-Precategory :
    (F : functor-Precategory) {x y z : obj-Precategory C}
    (g : hom-Precategory C y z) (f : hom-Precategory C x y) →
    ( hom-functor-Precategory F (comp-hom-Precategory C g f)) ＝
    ( comp-hom-Precategory D
      ( hom-functor-Precategory F g)
      ( hom-functor-Precategory F f))
  preserves-comp-functor-Precategory F =
    preserves-comp-is-functor-map-Precategory C D
      ( map-functor-Precategory F)
      ( is-functor-functor-Precategory F)

  preserves-id-functor-Precategory :
    (F : functor-Precategory) (x : obj-Precategory C) →
    ( hom-functor-Precategory F (id-hom-Precategory C {x})) ＝
    ( id-hom-Precategory D {obj-functor-Precategory F x})
  preserves-id-functor-Precategory F =
    preserves-id-is-functor-map-Precategory C D
      ( map-functor-Precategory F)
      ( is-functor-functor-Precategory F)

  functor-map-Precategory :
    (F : map-Precategory C D) →
    is-functor-map-Precategory C D F →
    functor-Precategory
  pr1 (functor-map-Precategory F is-functor-F) =
    obj-map-Precategory C D F
  pr1 (pr2 (functor-map-Precategory F is-functor-F)) =
    hom-map-Precategory C D F
  pr2 (pr2 (functor-map-Precategory F is-functor-F)) =
    is-functor-F
```

## Examples

### The identity functor

There is an identity functor on any precategory.

```agda
id-functor-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2) → functor-Precategory C C
pr1 (id-functor-Precategory C) = id
pr1 (pr2 (id-functor-Precategory C)) = id
pr1 (pr2 (pr2 (id-functor-Precategory C))) g f = refl
pr2 (pr2 (pr2 (id-functor-Precategory C))) x = refl
```

### Composition of functors

Any two compatible functors can be composed to a new functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (A : Precategory l1 l2) (B : Precategory l3 l4) (C : Precategory l5 l6)
  (G : functor-Precategory B C) (F : functor-Precategory A B)
  where

  obj-comp-functor-Precategory : obj-Precategory A → obj-Precategory C
  obj-comp-functor-Precategory =
    obj-functor-Precategory B C G ∘ obj-functor-Precategory A B F

  hom-comp-functor-Precategory :
    {x y : obj-Precategory A} →
    hom-Precategory A x y →
    hom-Precategory C
      ( obj-comp-functor-Precategory x)
      ( obj-comp-functor-Precategory y)
  hom-comp-functor-Precategory =
    hom-functor-Precategory B C G ∘ hom-functor-Precategory A B F

  map-comp-functor-Precategory : map-Precategory A C
  pr1 map-comp-functor-Precategory = obj-comp-functor-Precategory
  pr2 map-comp-functor-Precategory = hom-comp-functor-Precategory

  preserves-comp-comp-functor-Precategory :
    preserves-comp-hom-map-Precategory A C map-comp-functor-Precategory
  preserves-comp-comp-functor-Precategory g f =
    ( ap
      ( hom-functor-Precategory B C G)
      ( preserves-comp-functor-Precategory A B F g f)) ∙
    ( preserves-comp-functor-Precategory B C G
      ( hom-functor-Precategory A B F g)
      ( hom-functor-Precategory A B F f))

  preserves-id-comp-functor-Precategory :
    preserves-id-hom-map-Precategory A C map-comp-functor-Precategory
  preserves-id-comp-functor-Precategory x =
    ( ap
      ( hom-functor-Precategory B C G)
      ( preserves-id-functor-Precategory A B F x)) ∙
    ( preserves-id-functor-Precategory B C G
      ( obj-functor-Precategory A B F x))

  comp-functor-Precategory : functor-Precategory A C
  pr1 comp-functor-Precategory = obj-comp-functor-Precategory
  pr1 (pr2 comp-functor-Precategory) =
    hom-functor-Precategory B C G ∘ hom-functor-Precategory A B F
  pr1 (pr2 (pr2 comp-functor-Precategory)) =
    preserves-comp-comp-functor-Precategory
  pr2 (pr2 (pr2 comp-functor-Precategory)) =
    preserves-id-comp-functor-Precategory
```

## Properties

### Extensionality of functors between precategories

#### Equality of functors is equality of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  equiv-eq-map-eq-functor-Precategory :
    (F ＝ G) ≃ (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  equiv-eq-map-eq-functor-Precategory =
    equiv-ap-emb
      ( comp-emb
        ( emb-subtype (is-functor-prop-map-Precategory C D))
        ( emb-equiv inv-associative-Σ))

  eq-map-eq-functor-Precategory :
    (F ＝ G) → (map-functor-Precategory C D F ＝ map-functor-Precategory C D G)
  eq-map-eq-functor-Precategory =
    map-equiv equiv-eq-map-eq-functor-Precategory

  eq-eq-map-functor-Precategory :
    (map-functor-Precategory C D F ＝ map-functor-Precategory C D G) → (F ＝ G)
  eq-eq-map-functor-Precategory =
    map-inv-equiv equiv-eq-map-eq-functor-Precategory

  is-section-eq-eq-map-functor-Precategory :
    eq-map-eq-functor-Precategory ∘ eq-eq-map-functor-Precategory ~ id
  is-section-eq-eq-map-functor-Precategory =
    is-section-map-inv-equiv equiv-eq-map-eq-functor-Precategory

  is-retraction-eq-eq-map-functor-Precategory :
    eq-eq-map-functor-Precategory ∘ eq-map-eq-functor-Precategory ~ id
  is-retraction-eq-eq-map-functor-Precategory =
    is-retraction-map-inv-equiv equiv-eq-map-eq-functor-Precategory
```

#### Equality of functors is homotopy of underlying maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F G : functor-Precategory C D)
  where

  htpy-functor-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-functor-Precategory =
    htpy-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)

  equiv-htpy-eq-functor-Precategory : (F ＝ G) ≃ htpy-functor-Precategory
  equiv-htpy-eq-functor-Precategory =
    ( equiv-htpy-eq-map-Precategory C D
      ( map-functor-Precategory C D F)
      ( map-functor-Precategory C D G)) ∘e
    ( equiv-eq-map-eq-functor-Precategory C D F G)

  htpy-eq-functor-Precategory : F ＝ G → htpy-functor-Precategory
  htpy-eq-functor-Precategory =
    map-equiv equiv-htpy-eq-functor-Precategory

  eq-htpy-functor-Precategory : htpy-functor-Precategory → F ＝ G
  eq-htpy-functor-Precategory =
    map-inv-equiv equiv-htpy-eq-functor-Precategory

  is-section-eq-htpy-functor-Precategory :
    htpy-eq-functor-Precategory ∘ eq-htpy-functor-Precategory ~ id
  is-section-eq-htpy-functor-Precategory =
    is-section-map-inv-equiv equiv-htpy-eq-functor-Precategory

  is-retraction-eq-htpy-functor-Precategory :
    eq-htpy-functor-Precategory ∘ htpy-eq-functor-Precategory ~ id
  is-retraction-eq-htpy-functor-Precategory =
    is-retraction-map-inv-equiv equiv-htpy-eq-functor-Precategory
```

### Functors preserve isomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  {x y : obj-Precategory C}
  where

  hom-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    is-iso-Precategory C f →
    hom-Precategory D
      ( obj-functor-Precategory C D F y)
      ( obj-functor-Precategory C D F x)
  hom-inv-preserves-is-iso-functor-Precategory f is-iso-f =
    hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f)

  is-right-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    (is-iso-f : is-iso-Precategory C f) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F f)
      ( hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f)) ＝
    id-hom-Precategory D
  is-right-inv-preserves-is-iso-functor-Precategory f is-iso-f =
    ( inv
      ( preserves-comp-functor-Precategory C D F
        ( f)
        ( hom-inv-is-iso-Precategory C is-iso-f))) ∙
    ( ap
      ( hom-functor-Precategory C D F)
      ( is-section-hom-inv-is-iso-Precategory C is-iso-f)) ∙
    ( preserves-id-functor-Precategory C D F y)

  is-left-inv-preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    (is-iso-f : is-iso-Precategory C f) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F (hom-inv-is-iso-Precategory C is-iso-f))
      ( hom-functor-Precategory C D F f) ＝
    id-hom-Precategory D
  is-left-inv-preserves-is-iso-functor-Precategory f is-iso-f =
    ( inv
      ( preserves-comp-functor-Precategory C D F
        ( hom-inv-is-iso-Precategory C is-iso-f)
        ( f))) ∙
    ( ap
      ( hom-functor-Precategory C D F)
      ( is-retraction-hom-inv-is-iso-Precategory C is-iso-f)) ∙
    ( preserves-id-functor-Precategory C D F x)

  preserves-is-iso-functor-Precategory :
    (f : hom-Precategory C x y) →
    is-iso-Precategory C f →
    is-iso-Precategory D (hom-functor-Precategory C D F f)
  pr1 (preserves-is-iso-functor-Precategory f is-iso-f) =
    hom-inv-preserves-is-iso-functor-Precategory f is-iso-f
  pr1 (pr2 (preserves-is-iso-functor-Precategory f is-iso-f)) =
    is-right-inv-preserves-is-iso-functor-Precategory f is-iso-f
  pr2 (pr2 (preserves-is-iso-functor-Precategory f is-iso-f)) =
    is-left-inv-preserves-is-iso-functor-Precategory f is-iso-f

  preserves-iso-functor-Precategory :
    iso-Precategory C x y →
    iso-Precategory D
      ( obj-functor-Precategory C D F x)
      ( obj-functor-Precategory C D F y)
  pr1 (preserves-iso-functor-Precategory f) =
    hom-functor-Precategory C D F (hom-iso-Precategory C f)
  pr2 (preserves-iso-functor-Precategory f) =
    preserves-is-iso-functor-Precategory
      ( hom-iso-Precategory C f)
      ( is-iso-iso-Precategory C f)
```

### Functors induce functors on the opposite precategories

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  opposite-functor-Precategory :
    functor-Precategory (opposite-Precategory C) (opposite-Precategory D)
  pr1 opposite-functor-Precategory = obj-functor-Precategory C D F
  pr1 (pr2 opposite-functor-Precategory) = hom-functor-Precategory C D F
  pr1 (pr2 (pr2 opposite-functor-Precategory)) g f =
    preserves-comp-functor-Precategory C D F f g
  pr2 (pr2 (pr2 opposite-functor-Precategory)) =
    preserves-id-functor-Precategory C D F
```

### Categorical laws for functor composition

#### Unit laws for functor composition

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  left-unit-law-comp-functor-Precategory :
    comp-functor-Precategory C D D (id-functor-Precategory D) F ＝ F
  left-unit-law-comp-functor-Precategory =
    eq-eq-map-functor-Precategory C D _ _ refl

  right-unit-law-comp-functor-Precategory :
    comp-functor-Precategory C C D F (id-functor-Precategory C) ＝ F
  right-unit-law-comp-functor-Precategory = refl
```

#### Associativity of functor composition

```agda
module _
  {l1 l1' l2 l2' l3 l3' l4 l4' : Level}
  (A : Precategory l1 l1')
  (B : Precategory l2 l2')
  (C : Precategory l3 l3')
  (D : Precategory l4 l4')
  (F : functor-Precategory A B)
  (G : functor-Precategory B C)
  (H : functor-Precategory C D)
  where

  associative-comp-functor-Precategory :
    comp-functor-Precategory A B D (comp-functor-Precategory B C D H G) F ＝
    comp-functor-Precategory A C D H (comp-functor-Precategory A B C G F)
  associative-comp-functor-Precategory =
    eq-eq-map-functor-Precategory A D _ _ refl
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
  (A : Precategory l1 l1')
  (B : Precategory l2 l2')
  (C : Precategory l3 l3')
  (D : Precategory l4 l4')
  (E : Precategory l4 l4')
  (F : functor-Precategory A B)
  (G : functor-Precategory B C)
  (H : functor-Precategory C D)
  (I : functor-Precategory D E)
  where

  mac-lane-pentagon-comp-functor-Precategory :
    coherence-pentagon-identifications
      { x =
        comp-functor-Precategory A B E
        ( comp-functor-Precategory B D E I
          ( comp-functor-Precategory B C D H G))
        ( F)}
      { comp-functor-Precategory A D E I
        ( comp-functor-Precategory A B D
          ( comp-functor-Precategory B C D H G)
          ( F))}
      { comp-functor-Precategory A B E
        ( comp-functor-Precategory B C E
          ( comp-functor-Precategory C D E I H)
          ( G))
        ( F)}
      { comp-functor-Precategory A D E
        ( I)
        ( comp-functor-Precategory A C D
          ( H)
          ( comp-functor-Precategory A B C G F))}
      { comp-functor-Precategory A C E
        ( comp-functor-Precategory C D E I H)
        ( comp-functor-Precategory A B C G F)}
      ( associative-comp-functor-Precategory A B D E
        ( F) (comp-functor-Precategory B C D H G) (I))
      ( ap
        ( λ p → comp-functor-Precategory A B E p F)
        ( inv (associative-comp-functor-Precategory B C D E G H I)))
      ( ap
        ( λ p → comp-functor-Precategory A D E I p)
        ( associative-comp-functor-Precategory A B C D F G H))
      ( associative-comp-functor-Precategory A B C E
        ( F) (G) (comp-functor-Precategory C D E I H))
      ( inv
        ( associative-comp-functor-Precategory A C D E
          (comp-functor-Precategory A B C G F) H I))
  mac-lane-pentagon-comp-functor-Precategory = {!!}
```

## See also

- [The precategory of functors and natural transformations between precategories](category-theory.precategory-of-functors.md)

## References

{{#bibliography}} {{#reference UF13}} {{#reference AKS15}}

## External links

- [Functors](https://1lab.dev/Cat.Base.html#functors) at 1lab
