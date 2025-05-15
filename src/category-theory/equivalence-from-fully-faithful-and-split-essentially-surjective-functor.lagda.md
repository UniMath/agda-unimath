# File title

```agda
module category-theory.equivalence-from-fully-faithful-and-split-essentially-surjective-functor where
```

<details><summary>Imports</summary>

```agda
open import category-theory.equivalences-of-precategories
open import category-theory.fully-faithful-functors-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.split-essentially-surjective-functors-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

A functor `F : C → D` that is fully faithful (it induces equivalences
`φ : C(c₁, c₂) ≃ D(F(c₁), F(c₂))` on homsets) and essentially surjective (for
every `x : D`, we have some `G(x) : C` and an isomorphism `εₓ : F(G(x)) ≅ x`) is
an equivalence of categories. The construction proceeds along the following
lines:

- The inverse functor `G` sends objects `x : D` to `G(x) : C`;
- Morpisms `f: D(x₁, x₂)` are sent to `φ⁻¹(εₓ₂⁻¹ ∘ f ∘ εₓ₁) : C(G(x₁), G(x₂))`;
- The unit is given on `c : C` by the preimage along `φ` of `ε` at `F(c)`;
- The counit is given on `x : D` by `εₓ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (C D : Precategory l1 l2)
  (F : functor-Precategory C D)
  (HFF : is-fully-faithful-functor-Precategory C D F)
  (HES : is-split-essentially-surjective-functor-Precategory C D F)
  where

  private
    infixl 10 _∘C_

    _∘C_ : {x y z : obj-Precategory C}
      → hom-Precategory C y z
      → hom-Precategory C x y
      → hom-Precategory C x z
    _∘C_ f g = comp-hom-Precategory C f g

    infixl 10 _∘D_
    _∘D_ : {x y z : obj-Precategory D}
      → hom-Precategory D y z
      → hom-Precategory D x y
      → hom-Precategory D x z
    _∘D_ f g = comp-hom-Precategory D f g

    F₀ : obj-Precategory C → obj-Precategory D
    F₀ = obj-functor-Precategory C D F

    F₁ : {x y : obj-Precategory C}
      → hom-Precategory C x y
      → hom-Precategory D (F₀ x) (F₀ y)
    F₁ = hom-functor-Precategory C D F

    F₁⁻¹ : {x y : obj-Precategory C}
      → hom-Precategory D (F₀ x) (F₀ y)
      → hom-Precategory C x y
    F₁⁻¹ = map-inv-hom-is-fully-faithful-functor-Precategory C D F HFF

    G : obj-Precategory D → obj-Precategory C
    G d = pr1 (HES d)

    ε :
      (d : obj-Precategory D)
      → iso-Precategory D (F₀ (G d)) d
    ε d = pr2 (HES d)

  obj-functor-ff-es-equiv : obj-Precategory D → obj-Precategory C
  obj-functor-ff-es-equiv = G

  hom-functor-ff-es-equiv :
    {x y : obj-Precategory D}
    → hom-Precategory D x y
    → hom-Precategory C (obj-functor-ff-es-equiv x) (obj-functor-ff-es-equiv y)
  hom-functor-ff-es-equiv {x} {y} f =
    F₁⁻¹ (hom-inv-iso-Precategory D (ε y) ∘D f ∘D hom-iso-Precategory D (ε x))

  map-functor-ff-es-equiv : map-Precategory D C
  pr1 map-functor-ff-es-equiv = obj-functor-ff-es-equiv
  pr2 map-functor-ff-es-equiv = hom-functor-ff-es-equiv

  opaque
    preserves-comp-hom-functor-ff-es-equiv :
      preserves-comp-hom-map-Precategory D C map-functor-ff-es-equiv
    preserves-comp-hom-functor-ff-es-equiv {x} {y} {z} g f = inv (
        fully-faithful-inv-preserves-comp C D F HFF _ _
        ∙ ap F₁⁻¹ (
          associative-comp-hom-Precategory D _ _ _
          ∙ ap (λ a → _ ∘D _ ∘D a)
              (inv (associative-comp-hom-Precategory D _ _ _))
          ∙ ap (λ a → _ ∘D _ ∘D (a ∘D _))
              (inv (associative-comp-hom-Precategory D _ _ _))
          ∙ ap (λ a → _ ∘D _ ∘D (a ∘D _ ∘D _))
              (is-section-hom-inv-iso-Precategory D (ε y))
          ∙ ap (λ a → _ ∘D (a ∘D _))
              (left-unit-law-comp-hom-Precategory D _)
          ∙ associative-comp-hom-Precategory D _ g _
          ∙ ap (λ a → _ ∘D a)
              (inv (associative-comp-hom-Precategory D _ _ _))
          ∙ inv (associative-comp-hom-Precategory D _ _ _)
      ))

    preserves-id-hom-functor-ff-es-equiv :
      preserves-id-hom-map-Precategory D C map-functor-ff-es-equiv
    preserves-id-hom-functor-ff-es-equiv x =
      ap F₁⁻¹ (
        ap (λ a → a ∘D _) (right-unit-law-comp-hom-Precategory D _)
        ∙ is-retraction-hom-inv-iso-Precategory D (ε x)
      ) ∙ inv (fully-faithful-inv-preserves-id C D F HFF _)

  functor-ff-es-equiv : functor-Precategory D C
  pr1 functor-ff-es-equiv = obj-functor-ff-es-equiv
  pr1 (pr2 functor-ff-es-equiv) = hom-functor-ff-es-equiv
  pr1 (pr2 (pr2 functor-ff-es-equiv)) = preserves-comp-hom-functor-ff-es-equiv
  pr2 (pr2 (pr2 functor-ff-es-equiv)) = preserves-id-hom-functor-ff-es-equiv

  module _
    (x : obj-Precategory C)
    where

    iso-unit-ff-es-equiv :
      iso-Precategory C
        (obj-functor-Precategory C C
          (comp-functor-Precategory C D C functor-ff-es-equiv F) x)
        x
    iso-unit-ff-es-equiv =
      (is-essentially-injective-is-fully-faithful-functor-Precategory
        C D F HFF _ _ (ε (F₀ x)))

    hom-unit-ff-es-equiv :
      hom-Precategory C
        (obj-functor-Precategory C C
          (comp-functor-Precategory C D C functor-ff-es-equiv F) x)
        x
    hom-unit-ff-es-equiv = hom-iso-Precategory C iso-unit-ff-es-equiv

    is-iso-unit-ff-es-equiv : is-iso-Precategory C hom-unit-ff-es-equiv
    is-iso-unit-ff-es-equiv = is-iso-iso-Precategory C iso-unit-ff-es-equiv

  opaque
    is-natural-unit-ff-es-equiv :
      is-natural-transformation-Precategory C C
        (comp-functor-Precategory C D C functor-ff-es-equiv F)
        (id-functor-Precategory C)
        hom-unit-ff-es-equiv
    is-natural-unit-ff-es-equiv {x} {y} f = equational-reasoning
        f ∘C hom-unit-ff-es-equiv x
      ＝ F₁⁻¹ (F₁ f) ∘C hom-unit-ff-es-equiv x
        by ap (λ a → a ∘C _)
          (inv (is-retraction-map-section-is-equiv (HFF _ _) f))
      ＝ F₁⁻¹ (F₁ f ∘D (hom-iso-Precategory D (ε (F₀ x))))
        by fully-faithful-inv-preserves-comp C D F HFF _ _
      ＝ F₁⁻¹ (
          (id-hom-Precategory D)
          ∘D (F₁ f)
          ∘D (hom-iso-Precategory D (ε (F₀ x))))
        by ap (λ a → F₁⁻¹ (a ∘D _))
          (inv (left-unit-law-comp-hom-Precategory D _))
      ＝ F₁⁻¹ (
          (hom-iso-Precategory D (ε (F₀ y)))
          ∘D (hom-inv-iso-Precategory D (ε (F₀ y)))
          ∘D (F₁ f)
          ∘D (hom-iso-Precategory D (ε (F₀ x))))
        by ap (λ a → F₁⁻¹ (a ∘D _ ∘D _))
          (inv (is-section-hom-inv-iso-Precategory D (ε (F₀ y))))
      ＝ F₁⁻¹ (
          (hom-iso-Precategory D (ε (F₀ y)))
          ∘D (
            (hom-inv-iso-Precategory D (ε (F₀ y)))
            ∘D (F₁ f)
            ∘D (hom-iso-Precategory D (ε (F₀ x)))))
        by ap F₁⁻¹ (
          associative-comp-hom-Precategory D _ _ _
          ∙ associative-comp-hom-Precategory D _ _ _
          ∙ ap (λ a → _ ∘D a) (inv (associative-comp-hom-Precategory D _ _ _)))
      ＝ (hom-unit-ff-es-equiv y) ∘C (hom-functor-ff-es-equiv (F₁ f))
        by inv (fully-faithful-inv-preserves-comp C D F HFF _ _)

  unit-ff-es-equiv :
    natural-isomorphism-Precategory C C
      (comp-functor-Precategory C D C functor-ff-es-equiv F)
      (id-functor-Precategory C)
  pr1 (pr1 unit-ff-es-equiv) = hom-unit-ff-es-equiv
  pr2 (pr1 unit-ff-es-equiv) = is-natural-unit-ff-es-equiv
  pr2 unit-ff-es-equiv = is-iso-unit-ff-es-equiv

  hom-counit-ff-es-equiv :
    (d : obj-Precategory D)
    → hom-Precategory D
      (obj-functor-Precategory D D
        (comp-functor-Precategory D C D F functor-ff-es-equiv) d) d
  hom-counit-ff-es-equiv d = hom-iso-Precategory D (ε d)

  is-iso-counit-ff-es-equiv :
    (d : obj-Precategory D)
    → is-iso-Precategory D (hom-counit-ff-es-equiv d)
  is-iso-counit-ff-es-equiv d = is-iso-iso-Precategory D (ε d)

  opaque
    is-natural-counit-ff-es-equiv :
      is-natural-transformation-Precategory D D
        (comp-functor-Precategory D C D F functor-ff-es-equiv)
        (id-functor-Precategory D)
        hom-counit-ff-es-equiv
    is-natural-counit-ff-es-equiv {x} {y} f = equational-reasoning
      f ∘D (hom-counit-ff-es-equiv x)
      ＝ (id-hom-Precategory D) ∘D f ∘D (hom-counit-ff-es-equiv x)
        by ap (λ a → a ∘D _) (inv (left-unit-law-comp-hom-Precategory D f))
      ＝ (hom-iso-Precategory D (ε y))
          ∘D (hom-inv-iso-Precategory D (ε y))
          ∘D f
          ∘D (hom-counit-ff-es-equiv x)
        by ap (λ a → a ∘D _ ∘D _)
          (inv (is-section-hom-inv-iso-Precategory D (ε y)))
      ＝ (hom-iso-Precategory D (ε y))
          ∘D (
            (hom-inv-iso-Precategory D (ε y))
            ∘D f
            ∘D (hom-iso-Precategory D (ε x)))
        by associative-comp-hom-Precategory D _ _ _
          ∙ associative-comp-hom-Precategory D _ _ _
          ∙ ap (λ a → _ ∘D a) (inv (associative-comp-hom-Precategory D _ _ _))
      ＝ (hom-counit-ff-es-equiv y) ∘D (F₁ (hom-functor-ff-es-equiv f))
        by ap (λ a → _ ∘D a) (inv (is-section-map-section-is-equiv (HFF _ _) _))

  counit-ff-es-equiv :
    natural-isomorphism-Precategory D D
      (comp-functor-Precategory D C D F functor-ff-es-equiv)
      (id-functor-Precategory D)
  pr1 (pr1 counit-ff-es-equiv) = hom-counit-ff-es-equiv
  pr2 (pr1 counit-ff-es-equiv) = is-natural-counit-ff-es-equiv
  pr2 counit-ff-es-equiv = is-iso-counit-ff-es-equiv

  result : equiv-Precategory C D
  pr1 result = F
  pr1 (pr1 (pr2 result)) = functor-ff-es-equiv
  pr2 (pr1 (pr2 result)) = unit-ff-es-equiv
  pr1 (pr2 (pr2 result)) = functor-ff-es-equiv
  pr2 (pr2 (pr2 result)) = counit-ff-es-equiv
```
