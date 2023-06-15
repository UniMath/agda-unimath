# Epimorphism in large precategories

```agda
module category-theory.epimorphisms-large-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories
open import category-theory.large-precategories

open import foundation.action-on-identifications-functions
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A morphism `f : x → y` is a epimorphism if whenever we have two morphisms
`g h : y → w` such that `g ∘ f = h ∘ f`, then in fact `g = h`. The way to state
this in Homotopy Type Theory is to say that precomposition by `f` is an
embedding.

## Definition

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  (f : type-hom-Large-Precategory C X Y)
  where

  is-epi-Large-Precategory-Prop : Prop (α l3 ⊔ β l1 l3 ⊔ β l2 l3)
  is-epi-Large-Precategory-Prop =
    Π-Prop
      ( obj-Large-Precategory C l3)
      ( λ Z → is-emb-Prop (λ g → comp-hom-Large-Precategory C {Z = Z} g f))

  is-epi-Large-Precategory : UU (α l3 ⊔ β l1 l3 ⊔ β l2 l3)
  is-epi-Large-Precategory = type-Prop is-epi-Large-Precategory-Prop

  is-prop-is-epi-Large-Precategory : is-prop is-epi-Large-Precategory
  is-prop-is-epi-Large-Precategory =
    is-prop-type-Prop is-epi-Large-Precategory-Prop
```

## Properties

### Isomorphisms are epimorphisms

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precategory α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precategory C l1) (Y : obj-Large-Precategory C l2)
  (f : iso-Large-Precategory C X Y)
  where

  is-epi-iso-Large-Precategory :
    is-epi-Large-Precategory C l3 X Y (hom-iso-Large-Precategory C X Y f)
  is-epi-iso-Large-Precategory Z g h =
    is-equiv-has-inverse
      ( λ P →
        ( inv
          ( right-unit-law-comp-hom-Large-Precategory C g)) ∙
          ( ( ap
            ( λ h' → comp-hom-Large-Precategory C g h')
            ( inv (is-section-hom-inv-iso-Large-Precategory C X Y f))) ∙
            ( ( inv
              ( associative-comp-hom-Large-Precategory C
                ( g)
                ( hom-iso-Large-Precategory C X Y f)
                ( hom-inv-iso-Large-Precategory C X Y f))) ∙
              ( ( ap
                ( λ h' →
                  comp-hom-Large-Precategory
                    ( C)
                    ( h')
                    ( hom-inv-iso-Large-Precategory C X Y f))
                ( P)) ∙
                ( ( associative-comp-hom-Large-Precategory C
                  ( h)
                  ( hom-iso-Large-Precategory C X Y f)
                  ( hom-inv-iso-Large-Precategory C X Y f)) ∙
                  ( ( ap
                    ( comp-hom-Large-Precategory C h)
                    ( is-section-hom-inv-iso-Large-Precategory C X Y f)) ∙
                    ( right-unit-law-comp-hom-Large-Precategory C h)))))))
      ( λ p →
        eq-is-prop
          ( is-set-type-hom-Large-Precategory C X Z
            ( comp-hom-Large-Precategory C g
              ( hom-iso-Large-Precategory C X Y f))
            ( comp-hom-Large-Precategory C h
              ( hom-iso-Large-Precategory C X Y f))))
      ( λ p → eq-is-prop (is-set-type-hom-Large-Precategory C Y Z g h))
```
