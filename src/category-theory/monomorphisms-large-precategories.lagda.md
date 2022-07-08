---
title: Monomorphisms in large precategories
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module category-theory.monomorphisms-large-precategories where

open import category-theory.isomorphisms-large-precategories using
  ( iso-Large-Precat; hom-iso-Large-Precat; is-retr-hom-inv-iso-Large-Precat;
    hom-inv-iso-Large-Precat)
open import category-theory.large-precategories using
  ( Large-Precat; obj-Large-Precat; type-hom-Large-Precat;
    comp-hom-Large-Precat; left-unit-law-comp-hom-Large-Precat;
    associative-comp-hom-Large-Precat; is-set-type-hom-Large-Precat)

open import foundation.embeddings using (is-emb-Prop)
open import foundation.equivalences using (is-equiv-has-inverse)
open import foundation.identity-types using (refl; _∙_; ap; inv)
open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop; eq-is-prop)
open import foundation.universe-levels using (UU; Level; _⊔_)
```

## Idea

A morphism `f : x → y` is a monomorphism if whenever we have two morphisms `g h : w → x` such that `f ∘ g = f ∘ h`, then in fact `g = h`. The way to state this in Homotopy Type Theory is to say that postcomposition by `f` is an embedding.

## Definition

```agda
module _ {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  (f : type-hom-Large-Precat C X Y) where

  is-mono-Large-Precat-Prop : UU-Prop (α l3 ⊔ β l3 l1 ⊔ β l3 l2)
  is-mono-Large-Precat-Prop =
    Π-Prop
      ( obj-Large-Precat C l3)
      ( λ Z → is-emb-Prop (comp-hom-Large-Precat C {X = Z} f))

  is-mono-Large-Precat : UU (α l3 ⊔ β l3 l1 ⊔ β l3 l2)
  is-mono-Large-Precat = type-Prop is-mono-Large-Precat-Prop

  is-prop-is-mono-Large-Precat : is-prop is-mono-Large-Precat
  is-prop-is-mono-Large-Precat = is-prop-type-Prop is-mono-Large-Precat-Prop
```

## Properties

### Isomorphisms are monomorphisms

```agda
module _ {α : Level → Level} {β : Level → Level → Level}
  (C : Large-Precat α β) {l1 l2 : Level} (l3 : Level)
  (X : obj-Large-Precat C l1) (Y : obj-Large-Precat C l2)
  (f : iso-Large-Precat C X Y) where

  is-mono-iso-Large-Precat :
    is-mono-Large-Precat C l3 X Y (hom-iso-Large-Precat C X Y f)
  is-mono-iso-Large-Precat Z g h =
    is-equiv-has-inverse
      ( λ P →
        ( inv
          ( left-unit-law-comp-hom-Large-Precat C g)) ∙
          ( ( ap
            ( λ h' → comp-hom-Large-Precat C h' g)
            ( inv (is-retr-hom-inv-iso-Large-Precat C X Y f))) ∙
            ( ( associative-comp-hom-Large-Precat C
              ( hom-inv-iso-Large-Precat C X Y f)
              ( hom-iso-Large-Precat C X Y f)
              ( g)) ∙
              ( ( ap
                ( comp-hom-Large-Precat C (hom-inv-iso-Large-Precat C X Y f))
                ( P)) ∙
                ( ( inv
                  ( associative-comp-hom-Large-Precat C
                    ( hom-inv-iso-Large-Precat C X Y f)
                    ( hom-iso-Large-Precat C X Y f)
                    ( h))) ∙
                  ( ( ap
                    ( λ h' → comp-hom-Large-Precat C h' h)
                    ( is-retr-hom-inv-iso-Large-Precat C X Y f)) ∙
                    ( left-unit-law-comp-hom-Large-Precat C h)))))))
      ( λ p →
        eq-is-prop
          ( is-set-type-hom-Large-Precat C Z Y
            ( comp-hom-Large-Precat C (hom-iso-Large-Precat C X Y f) g)
            ( comp-hom-Large-Precat C (hom-iso-Large-Precat C X Y f) h)))
      ( λ p → eq-is-prop (is-set-type-hom-Large-Precat C Z X g h))
```
