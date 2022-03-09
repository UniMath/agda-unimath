# Monomorphisms in large precategories

```agda
{-# OPTIONS --without-K --exact-split #-}

module categories.monomorphisms-large-precategories where

open import categories.large-precategories using
  ( Large-Precat; obj-Large-Precat; type-hom-Large-Precat;
    comp-Large-Precat)
open import foundation.embeddings using (is-emb-Prop)
open import foundation.propositions using
  ( UU-Prop; Π-Prop; type-Prop; is-prop; is-prop-type-Prop)
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
    Π-Prop (obj-Large-Precat C l3) (λ Z → is-emb-Prop (comp-Large-Precat C {X = Z} f))

  is-mono-Large-Precat : UU (α l3 ⊔ β l3 l1 ⊔ β l3 l2)
  is-mono-Large-Precat = type-Prop is-mono-Large-Precat-Prop

  is-prop-is-mono-Large-Precat : is-prop is-mono-Large-Precat
  is-prop-is-mono-Large-Precat = is-prop-type-Prop is-mono-Large-Precat-Prop
```
