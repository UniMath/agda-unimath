# Embeddings

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.embeddings where

open import foundation-core.embeddings public

open import foundation.commuting-squares using (coherence-square)
open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr-equiv; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; map-equiv; is-equiv-map-equiv;
    id-equiv; map-inv-equiv; inv-equiv; _∘e_;
    issec-map-inv-equiv; is-equiv-top-is-equiv-left-square;
    is-equiv-comp; is-equiv-right-factor; triangle-section;
    issec-map-inv-is-equiv; is-equiv-map-inv-is-equiv; is-equiv-left-factor;
    is-emb-is-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.foundation-base using ([sec])
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id-sec)
open import foundation.homotopies using
  ( _~_; _·l_; _·r_; _∙h_; nat-htpy; inv-htpy; refl-htpy)
open import foundation.identity-types using
  ( Id; refl; ap; inv; _∙_; concat'; assoc; concat; left-inv; right-unit;
    distributive-inv-concat; con-inv; inv-inv; ap-inv; ap-comp;
    is-equiv-concat; is-equiv-concat')
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Properties

### Embeddings are closed under homotopies

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where

  abstract
    is-emb-htpy : is-emb g → is-emb f
    is-emb-htpy is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( ap g)
        ( concat' (f x) (H y))
        ( ap f)
        ( concat (H x) (g y))
        ( nat-htpy H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where
  
  abstract
    is-emb-htpy' : is-emb f → is-emb g
    is-emb-htpy' is-emb-f =
      is-emb-htpy g f (inv-htpy H) is-emb-f
```

### Embeddings are closed under composition

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-comp :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb h → is-emb f
    is-emb-comp f g h H is-emb-g is-emb-h =
      is-emb-htpy f (g ∘ h) H
        ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
          ( is-emb-h x y)
          ( is-emb-g (h x) (h y)))

  abstract
    is-emb-comp' :
      (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
    is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

    comp-emb :
      (B ↪ C) → (A ↪ B) → (A ↪ C)
    pr1 (comp-emb (pair g H) (pair f K)) = g ∘ f
    pr2 (comp-emb (pair g H) (pair f K)) = is-emb-comp' g f H K
```

### The right factor of a composed embedding is an embedding

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-right-factor :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb f → is-emb h
    is-emb-right-factor f g h H is-emb-g is-emb-f x y =
      is-equiv-right-factor
        ( ap (g ∘ h))
        ( ap g)
        ( ap h)
        ( ap-comp g h)
        ( is-emb-g (h x) (h y))
        ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

  abstract
    is-emb-triangle-is-equiv :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-comp f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb f → is-emb g
    is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
      is-emb-triangle-is-equiv g f
        ( map-inv-is-equiv is-equiv-e)
        ( triangle-section f g e H
          ( pair
            ( map-inv-is-equiv is-equiv-e)
            ( issec-map-inv-is-equiv is-equiv-e)))
        ( is-equiv-map-inv-is-equiv is-equiv-e)
        ( is-emb-f)
```

### If the action on identifications has a section, then f is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-emb-sec-ap :
      ((x y : A) → [sec] (ap f {x = x} {y = y})) → is-emb f
    is-emb-sec-ap sec-ap-f x y =
      fundamental-theorem-id-sec x (λ y → ap f {y = y}) (sec-ap-f x) y
```
