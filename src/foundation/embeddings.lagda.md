# Embeddings

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.embeddings where

open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( is-contr-equiv; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; equiv-inv; map-equiv; is-equiv-map-equiv;
    id-equiv; map-inv-equiv; inv-equiv; _∘e_; equiv-concat'; sec;
    issec-map-inv-equiv; is-equiv-top-is-equiv-left-square; is-equiv-concat;
    is-equiv-concat'; is-equiv-comp; is-equiv-right-factor; triangle-section;
    issec-map-inv-is-equiv; is-equiv-map-inv-is-equiv; is-equiv-left-factor)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (id; _∘_)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id-sec)
open import foundation.homotopies using
  ( _~_; coherence-square; _·l_; _·r_; _∙h_; htpy-nat; inv-htpy; refl-htpy)
open import foundation.identity-types using
  ( Id; refl; ap; inv; _∙_; concat'; assoc; concat; left-inv; right-unit;
    distributive-inv-concat; con-inv; inv-inv; ap-inv; ap-comp)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

An embedding from one type into another is a map that induces equivalences on identity types. In other words, the identitifications `Id (f x) (f y)` for an embedding `f : A → B` are in one-to-one correspondence with the identitifications `Id x y`. Embeddings are better behaved homotopically than injective maps, because the condition of being an equivalence is a property under function extensionality.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb f = pr1 f

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb f = pr2 f

  equiv-ap-emb : (e : A ↪ B) {x y : A} → Id x y ≃ Id (map-emb e x) (map-emb e y)
  pr1 (equiv-ap-emb e {x} {y}) = ap (map-emb e)
  pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y
```

## Examples

### Any equivalence is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-is-equiv : {f : A → B} → is-equiv f → is-emb f
  is-emb-is-equiv {f} is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → ap f p)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

  equiv-ap :
    (e : A ≃ B) (x y : A) → (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
  pr1 (equiv-ap e x y) = ap (map-equiv e) {x} {y}
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y
```

### The identity map is an embedding

```agda
module _
  {l : Level} {A : UU l}
  where

  id-emb : A ↪ A
  id-emb = emb-equiv id-equiv

  is-emb-id : is-emb (id {A = A})
  is-emb-id = is-emb-map-emb id-emb
```

### Transposing equalities along equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (Id (map-equiv e x) y) ≃ (Id x (map-inv-equiv e y))
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (issec-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → Id (map-equiv e x) y → Id x (map-inv-equiv e y)
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → Id x (map-inv-equiv e y) → Id (map-equiv e x) y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : Id (map-equiv e x) y) →
    Id ( ( ap (map-equiv e) (map-eq-transpose-equiv p)) ∙
         ( issec-map-inv-equiv e y))
       ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
         ( issec-map-inv-equiv
           ( equiv-ap e x (map-inv-equiv e y))
           ( p ∙ inv (issec-map-inv-equiv e y)))) ∙
    ( ( assoc p (inv (issec-map-inv-equiv e y)) (issec-map-inv-equiv e y)) ∙
      ( ( ap (concat p y) (left-inv (issec-map-inv-equiv e y))) ∙ right-unit))
  
  map-eq-transpose-equiv' :
    {a : A} {b : B} → Id b (map-equiv e a) → Id (map-inv-equiv e b) a
  map-eq-transpose-equiv' p = inv (map-eq-transpose-equiv (inv p))

  inv-map-eq-transpose-equiv' :
    {a : A} {b : B} → Id (map-inv-equiv e b) a → Id b (map-equiv e a)
  inv-map-eq-transpose-equiv' p =
    inv (inv-map-eq-transpose-equiv (inv p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : Id y (map-equiv e x)) →
    Id ( (issec-map-inv-equiv e y) ∙ p)
      ( ap (map-equiv e) (map-eq-transpose-equiv' p))
  triangle-eq-transpose-equiv' {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (issec-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv' p)))
      ( ( distributive-inv-concat (issec-map-inv-equiv e y) p) ∙
        ( ( inv
            ( con-inv
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv' p)))
              ( issec-map-inv-equiv e y)
              ( inv p)
              ( ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
                     ( ap ( ap (map-equiv e))
                          ( inv-inv
                            ( map-inv-equiv
                              ( equiv-ap e x (map-inv-equiv e y))
                              ( ( inv p) ∙
                                ( inv (issec-map-inv-equiv e y))))))) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv' p))))
```

## Composing and inverting squares horizontally and vertically

```agda
coherence-square-comp-horizontal :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top-left : A → B) (top-right : B → C)
  (left : A → X) (mid : B → Y) (right : C → Z)
  (bottom-left : X → Y) (bottom-right : Y → Z) →
  coherence-square top-left left mid bottom-left →
  coherence-square top-right mid right bottom-right →
  coherence-square
    (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
coherence-square-comp-horizontal
  top-left top-right left mid right bottom-left bottom-right sq-left sq-right =
  (bottom-right ·l sq-left) ∙h (sq-right ·r top-left)

coherence-square-inv-horizontal :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square (map-equiv top) left right (map-equiv bottom) →
  coherence-square (map-inv-equiv top) right left (map-inv-equiv bottom)
coherence-square-inv-horizontal top left right bottom H b =
  map-eq-transpose-equiv' bottom
    ( ( ap right (inv (issec-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

coherence-square-comp-vertical :
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X)
  (left-top : A → B) (right-top : X → Y)
  (mid : B → Y)
  (left-bottom : B → C) (right-bottom : Y → Z)
  (bottom : C → Z) →
  coherence-square top left-top right-top mid →
  coherence-square mid left-bottom right-bottom bottom →
  coherence-square
    top (left-bottom ∘ left-top) (right-bottom ∘ right-top) bottom
coherence-square-comp-vertical
  top left-top right-top mid left-bottom right-bottom bottom sq-top sq-bottom =
  (sq-bottom ·r left-top) ∙h (right-bottom ·l sq-top)

coherence-square-inv-vertical :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square top (map-equiv left) (map-equiv right) bottom →
  coherence-square bottom (map-inv-equiv left) (map-inv-equiv right) top
coherence-square-inv-vertical top left right bottom H x =
  map-eq-transpose-equiv right
    ( inv (H (map-inv-equiv left x)) ∙ ap bottom (issec-map-inv-equiv left x))
```

## Embeddings are closed under homotopies

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
        ( htpy-nat H)
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

## Composites of embeddings

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

## The right factor of a composed embedding is an embedding

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

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-emb-sec-ap :
      ((x y : A) → sec (ap f {x = x} {y = y})) → is-emb f
    is-emb-sec-ap sec-ap-f x y =
      fundamental-theorem-id-sec x (λ y → ap f {y = y}) (sec-ap-f x) y
```
