# Functoriality of coproduct types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.functoriality-coproduct-types where

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.dependent-pair-types using (pair; pr1; pr2)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_; inv-htpy; _∙h_)
open import foundation.identity-types using (refl; ap)
open import foundation.universe-levels using (Level; UU)
```

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map `map-coprod f g : coprod A B → coprod C D`.

## Definition

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  where
  
  map-coprod : (A → A') → (B → B') → coprod A B → coprod A' B'
  map-coprod f g (inl x) = inl (f x)
  map-coprod f g (inr y) = inr (g y)
```

## Properties

### Functoriality of coproducts preserves identity maps

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  id-map-coprod : (map-coprod (id {A = A}) (id {A = B})) ~ id
  id-map-coprod (inl x) = refl
  id-map-coprod (inr x) = refl
```

### Functoriality of coproducts preserves composition

```agda
module _
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'')
  where
  
  compose-map-coprod :
    (map-coprod (f' ∘ f) (g' ∘ g)) ~ ((map-coprod f' g') ∘ (map-coprod f g))
  compose-map-coprod (inl x) = refl
  compose-map-coprod (inr y) = refl
```

### Functoriality of coproducts preserves homotopies

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g')
  where
  
  htpy-map-coprod : (map-coprod f g) ~ (map-coprod f' g')
  htpy-map-coprod (inl x) = ap inl (H x)
  htpy-map-coprod (inr y) = ap inr (K y)
```

### Functoriality of coproducts preserves equivalences

```agda
module _
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f : A → A'} {g : B → B'}
  where

  abstract
    is-equiv-map-coprod : is-equiv f → is-equiv g → is-equiv (map-coprod f g)
    pr1
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod sf sg
    pr2
      ( pr1
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
        ( htpy-map-coprod Sf Sg)) ∙h
      ( id-map-coprod A' B')
    pr1
      ( pr2
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-coprod rf rg
    pr2
      ( pr2
        ( is-equiv-map-coprod
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
        ( htpy-map-coprod Rf Rg)) ∙h
      ( id-map-coprod A B)
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → (coprod A B) ≃ (coprod A' B')
pr1 (equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f)) = map-coprod e f
pr2 (equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f)) =
  is-equiv-map-coprod is-equiv-e is-equiv-f
```
