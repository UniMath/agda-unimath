---
title: Functoriality of function types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.functoriality-function-types where

open import foundation-core.coherently-invertible-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.path-split-maps
open import foundation-core.universe-levels
```

## Properties

### If `f` is coherently invertible, then precomposing by `f` is an equivalence

```agda
tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-coherently-invertible :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-coherently-invertible f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-coherently-invertible f
    ( pair g (pair issec-g (pair isretr-g coh))) C = 
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))
```

### If `f` is an equivalence, then precomposing by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-coherently-invertible f
      ( is-coherently-invertible-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C
```

### A map `f` is an equivalence if and only if postcomposing by `f` is an equivalence

```agda
abstract
  is-equiv-is-equiv-postcomp :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f)) → is-equiv f
  is-equiv-is-equiv-postcomp {X = X} {Y = Y} f post-comp-equiv-f =
    is-equiv-is-contr-map (λ g → {!!})
    {-
      ( is-trunc-map-is-trunc-map-postcomp neg-two-𝕋 f
        ( λ {l} A → is-contr-map-is-equiv (post-comp-equiv-f A)))-}

{- The following version of the same theorem works when X and Y are in the same
   universe. The condition of inducing equivalences by postcomposition is 
   simplified to that universe. -}

is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let sec-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-has-inverse
    ( pr1 sec-f)
    ( htpy-eq (pr2 sec-f))
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
             ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
             ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse 
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( λ g → eq-htpy (htpy-right-whisk (issec-map-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A
```
