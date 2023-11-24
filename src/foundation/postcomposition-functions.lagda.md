# Postcomposition

```agda
module foundation.postcomposition-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a map `f : X → Y` and a type `A`, the **postcomposition function**

```text
  f ∘ - : (A → X) → (A → Y)
```

is defined by `λ h → f ∘ h`.

## Definitions

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3)
  where

  postcomp : (X → Y) → (A → X) → (A → Y)
  postcomp f h = f ∘ h
```

## Properties

### Postcomposition preserves homotopies

```agda
htpy-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  {f g : X → Y} → (f ~ g) → postcomp A f ~ postcomp A g
htpy-postcomp A H h = eq-htpy (H ∘ h)

compute-htpy-postcomp-refl-htpy :
  {l1 l2 l3 : Level} (A : UU l1) {B : UU l2} {C : UU l3} (f : B → C) →
  (htpy-postcomp A (refl-htpy' f)) ~ refl-htpy
compute-htpy-postcomp-refl-htpy A f h = eq-htpy-refl-htpy (f ∘ h)
```

### The fibers of `postcomp`

```agda
compute-fiber-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (f : X → Y) (h : A → Y) →
  ((x : A) → fiber f (h x)) ≃ fiber (postcomp A f) h
compute-fiber-postcomp A f h =
  equiv-tot (λ _ → equiv-eq-htpy) ∘e distributive-Π-Σ
```

### Postcomposition and equivalences

#### A map `f` is an equivalence if and only if postcomposing by `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (H : {l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  where

  map-inv-is-equiv-is-equiv-postcomp : Y → X
  map-inv-is-equiv-is-equiv-postcomp = map-inv-is-equiv (H Y) id

  is-section-map-inv-is-equiv-is-equiv-postcomp :
    ( f ∘ map-inv-is-equiv-is-equiv-postcomp) ~ id
  is-section-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq (is-section-map-inv-is-equiv (H Y) id)

  is-retraction-map-inv-is-equiv-is-equiv-postcomp :
    ( map-inv-is-equiv-is-equiv-postcomp ∘ f) ~ id
  is-retraction-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr
          ( is-contr-map-is-equiv (H X) f)
          { x =
            pair
              ( map-inv-is-equiv-is-equiv-postcomp ∘ f)
              ( ap (λ u → u ∘ f) (is-section-map-inv-is-equiv (H Y) id))}
          { y = pair id refl}))

  abstract
    is-equiv-is-equiv-postcomp : is-equiv f
    is-equiv-is-equiv-postcomp =
      is-equiv-is-invertible
        map-inv-is-equiv-is-equiv-postcomp
        is-section-map-inv-is-equiv-is-equiv-postcomp
        is-retraction-map-inv-is-equiv-is-equiv-postcomp
```

The following version of the same theorem works when `X` and `Y` are in the same
universe. The condition of inducing equivalences by postcomposition is
simplified to that universe.

```agda
is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let section-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-is-invertible
    ( pr1 section-f)
    ( htpy-eq (pr2 section-f))
    ( htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
          ( pair ((pr1 section-f) ∘ f) (ap (λ t → t ∘ f) (pr2 section-f)))
          ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    {l3 : Level} (A : UU l3) → is-equiv (postcomp A f)
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-is-invertible
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( eq-htpy ∘ htpy-right-whisk (is-section-map-inv-is-equiv is-equiv-f))
      ( eq-htpy ∘ htpy-right-whisk (is-retraction-map-inv-is-equiv is-equiv-f))

  is-equiv-postcomp-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X ≃ Y) →
    {l3 : Level} (A : UU l3) → is-equiv (postcomp A (map-equiv f))
  is-equiv-postcomp-equiv f =
    is-equiv-postcomp-is-equiv (map-equiv f) (is-equiv-map-equiv f)

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A
```

### Two maps being homotopic is equivalent to them being homotopic after pre- or postcomposition by an equivalence

```agda
module _
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-htpy-postcomp-htpy :
    (e : B ≃ C) (f g : A → B) → (f ~ g) ≃ (map-equiv e ∘ f ~ map-equiv e ∘ g)
  equiv-htpy-postcomp-htpy e f g =
    equiv-Π-equiv-family
      ( λ a → equiv-ap e (f a) (g a))
```
