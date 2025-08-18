# Postcomposition of functions

```agda
module foundation.postcomposition-functions where

open import foundation-core.postcomposition-functions public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.postcomposition-dependent-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
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
```

</details>

## Idea

Given a map `f : X → Y` and a type `A`, the
{{#concept "postcomposition function"}}

```text
  f ∘ - : (A → X) → (A → Y)
```

is defined by `λ h x → f (h x)`.

## Properties

### Postcomposition preserves homotopies

```agda
htpy-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  {f g : X → Y} → (f ~ g) → postcomp A f ~ postcomp A g
htpy-postcomp A H h = eq-htpy (H ·r h)

compute-htpy-postcomp-refl-htpy :
  {l1 l2 l3 : Level} (A : UU l1) {B : UU l2} {C : UU l3} (f : B → C) →
  (htpy-postcomp A (refl-htpy' f)) ~ refl-htpy
compute-htpy-postcomp-refl-htpy A f h = eq-htpy-refl-htpy (f ∘ h)
```

### Computations of the fibers of `postcomp`

We give three computations of the fibers of a postcomposition function:

1. `fiber (postcomp A f) h ≃ ((x : A) → fiber f (h x))`
2. `fiber (postcomp A f) h ≃ Σ (A → X) (coherence-triangle-maps h f)`, and
3. `fiber (postcomp A f) (f ∘ h) ≃ Σ (A → X) (λ g → coherence-square-maps g h f f)`

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3)
  (f : X → Y)
  where

  inv-compute-Π-fiber-postcomp :
    (h : A → Y) → fiber (postcomp A f) h ≃ ((x : A) → fiber f (h x))
  inv-compute-Π-fiber-postcomp h =
    inv-distributive-Π-Σ ∘e equiv-tot (λ _ → equiv-funext)

  compute-Π-fiber-postcomp :
    (h : A → Y) → ((x : A) → fiber f (h x)) ≃ fiber (postcomp A f) h
  compute-Π-fiber-postcomp h =
    equiv-tot (λ _ → equiv-eq-htpy) ∘e distributive-Π-Σ

  inv-compute-coherence-triangle-fiber-postcomp :
    (h : A → Y) →
    fiber (postcomp A f) h ≃ Σ (A → X) (coherence-triangle-maps h f)
  inv-compute-coherence-triangle-fiber-postcomp h =
    equiv-tot (λ _ → equiv-funext) ∘e equiv-fiber (postcomp A f) h

  compute-coherence-triangle-fiber-postcomp :
    (h : A → Y) →
    Σ (A → X) (coherence-triangle-maps h f) ≃ fiber (postcomp A f) h
  compute-coherence-triangle-fiber-postcomp h =
    inv-equiv (inv-compute-coherence-triangle-fiber-postcomp h)

  inv-compute-fiber-postcomp :
    (h : A → X) →
    fiber (postcomp A f) (f ∘ h) ≃
    Σ (A → X) (λ g → coherence-square-maps g h f f)
  inv-compute-fiber-postcomp h =
    inv-compute-coherence-triangle-fiber-postcomp (f ∘ h)

  compute-fiber-postcomp :
    (h : A → X) →
    Σ (A → X) (λ g → coherence-square-maps g h f f) ≃
    fiber (postcomp A f) (f ∘ h)
  compute-fiber-postcomp h = compute-coherence-triangle-fiber-postcomp (f ∘ h)
```

### Computing the fiber of the postcomposition function at the identity function

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  (f : X → Y)
  where

  compute-fiber-id-postcomp :
    ((x : Y) → fiber f x) ≃ fiber (postcomp Y f) id
  compute-fiber-id-postcomp = compute-Π-fiber-postcomp Y f id

  inv-compute-fiber-id-postcomp :
    fiber (postcomp Y f) id ≃ ((x : Y) → fiber f x)
  inv-compute-fiber-id-postcomp = inv-compute-Π-fiber-postcomp Y f id
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
              ( map-inv-is-equiv-is-equiv-postcomp ∘ f) ,
              ( ap (_∘ f) (is-section-map-inv-is-equiv (H Y) id))}
          { y = id , refl}))

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
is-equiv-is-equiv-postcomp' {l} {X} {Y} f is-equiv-postcomp-f =
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
          ( pr1 section-f ∘ f , ap (_∘ f) (pr2 section-f))
          ( id , refl))))

is-equiv-postcomp-is-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
  {l3 : Level} (A : UU l3) → is-equiv (postcomp A f)
is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
  is-equiv-is-invertible
    ( postcomp A (map-inv-is-equiv is-equiv-f))
    ( eq-htpy ∘
      right-whisker-comp (is-section-map-inv-is-equiv is-equiv-f))
    ( eq-htpy ∘
      right-whisker-comp (is-retraction-map-inv-is-equiv is-equiv-f))

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
    equiv-Π-equiv-family (λ a → equiv-ap e (f a) (g a))
```

### Computing the action on identifications of postcomposition by a map

Consider a map `f : B → C` and two functions `g h : A → B`. Then the
[action on identifications](foundation.action-on-identifications-functions.md)
`ap (postcomp A f)` fits in a
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                    ap (postcomp A f)
       (g = h) --------------------------> (f ∘ g = f ∘ h)
          |                                       |
  htpy-eq |                                       | htpy-eq
          ∨                                       ∨
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h).
                          f ·l_
```

Similarly, the action on identifications `ap (postcomp A f)` also fits in a
commuting square

```text
                          f ·l_
       (g ~ h) --------------------------> (f ∘ g ~ f ∘ h)
          |                                       |
  eq-htpy |                                       | eq-htpy
          ∨                                       ∨
       (g = h) --------------------------> (f ∘ g = f ∘ h).
                     ap (postcomp A f)
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g h : A → B} (f : B → C)
  where

  compute-htpy-eq-ap-postcomp :
    coherence-square-maps
      ( ap (postcomp A f) {x = g} {y = h})
      ( htpy-eq)
      ( htpy-eq)
      ( f ·l_)
  compute-htpy-eq-ap-postcomp =
    compute-htpy-eq-ap-postcomp-Π f

  compute-eq-htpy-ap-postcomp :
    coherence-square-maps
      ( f ·l_)
      ( eq-htpy)
      ( eq-htpy)
      ( ap (postcomp A f) {x = g} {y = h})
  compute-eq-htpy-ap-postcomp =
    compute-eq-htpy-ap-postcomp-Π f
```
