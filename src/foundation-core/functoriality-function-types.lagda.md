# Functoriality of function types

```agda
module foundation-core.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.precomposition
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.whiskering-homotopies
```

</details>

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

### Any commuting triangle of maps induces a commuting triangle of function spaces

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  ( left : A → X) (right : B → X) (top : A → B)
  where

  precomp-coherence-triangle-maps :
    coherence-triangle-maps left right top →
    ( W : UU l4) →
    coherence-triangle-maps
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps H W = htpy-precomp H W

  precomp-coherence-triangle-maps' :
    coherence-triangle-maps' left right top →
    ( W : UU l4) →
    coherence-triangle-maps'
      ( precomp left W)
      ( precomp top W)
      ( precomp right W)
  precomp-coherence-triangle-maps' H W = htpy-precomp H W
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
