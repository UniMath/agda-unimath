# Functoriality of function types

```agda
module foundation-core.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.path-split-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.transport
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Properties

### Postcomposition preserves homotopies

```agda
htpy-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (f g : X → Y) → (f ~ g) → postcomp A f ~ postcomp A g
htpy-postcomp A f g H h = eq-htpy (λ x → H (h x))
```

### The fibers of `postcomp`

```agda
compute-fib-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (f : X → Y) (h : A → Y) →
  ((x : A) → fib f (h x)) ≃ fib (postcomp A f) h
compute-fib-postcomp A f h =
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
      is-equiv-has-inverse
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
  is-equiv-has-inverse
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
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( λ g →
        eq-htpy
          ( htpy-right-whisk (is-section-map-inv-is-equiv is-equiv-f) g))
      ( λ h →
        eq-htpy
          ( htpy-right-whisk (is-retraction-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A
```

### Precomposition and equivalences

#### If dependent precomposition by `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)
```

#### If `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
pr1 (equiv-precomp e C) = precomp (map-equiv e) C
pr2 (equiv-precomp e C) =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C
```

#### If precomposing by `f` is an equivalence, then `f` is an equivalence

First, we prove this relative to a subuniverse, such that `f` is a map between
two types in that subuniverse.

```agda
module _
  { l1 l2 : Level}
  ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
  ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B)
  ( H : (l : Level) (C : Σ (UU l) (P l)) → is-equiv (precomp f (pr1 C)))
  where

  map-inv-is-equiv-precomp-subuniverse : pr1 B → pr1 A
  map-inv-is-equiv-precomp-subuniverse =
    pr1 (center (is-contr-map-is-equiv (H _ A) id))

  is-section-map-inv-is-equiv-precomp-subuniverse :
    ( f ∘ map-inv-is-equiv-precomp-subuniverse) ~ id
  is-section-map-inv-is-equiv-precomp-subuniverse =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr'
          ( is-contr-map-is-equiv (H _ B) f)
          ( ( f ∘ (pr1 (center (is-contr-map-is-equiv (H _ A) id)))) ,
            ( ap
              ( λ (g : pr1 A → pr1 A) → f ∘ g)
              ( pr2 (center (is-contr-map-is-equiv (H _ A) id)))))
          ( id , refl)))

  is-retraction-map-inv-is-equiv-precomp-subuniverse :
    ( map-inv-is-equiv-precomp-subuniverse ∘ f) ~ id
  is-retraction-map-inv-is-equiv-precomp-subuniverse =
    htpy-eq (pr2 (center (is-contr-map-is-equiv (H _ A) id)))

  abstract
    is-equiv-is-equiv-precomp-subuniverse :
      is-equiv f
    is-equiv-is-equiv-precomp-subuniverse =
      is-equiv-has-inverse
        ( map-inv-is-equiv-precomp-subuniverse)
        ( is-section-map-inv-is-equiv-precomp-subuniverse)
        ( is-retraction-map-inv-is-equiv-precomp-subuniverse)
```

Now we prove the usual statement, without the subuniverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-equiv-precomp :
      (f : A → B) → ((l : Level) (C : UU l) → is-equiv (precomp f C)) →
      is-equiv f
    is-equiv-is-equiv-precomp f is-equiv-precomp-f =
      is-equiv-is-equiv-precomp-subuniverse
        ( λ l → l1 ⊔ l2)
        ( λ l X → A → B)
        ( A , f)
        ( B , f)
        ( f)
        ( λ l C → is-equiv-precomp-f l (pr1 C))
```

```agda
is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : Truncated-Type l1 k) (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : Truncated-Type l k) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
