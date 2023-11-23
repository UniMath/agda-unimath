# Precomposition

```agda
module foundation.precomposition where

open import foundation-core.precomposition public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.constant-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.path-split-maps
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.transport-along-identifications
open import foundation-core.truncated-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a function `f : A → B` and a type family `X` over `B`, the
**precomposition function**

```text
  - ∘ f : ((y : B) → X b) → ((x : A) → X (f x))
```

is defined by `λ h x → h (f x)`. The precomposition function takes a simpler
form without dependent types: Given a type `X` the precomposition function by
`f`

```text
  - ∘ f : (B → X) → (A → X)
```

is given by `λ h x → h (f x)`.

## Properties

### All precomposition functions by f are equivalences if and only if `f` is an equivalence

#### For any map `f : A → B` and any family `C` over `B`, if `f` satisfies the property that `C b → (fiber f b → C b)` is an equivalence for every `b : B` then the precomposition function `((b : B) → C b) → ((a : A) → C (f a))` is an equivalence

This condition simplifies, for example, the proof that connected maps satisfy a
dependent universal property.

```agda
is-equiv-precomp-Π-fiber-condition :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} {C : B → UU l3} →
  ((b : B) → is-equiv (λ (c : C b) → const (fiber f b) (C b) c)) →
  is-equiv (precomp-Π f C)
is-equiv-precomp-Π-fiber-condition {f = f} {C} H =
  is-equiv-comp
    ( map-reduce-Π-fiber f (λ b u → C b))
    ( map-Π (λ b u t → u))
    ( is-equiv-map-Π-is-fiberwise-equiv H)
    ( is-equiv-map-reduce-Π-fiber f (λ b u → C b))
```

#### If `f` is coherently invertible, then precomposing by `f` is an equivalence

```agda
tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : x ＝ y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-coherently-invertible :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-coherently-invertible f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-coherently-invertible f
    ( g , is-section-g , is-retraction-g , coh) C =
    is-equiv-is-invertible
      (λ s y → tr C (is-section-g y) (s (g y)))
      ( λ s → eq-htpy (λ x →
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (is-retraction-g x) (s (g (f x)))) ∙
          ( apd s (is-retraction-g x)))))
      ( λ s → eq-htpy λ y → apd s (is-section-g y))
```

#### If `f` is an equivalence, then dependent precomposition by `f` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (H : is-equiv f) (C : B → UU l3)
  where

  abstract
    is-equiv-precomp-Π-is-equiv : is-equiv (precomp-Π f C)
    is-equiv-precomp-Π-is-equiv =
      is-equiv-precomp-Π-is-coherently-invertible f
        ( is-coherently-invertible-is-path-split f
          ( is-path-split-is-equiv f H))
        ( C)

  map-inv-is-equiv-precomp-Π-is-equiv :
    ((a : A) → C (f a)) → ((b : B) → C b)
  map-inv-is-equiv-precomp-Π-is-equiv =
    map-inv-is-equiv is-equiv-precomp-Π-is-equiv

  is-section-map-inv-is-equiv-precomp-Π-is-equiv :
    (h : (a : A) → C (f a)) →
    (precomp-Π f C (map-inv-is-equiv-precomp-Π-is-equiv h)) ~ h
  is-section-map-inv-is-equiv-precomp-Π-is-equiv h =
    htpy-eq (is-section-map-inv-is-equiv is-equiv-precomp-Π-is-equiv h)

  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv :
    (g : (b : B) → C b) →
    (map-inv-is-equiv-precomp-Π-is-equiv (precomp-Π f C g)) ~ g
  is-retraction-map-inv-is-equiv-precomp-Π-is-equiv g =
    htpy-eq (is-retraction-map-inv-is-equiv is-equiv-precomp-Π-is-equiv g)

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (is-equiv-map-equiv e) C
```

### Precomposition preserves homotopies

```agda
htpy-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B} (H : f ~ g) (C : UU l3) →
  precomp f C ~ precomp g C
htpy-precomp H C h = eq-htpy (h ·l H)

compute-htpy-precomp-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (htpy-precomp (refl-htpy' f) C) ~ refl-htpy
compute-htpy-precomp-refl-htpy f C h = eq-htpy-refl-htpy (h ∘ f)
```

### Precomposition preserves concatenation of homotopies

```agda
compute-concat-htpy-precomp :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  { f g h : A → B} (H : f ~ g) (K : g ~ h) (C : UU l3) →
  htpy-precomp (H ∙h K) C ~ (htpy-precomp H C ∙h htpy-precomp K C)
compute-concat-htpy-precomp H K C k =
  ( ap
    ( eq-htpy)
    ( eq-htpy (distributive-left-whisk-concat-htpy k H K))) ∙
  ( eq-htpy-concat-htpy (k ·l H) (k ·l K))
```

### If precomposition `- ∘ f : (Y → X) → (X → X)` has a section, then `f` has a retraction

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  where

  retraction-section-precomp-domain : section (precomp f X) → retraction f
  pr1 (retraction-section-precomp-domain s) =
    map-section (precomp f X) s id
  pr2 (retraction-section-precomp-domain s) =
    htpy-eq (is-section-map-section (precomp f X) s id)
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
      ( is-equiv-precomp-Π-is-equiv is-equiv-f)

  is-equiv-precomp-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A ≃ B) →
    (C : UU l3) → is-equiv (precomp (map-equiv f) C)
  is-equiv-precomp-equiv f =
    is-equiv-precomp-is-equiv (map-equiv f) (is-equiv-map-equiv f)

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
      is-equiv-is-invertible
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

#### Corollaries for particular subuniverses

```agda
is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : Prop l1) (Q : Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse
    ( λ l → l) (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse
    ( λ l → l) (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : Truncated-Type l1 k) (B : Truncated-Type l2 k)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : Truncated-Type l k) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse (λ l → l) (λ l → is-trunc k) A B f
      ( λ l → H {l})
```
