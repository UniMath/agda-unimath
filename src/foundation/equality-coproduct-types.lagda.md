# Equality of coproduct types

```agda
module foundation.equality-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

In order to construct an identification `Id x y` in a coproduct `coproduct A B`,
both `x` and `y` must be of the form `inl _` or of the form `inr _`. If that is
the case, then an identification can be constructed by constructing an
identification in A or in B, according to the case. This leads to the
characterization of identity types of coproducts.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coproduct : A + B → A + B → UU (l1 ⊔ l2)
    where
    Eq-eq-coproduct-inl : {x y : A} → x ＝ y → Eq-coproduct (inl x) (inl y)
    Eq-eq-coproduct-inr : {x y : B} → x ＝ y → Eq-coproduct (inr x) (inr y)
```

## Properties

### The type `Eq-coproduct x y` is equivalent to `Id x y`

We will use the fundamental theorem of identity types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  refl-Eq-coproduct : (x : A + B) → Eq-coproduct x x
  refl-Eq-coproduct (inl x) = Eq-eq-coproduct-inl refl
  refl-Eq-coproduct (inr x) = Eq-eq-coproduct-inr refl

  Eq-eq-coproduct : (x y : A + B) → x ＝ y → Eq-coproduct x y
  Eq-eq-coproduct x .x refl = refl-Eq-coproduct x

  eq-Eq-coproduct : (x y : A + B) → Eq-coproduct x y → x ＝ y
  eq-Eq-coproduct .(inl x) .(inl x) (Eq-eq-coproduct-inl {x} {.x} refl) = refl
  eq-Eq-coproduct .(inr x) .(inr x) (Eq-eq-coproduct-inr {x} {.x} refl) = refl

  is-torsorial-Eq-coproduct :
    (x : A + B) → is-torsorial (Eq-coproduct x)
  pr1 (pr1 (is-torsorial-Eq-coproduct (inl x))) = inl x
  pr2 (pr1 (is-torsorial-Eq-coproduct (inl x))) = Eq-eq-coproduct-inl refl
  pr2
    ( is-torsorial-Eq-coproduct (inl x)) (.(inl x) , Eq-eq-coproduct-inl refl) =
    refl
  pr1 (pr1 (is-torsorial-Eq-coproduct (inr x))) = inr x
  pr2 (pr1 (is-torsorial-Eq-coproduct (inr x))) = Eq-eq-coproduct-inr refl
  pr2
    ( is-torsorial-Eq-coproduct (inr x)) (.(inr x) , Eq-eq-coproduct-inr refl) =
    refl

  is-equiv-Eq-eq-coproduct : (x y : A + B) → is-equiv (Eq-eq-coproduct x y)
  is-equiv-Eq-eq-coproduct x =
    fundamental-theorem-id (is-torsorial-Eq-coproduct x) (Eq-eq-coproduct x)

  extensionality-coproduct : (x y : A + B) → (x ＝ y) ≃ Eq-coproduct x y
  pr1 (extensionality-coproduct x y) = Eq-eq-coproduct x y
  pr2 (extensionality-coproduct x y) = is-equiv-Eq-eq-coproduct x y
```

Now we use the characterization of the identity type to obtain the desired
equivalences.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  module _
    (x y : A)
    where

    map-compute-Eq-coproduct-inl-inl :
      Eq-coproduct {B = B} (inl x) (inl y) → (x ＝ y)
    map-compute-Eq-coproduct-inl-inl (Eq-eq-coproduct-inl p) = p

    is-section-Eq-eq-coproduct-inl :
      (map-compute-Eq-coproduct-inl-inl ∘ Eq-eq-coproduct-inl) ~ id
    is-section-Eq-eq-coproduct-inl p = refl

    is-retraction-Eq-eq-coproduct-inl :
      (Eq-eq-coproduct-inl ∘ map-compute-Eq-coproduct-inl-inl) ~ id
    is-retraction-Eq-eq-coproduct-inl (Eq-eq-coproduct-inl p) = refl

    is-equiv-map-compute-Eq-coproduct-inl-inl :
      is-equiv map-compute-Eq-coproduct-inl-inl
    is-equiv-map-compute-Eq-coproduct-inl-inl =
      is-equiv-is-invertible
        ( Eq-eq-coproduct-inl)
        ( is-section-Eq-eq-coproduct-inl)
        ( is-retraction-Eq-eq-coproduct-inl)

    compute-Eq-coproduct-inl-inl : Eq-coproduct (inl x) (inl y) ≃ (x ＝ y)
    pr1 compute-Eq-coproduct-inl-inl = map-compute-Eq-coproduct-inl-inl
    pr2 compute-Eq-coproduct-inl-inl = is-equiv-map-compute-Eq-coproduct-inl-inl

    compute-eq-coproduct-inl-inl : Id {A = A + B} (inl x) (inl y) ≃ (x ＝ y)
    compute-eq-coproduct-inl-inl =
      compute-Eq-coproduct-inl-inl ∘e extensionality-coproduct (inl x) (inl y)

    map-compute-eq-coproduct-inl-inl : Id {A = A + B} (inl x) (inl y) → x ＝ y
    map-compute-eq-coproduct-inl-inl = map-equiv compute-eq-coproduct-inl-inl

    is-equiv-map-compute-eq-coproduct-inl-inl :
      is-equiv map-compute-eq-coproduct-inl-inl
    is-equiv-map-compute-eq-coproduct-inl-inl =
      is-equiv-map-equiv compute-eq-coproduct-inl-inl

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coproduct-inl-inr : Eq-coproduct (inl x) (inr y) → empty
    map-compute-Eq-coproduct-inl-inr ()

    is-equiv-map-compute-Eq-coproduct-inl-inr :
      is-equiv map-compute-Eq-coproduct-inl-inr
    is-equiv-map-compute-Eq-coproduct-inl-inr =
      is-equiv-is-empty' map-compute-Eq-coproduct-inl-inr

    compute-Eq-coproduct-inl-inr : Eq-coproduct (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coproduct-inl-inr = map-compute-Eq-coproduct-inl-inr
    pr2 compute-Eq-coproduct-inl-inr = is-equiv-map-compute-Eq-coproduct-inl-inr

    compute-eq-coproduct-inl-inr : Id {A = A + B} (inl x) (inr y) ≃ empty
    compute-eq-coproduct-inl-inr =
      compute-Eq-coproduct-inl-inr ∘e extensionality-coproduct (inl x) (inr y)

    is-empty-eq-coproduct-inl-inr : is-empty (Id {A = A + B} (inl x) (inr y))
    is-empty-eq-coproduct-inl-inr = map-equiv compute-eq-coproduct-inl-inr

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coproduct-inr-inl : Eq-coproduct (inr x) (inl y) → empty
    map-compute-Eq-coproduct-inr-inl ()

    is-equiv-map-compute-Eq-coproduct-inr-inl :
      is-equiv map-compute-Eq-coproduct-inr-inl
    is-equiv-map-compute-Eq-coproduct-inr-inl =
      is-equiv-is-empty' map-compute-Eq-coproduct-inr-inl

    compute-Eq-coproduct-inr-inl : Eq-coproduct (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coproduct-inr-inl = map-compute-Eq-coproduct-inr-inl
    pr2 compute-Eq-coproduct-inr-inl = is-equiv-map-compute-Eq-coproduct-inr-inl

    compute-eq-coproduct-inr-inl : Id {A = A + B} (inr x) (inl y) ≃ empty
    compute-eq-coproduct-inr-inl =
      compute-Eq-coproduct-inr-inl ∘e extensionality-coproduct (inr x) (inl y)

    is-empty-eq-coproduct-inr-inl : is-empty (Id {A = A + B} (inr x) (inl y))
    is-empty-eq-coproduct-inr-inl = map-equiv compute-eq-coproduct-inr-inl

  module _
    (x y : B)
    where

    map-compute-Eq-coproduct-inr-inr :
      Eq-coproduct {A = A} (inr x) (inr y) → x ＝ y
    map-compute-Eq-coproduct-inr-inr (Eq-eq-coproduct-inr p) = p

    is-section-Eq-eq-coproduct-inr :
      (map-compute-Eq-coproduct-inr-inr ∘ Eq-eq-coproduct-inr) ~ id
    is-section-Eq-eq-coproduct-inr p = refl

    is-retraction-Eq-eq-coproduct-inr :
      (Eq-eq-coproduct-inr ∘ map-compute-Eq-coproduct-inr-inr) ~ id
    is-retraction-Eq-eq-coproduct-inr (Eq-eq-coproduct-inr p) = refl

    is-equiv-map-compute-Eq-coproduct-inr-inr :
      is-equiv map-compute-Eq-coproduct-inr-inr
    is-equiv-map-compute-Eq-coproduct-inr-inr =
      is-equiv-is-invertible
        ( Eq-eq-coproduct-inr)
        ( is-section-Eq-eq-coproduct-inr)
        ( is-retraction-Eq-eq-coproduct-inr)

    compute-Eq-coproduct-inr-inr : Eq-coproduct (inr x) (inr y) ≃ (x ＝ y)
    pr1 compute-Eq-coproduct-inr-inr = map-compute-Eq-coproduct-inr-inr
    pr2 compute-Eq-coproduct-inr-inr = is-equiv-map-compute-Eq-coproduct-inr-inr

    compute-eq-coproduct-inr-inr : Id {A = A + B} (inr x) (inr y) ≃ (x ＝ y)
    compute-eq-coproduct-inr-inr =
      compute-Eq-coproduct-inr-inr ∘e extensionality-coproduct (inr x) (inr y)

    map-compute-eq-coproduct-inr-inr : Id {A = A + B} (inr x) (inr y) → x ＝ y
    map-compute-eq-coproduct-inr-inr = map-equiv compute-eq-coproduct-inr-inr

    is-equiv-map-compute-eq-coproduct-inr-inr :
      is-equiv map-compute-eq-coproduct-inr-inr
    is-equiv-map-compute-eq-coproduct-inr-inr =
      is-equiv-map-equiv compute-eq-coproduct-inr-inr
```

### The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coproduct-inl-inl x))
          ( is-torsorial-Id x))
        ( λ y → ap inl)

  emb-inl : A ↪ (A + B)
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coproduct-inr-inr x))
          ( is-torsorial-Id x))
        ( λ y → ap inr)

  emb-inr : B ↪ (A + B)
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr
```

Moreover, `is-injective-inl` and `is-injective-inr` are the inverses.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-retraction-is-injective-inl :
    {x y : A} →
    is-retraction (ap (inl {A = A} {B = B}) {x} {y}) (is-injective-inl)
  is-retraction-is-injective-inl refl = refl

  is-section-is-injective-inl :
    {x y : A} →
    is-section (ap (inl {A = A} {B = B}) {x} {y}) (is-injective-inl)
  is-section-is-injective-inl refl = refl

  is-retraction-is-injective-inr :
    {x y : B} →
    is-retraction (ap (inr {A = A} {B = B}) {x} {y}) (is-injective-inr)
  is-retraction-is-injective-inr refl = refl

  is-section-is-injective-inr :
    {x y : B} →
    is-section (ap (inr {A = A} {B = B}) {x} {y}) (is-injective-inr)
  is-section-is-injective-inr refl = refl
```

### A map `A + B → C` defined by maps `f : A → C` and `B → C` is an embedding if both `f` and `g` are embeddings and they don't overlap

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  is-emb-coproduct :
    is-emb f → is-emb g → ((a : A) (b : B) → f a ≠ g b) →
    is-emb (rec-coproduct f g)
  is-emb-coproduct H K L (inl a) (inl a') =
    is-equiv-right-map-triangle
      ( ap f)
      ( ap (rec-coproduct f g))
      ( ap inl)
      ( ap-comp (rec-coproduct f g) inl)
      ( H a a')
      ( is-emb-inl a a')
  is-emb-coproduct H K L (inl a) (inr b') =
    is-equiv-is-empty (ap (rec-coproduct f g)) (L a b')
  is-emb-coproduct H K L (inr b) (inl a') =
    is-equiv-is-empty (ap (rec-coproduct f g)) (L a' b ∘ inv)
  is-emb-coproduct H K L (inr b) (inr b') =
    is-equiv-right-map-triangle
      ( ap g)
      ( ap (rec-coproduct f g))
      ( ap inr)
      ( ap-comp (rec-coproduct f g) inr)
      ( K b b')
      ( is-emb-inr b b')
```

### Coproducts of `k+2`-truncated types are `k+2`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-coproduct :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (A + B)
    is-trunc-coproduct is-trunc-A is-trunc-B (inl x) (inl y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coproduct-inl-inl x y)
        ( is-trunc-A x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inl x) (inr y) =
      is-trunc-is-empty k (is-empty-eq-coproduct-inl-inr x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inr x) (inl y) =
      is-trunc-is-empty k (is-empty-eq-coproduct-inr-inl x y)
    is-trunc-coproduct is-trunc-A is-trunc-B (inr x) (inr y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coproduct-inr-inr x y)
        ( is-trunc-B x y)
```

### Coproducts of sets are sets

```agda
abstract
  is-set-coproduct :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A + B)
  is-set-coproduct = is-trunc-coproduct neg-two-𝕋

coproduct-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
pr1 (coproduct-Set (A , is-set-A) (B , is-set-B)) = A + B
pr2 (coproduct-Set (A , is-set-A) (B , is-set-B)) =
  is-set-coproduct is-set-A is-set-B
```

## See also

- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
