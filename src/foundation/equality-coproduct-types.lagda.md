# Equality of coproduct types

```agda
module foundation.equality-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.negated-equality
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.torsorial-type-families
open import foundation-core.truncated-types
open import foundation-core.truncation-levels
```

</details>

## Idea

In order to construct an identification `Id x y` in a coproduct `coprod A B`,
both `x` and `y` must be of the form `inl _` or of the form `inr _`. If that is
the case, then an identification can be constructed by constructin an
identification in A or in B, according to the case. This leads to the
characterization of identity types of coproducts.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  data Eq-coprod : A + B → A + B → UU (l1 ⊔ l2)
    where
    Eq-eq-coprod-inl : {x y : A} → x ＝ y → Eq-coprod (inl x) (inl y)
    Eq-eq-coprod-inr : {x y : B} → x ＝ y → Eq-coprod (inr x) (inr y)
```

## Properties

### The type `Eq-coprod x y` is equivalent to `Id x y`

We will use the fundamental theorem of identity types.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  refl-Eq-coprod : (x : A + B) → Eq-coprod x x
  refl-Eq-coprod (inl x) = Eq-eq-coprod-inl refl
  refl-Eq-coprod (inr x) = Eq-eq-coprod-inr refl

  Eq-eq-coprod : (x y : A + B) → x ＝ y → Eq-coprod x y
  Eq-eq-coprod x .x refl = refl-Eq-coprod x

  eq-Eq-coprod : (x y : A + B) → Eq-coprod x y → x ＝ y
  eq-Eq-coprod .(inl x) .(inl x) (Eq-eq-coprod-inl {x} {.x} refl) = refl
  eq-Eq-coprod .(inr x) .(inr x) (Eq-eq-coprod-inr {x} {.x} refl) = refl

  is-torsorial-Eq-coprod :
    (x : A + B) → is-torsorial (Eq-coprod x)
  pr1 (pr1 (is-torsorial-Eq-coprod (inl x))) = inl x
  pr2 (pr1 (is-torsorial-Eq-coprod (inl x))) = Eq-eq-coprod-inl refl
  pr2
    ( is-torsorial-Eq-coprod (inl x))
    ( pair (inl .x) (Eq-eq-coprod-inl refl)) = refl
  pr1 (pr1 (is-torsorial-Eq-coprod (inr x))) = inr x
  pr2 (pr1 (is-torsorial-Eq-coprod (inr x))) = Eq-eq-coprod-inr refl
  pr2
    ( is-torsorial-Eq-coprod (inr x))
    ( pair .(inr x) (Eq-eq-coprod-inr refl)) = refl

  is-equiv-Eq-eq-coprod : (x y : A + B) → is-equiv (Eq-eq-coprod x y)
  is-equiv-Eq-eq-coprod x =
    fundamental-theorem-id
      ( is-torsorial-Eq-coprod x)
      ( Eq-eq-coprod x)

  extensionality-coprod : (x y : A + B) → (x ＝ y) ≃ Eq-coprod x y
  pr1 (extensionality-coprod x y) = Eq-eq-coprod x y
  pr2 (extensionality-coprod x y) = is-equiv-Eq-eq-coprod x y
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

    map-compute-Eq-coprod-inl-inl : Eq-coprod {B = B} (inl x) (inl y) → (x ＝ y)
    map-compute-Eq-coprod-inl-inl (Eq-eq-coprod-inl p) = p

    is-section-Eq-eq-coprod-inl :
      (map-compute-Eq-coprod-inl-inl ∘ Eq-eq-coprod-inl) ~ id
    is-section-Eq-eq-coprod-inl p = refl

    is-retraction-Eq-eq-coprod-inl :
      (Eq-eq-coprod-inl ∘ map-compute-Eq-coprod-inl-inl) ~ id
    is-retraction-Eq-eq-coprod-inl (Eq-eq-coprod-inl p) = refl

    is-equiv-map-compute-Eq-coprod-inl-inl :
      is-equiv map-compute-Eq-coprod-inl-inl
    is-equiv-map-compute-Eq-coprod-inl-inl =
      is-equiv-is-invertible
        ( Eq-eq-coprod-inl)
        ( is-section-Eq-eq-coprod-inl)
        ( is-retraction-Eq-eq-coprod-inl)

    compute-Eq-coprod-inl-inl : Eq-coprod (inl x) (inl y) ≃ (x ＝ y)
    pr1 compute-Eq-coprod-inl-inl = map-compute-Eq-coprod-inl-inl
    pr2 compute-Eq-coprod-inl-inl = is-equiv-map-compute-Eq-coprod-inl-inl

    compute-eq-coprod-inl-inl : Id {A = A + B} (inl x) (inl y) ≃ (x ＝ y)
    compute-eq-coprod-inl-inl =
      compute-Eq-coprod-inl-inl ∘e extensionality-coprod (inl x) (inl y)

    map-compute-eq-coprod-inl-inl : Id {A = A + B} (inl x) (inl y) → x ＝ y
    map-compute-eq-coprod-inl-inl = map-equiv compute-eq-coprod-inl-inl

  module _
    (x : A) (y : B)
    where

    map-compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) → empty
    map-compute-Eq-coprod-inl-inr ()

    is-equiv-map-compute-Eq-coprod-inl-inr :
      is-equiv map-compute-Eq-coprod-inl-inr
    is-equiv-map-compute-Eq-coprod-inl-inr =
      is-equiv-is-empty' map-compute-Eq-coprod-inl-inr

    compute-Eq-coprod-inl-inr : Eq-coprod (inl x) (inr y) ≃ empty
    pr1 compute-Eq-coprod-inl-inr = map-compute-Eq-coprod-inl-inr
    pr2 compute-Eq-coprod-inl-inr = is-equiv-map-compute-Eq-coprod-inl-inr

    compute-eq-coprod-inl-inr : Id {A = A + B} (inl x) (inr y) ≃ empty
    compute-eq-coprod-inl-inr =
      compute-Eq-coprod-inl-inr ∘e extensionality-coprod (inl x) (inr y)

    is-empty-eq-coprod-inl-inr : is-empty (Id {A = A + B} (inl x) (inr y))
    is-empty-eq-coprod-inl-inr = map-equiv compute-eq-coprod-inl-inr

  module _
    (x : B) (y : A)
    where

    map-compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) → empty
    map-compute-Eq-coprod-inr-inl ()

    is-equiv-map-compute-Eq-coprod-inr-inl :
      is-equiv map-compute-Eq-coprod-inr-inl
    is-equiv-map-compute-Eq-coprod-inr-inl =
      is-equiv-is-empty' map-compute-Eq-coprod-inr-inl

    compute-Eq-coprod-inr-inl : Eq-coprod (inr x) (inl y) ≃ empty
    pr1 compute-Eq-coprod-inr-inl = map-compute-Eq-coprod-inr-inl
    pr2 compute-Eq-coprod-inr-inl = is-equiv-map-compute-Eq-coprod-inr-inl

    compute-eq-coprod-inr-inl : Id {A = A + B} (inr x) (inl y) ≃ empty
    compute-eq-coprod-inr-inl =
      compute-Eq-coprod-inr-inl ∘e extensionality-coprod (inr x) (inl y)

    is-empty-eq-coprod-inr-inl : is-empty (Id {A = A + B} (inr x) (inl y))
    is-empty-eq-coprod-inr-inl = map-equiv compute-eq-coprod-inr-inl

  module _
    (x y : B)
    where

    map-compute-Eq-coprod-inr-inr : Eq-coprod {A = A} (inr x) (inr y) → x ＝ y
    map-compute-Eq-coprod-inr-inr (Eq-eq-coprod-inr p) = p

    is-section-Eq-eq-coprod-inr :
      (map-compute-Eq-coprod-inr-inr ∘ Eq-eq-coprod-inr) ~ id
    is-section-Eq-eq-coprod-inr p = refl

    is-retraction-Eq-eq-coprod-inr :
      (Eq-eq-coprod-inr ∘ map-compute-Eq-coprod-inr-inr) ~ id
    is-retraction-Eq-eq-coprod-inr (Eq-eq-coprod-inr p) = refl

    is-equiv-map-compute-Eq-coprod-inr-inr :
      is-equiv map-compute-Eq-coprod-inr-inr
    is-equiv-map-compute-Eq-coprod-inr-inr =
      is-equiv-is-invertible
        ( Eq-eq-coprod-inr)
        ( is-section-Eq-eq-coprod-inr)
        ( is-retraction-Eq-eq-coprod-inr)

    compute-Eq-coprod-inr-inr : Eq-coprod (inr x) (inr y) ≃ (x ＝ y)
    pr1 compute-Eq-coprod-inr-inr = map-compute-Eq-coprod-inr-inr
    pr2 compute-Eq-coprod-inr-inr = is-equiv-map-compute-Eq-coprod-inr-inr

    compute-eq-coprod-inr-inr : Id {A = A + B} (inr x) (inr y) ≃ (x ＝ y)
    compute-eq-coprod-inr-inr =
      compute-Eq-coprod-inr-inr ∘e extensionality-coprod (inr x) (inr y)

    map-compute-eq-coprod-inr-inr : Id {A = A + B} (inr x) (inr y) → x ＝ y
    map-compute-eq-coprod-inr-inr = map-equiv compute-eq-coprod-inr-inr
```

### The left and right inclusions into a coproduct are embeddings

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coprod-inl-inl x))
          ( is-torsorial-path x))
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
          ( equiv-tot (compute-eq-coprod-inr-inr x))
          ( is-torsorial-path x))
        ( λ y → ap inr)

  emb-inr : B ↪ (A + B)
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr
```

### A map `A + B → C` defined by maps `f : A → C` and `B → C` is an embedding if both `f` and `g` are embeddings and they don't overlap

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  is-emb-coprod :
    is-emb f → is-emb g → ((a : A) (b : B) → f a ≠ g b) →
    is-emb (ind-coprod (λ x → C) f g)
  is-emb-coprod H K L (inl a) (inl a') =
    is-equiv-right-map-triangle
      ( ap f)
      ( ap (ind-coprod (λ x → C) f g))
      ( ap inl)
      ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
      ( H a a')
      ( is-emb-inl A B a a')
  is-emb-coprod H K L (inl a) (inr b') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
  is-emb-coprod H K L (inr b) (inl a') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
  is-emb-coprod H K L (inr b) (inr b') =
    is-equiv-right-map-triangle
      ( ap g)
      ( ap (ind-coprod (λ x → C) f g))
      ( ap inr)
      ( λ p → ap-comp (ind-coprod (λ x → C) f g) inr p)
      ( K b b')
      ( is-emb-inr A B b b')
```

### Coproducts of (k+2)-truncated types are (k+2)-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  abstract
    is-trunc-coprod :
      is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
      is-trunc (succ-𝕋 (succ-𝕋 k)) (A + B)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inl y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coprod-inl-inl x y)
        ( is-trunc-A x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inl x) (inr y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inl-inr x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inl y) =
      is-trunc-is-empty k (is-empty-eq-coprod-inr-inl x y)
    is-trunc-coprod is-trunc-A is-trunc-B (inr x) (inr y) =
      is-trunc-equiv (succ-𝕋 k)
        ( x ＝ y)
        ( compute-eq-coprod-inr-inr x y)
        ( is-trunc-B x y)
```

### Coproducts of sets are sets

```agda
abstract
  is-set-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A + B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : Set l1) (B : Set l2) → Set (l1 ⊔ l2)
pr1 (coprod-Set (pair A is-set-A) (pair B is-set-B)) = A + B
pr2 (coprod-Set (pair A is-set-A) (pair B is-set-B)) =
  is-set-coprod is-set-A is-set-B
```

## See also

- Equality proofs in coproduct types are characterized in
  [`foundation.equality-coproduct-types`](foundation.equality-coproduct-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
