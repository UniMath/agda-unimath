# Type duality

```agda
module foundation.type-duality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.locally-small-types
open import foundation.slice
open import foundation.surjective-maps
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.small-types
open import foundation-core.torsorial-type-families

open import trees.polynomial-endofunctors
open import trees.universal-polynomial-endofunctor
```

</details>

## Idea

Given a [univalent](foundation.univalence.md) universe `𝒰`, we can define two
closely related functors acting on all types. First there is the covariant
functor given by

```text
  P_𝒰(A) := Σ (X : 𝒰), X → A.
```

This is a [polynomial endofunctor](trees.polynomial-endofunctors.md). Second,
there is the contravariant functor given by

```text
  P^𝒰(A) := A → 𝒰.
```

If the type `A` is [locally `𝒰`-small](foundation.locally-small-types.md), then
there is a map `φ_A : P_𝒰(A) → P^𝒰(A)`. This map is natural in `A`, and it is
always an [embedding](foundation-core.embeddings.md). Furthermore, the map `φ_A`
is an [equivalence](foundation-core.equivalences.md) if and only if `A` is
[`𝒰`-small](foundation-core.small-types.md).

## Definitions

### The polynomial endofunctor of a universe

```agda
type-polynomial-endofunctor-UU :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
type-polynomial-endofunctor-UU l = Slice l

map-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-polynomial-endofunctor-UU l A → type-polynomial-endofunctor-UU l B
map-polynomial-endofunctor-UU l =
  map-polynomial-endofunctor (universal-polynomial-endofunctor l)
```

### Type families

```agda
type-exp-UU : (l : Level) {l1 : Level} → UU l1 → UU (lsuc l ⊔ l1)
type-exp-UU l A = A → UU l

map-exp-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-exp-UU l B → type-exp-UU l A
map-exp-UU l f P = P ∘ f
```

## Properties

### Characterizing equality in `type-polynomial-endofunctor-UU` over locally small `A`

```agda
module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  Eq-type-polynomial-endofunctor-UU' :
    type-polynomial-endofunctor-UU l A →
    type-polynomial-endofunctor-UU l A →
    UU (lsuc l ⊔ l1)
  Eq-type-polynomial-endofunctor-UU' (X , f) (Y , g) =
    ( λ a → Σ X (λ x → type-is-small (H (f x) a))) ＝
    ( λ a → Σ Y (λ y → type-is-small (H (g y) a)))

  compute-Eq-type-polynomial-endofunctor-UU' :
    (X Y : type-polynomial-endofunctor-UU l A) →
    (Eq-type-polynomial-endofunctor-UU' X Y) ≃ (X ＝ Y)
  compute-Eq-type-polynomial-endofunctor-UU' (X , f) (Y , g) =
    ( inv-equiv (extensionality-Slice (X , f) (Y , g))) ∘e
    ( inv-equiv (equiv-fam-equiv-equiv-slice f g)) ∘e
    ( equiv-Π-equiv-family
      ( λ a →
        ( equiv-postcomp-equiv
          ( equiv-tot (λ y → inv-equiv-is-small (H (g y) a)))
          ( fiber f a)) ∘e
        ( equiv-precomp-equiv
          ( equiv-tot (λ x → equiv-is-small (H (f x) a)))
          ( Σ Y (λ y → type-is-small (H (g y) a)))) ∘e
        ( equiv-univalence))) ∘e
    ( equiv-funext)

  compute-total-Eq-type-polynomial-endofunctor-UU' :
    (X : type-polynomial-endofunctor-UU l A) →
    Σ ( type-polynomial-endofunctor-UU l A)
      ( Eq-type-polynomial-endofunctor-UU' X) ≃
    Σ (type-polynomial-endofunctor-UU l A) (X ＝_)
  compute-total-Eq-type-polynomial-endofunctor-UU' X =
    equiv-tot (compute-Eq-type-polynomial-endofunctor-UU' X)

  abstract
    is-torsorial-Eq-type-polynomial-endofunctor-UU' :
      (X : type-polynomial-endofunctor-UU l A) →
      is-torsorial (Eq-type-polynomial-endofunctor-UU' X)
    is-torsorial-Eq-type-polynomial-endofunctor-UU' X =
      is-contr-equiv
        ( Σ ( type-polynomial-endofunctor-UU l A) (X ＝_))
        ( compute-total-Eq-type-polynomial-endofunctor-UU' X)
        ( is-torsorial-Id X)
```

### If `A` is locally `l`-small, then we can construct an embedding `type-polynomial-endofunctor l A ↪ type-exp-UU A`

```agda
module _
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  map-type-duality :
    type-polynomial-endofunctor-UU l A → type-exp-UU l A
  map-type-duality (X , f) a =
    Σ X (λ x → type-is-small (H (f x) a))

  abstract
    is-emb-map-type-duality : is-emb map-type-duality
    is-emb-map-type-duality (X , f) =
      fundamental-theorem-id
        ( is-torsorial-Eq-type-polynomial-endofunctor-UU' H (X , f))
        ( λ Y → ap map-type-duality)

  emb-type-duality :
    type-polynomial-endofunctor-UU l A ↪ type-exp-UU l A
  emb-type-duality = (map-type-duality , is-emb-map-type-duality)
```

### A type `A` is small if and only if `P_𝒰(A) ↪ P^𝒰(A)` is an equivalence

#### The forward direction

```agda
module _
  {l l1 : Level} {A : UU l1} (H : is-small l A)
  where

  map-inv-type-duality :
    type-exp-UU l A → type-polynomial-endofunctor-UU l A
  pr1 (map-inv-type-duality B) =
    type-is-small (is-small-Σ H (λ a → is-small' {l} {B a}))
  pr2 (map-inv-type-duality B) =
    ( pr1) ∘
    ( map-inv-equiv-is-small (is-small-Σ H (λ a → is-small' {l} {B a})))

  compute-map-type-duality :
    (B : type-exp-UU l A) (a : A) →
    map-type-duality
      ( is-locally-small-is-small H)
      ( map-inv-type-duality B)
      ( a) ≃
    B a
  compute-map-type-duality B a =
    equivalence-reasoning
      map-type-duality
        ( is-locally-small-is-small H)
        ( map-inv-type-duality B)
        ( a)
      ≃ fiber
          ( pr1 ∘ map-inv-equiv-is-small (is-small-Σ H (λ a → is-small')))
          ( a)
        by
        equiv-tot
          ( λ x →
            inv-equiv-is-small
              ( is-locally-small-is-small H
                ( pr2 (map-inv-type-duality B) x)
                ( a)))
      ≃ Σ ( fiber pr1 a)
          ( λ b →
            fiber
              ( map-inv-equiv-is-small
                ( is-small-Σ H (λ a → is-small' {l} {B a})))
              ( pr1 b))
        by compute-fiber-comp pr1 _ a
      ≃ fiber pr1 a
        by
        right-unit-law-Σ-is-contr
          ( λ b →
            is-contr-map-is-equiv
              ( is-equiv-map-inv-equiv-is-small
                ( is-small-Σ H (λ a → is-small' {l} {B a})))
              ( pr1 b))
      ≃ B a
        by equiv-fiber-pr1 B a

  abstract
    is-section-map-inv-type-duality :
      is-section
        ( map-type-duality (is-locally-small-is-small H))
        ( map-inv-type-duality)
    is-section-map-inv-type-duality B =
      eq-equiv-fam (compute-map-type-duality B)

  is-retraction-map-inv-type-duality :
    is-retraction
      ( map-type-duality (is-locally-small-is-small H))
      ( map-inv-type-duality)
  is-retraction-map-inv-type-duality X =
    is-injective-is-emb
      ( is-emb-map-type-duality (is-locally-small-is-small H))
      ( is-section-map-inv-type-duality
        ( map-type-duality (is-locally-small-is-small H) X))

  is-equiv-map-type-duality :
    is-equiv (map-type-duality (is-locally-small-is-small H))
  is-equiv-map-type-duality =
    is-equiv-is-invertible
      map-inv-type-duality
      is-section-map-inv-type-duality
      is-retraction-map-inv-type-duality

  type-duality : type-polynomial-endofunctor-UU l A ≃ type-exp-UU l A
  pr1 type-duality = map-type-duality (is-locally-small-is-small H)
  pr2 type-duality = is-equiv-map-type-duality
```

#### The converse direction

```agda
module _
  {l l1 : Level} {A : UU l1}
  (H : is-locally-small l A)
  (E : is-equiv (map-type-duality H))
  where

  type-is-small-is-equiv-map-type-duality : UU l
  type-is-small-is-equiv-map-type-duality =
    pr1 (map-inv-is-equiv E (λ _ → raise-unit l))

  map-inv-equiv-is-small-is-equiv-map-type-duality :
    type-is-small-is-equiv-map-type-duality → A
  map-inv-equiv-is-small-is-equiv-map-type-duality =
    pr2 (map-inv-is-equiv E (λ _ → raise-unit l))

  abstract
    is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality :
      is-contr-map map-inv-equiv-is-small-is-equiv-map-type-duality
    is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality a =
      is-contr-equiv
        ( raise-unit l)
        ( ( equiv-eq-fam _ _
            ( is-section-map-inv-is-equiv E (λ _ → raise-unit l))
            ( a)) ∘e
          ( equiv-tot
            ( λ x →
              equiv-is-small
                ( H (pr2 (map-inv-is-equiv E (λ _ → raise-unit l)) x) a))))
        ( is-contr-raise-unit)

  abstract
    is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality :
      is-equiv map-inv-equiv-is-small-is-equiv-map-type-duality
    is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality =
      is-equiv-is-contr-map
        is-contr-map-map-inv-equiv-is-small-is-equiv-map-type-duality

  inv-equiv-is-small-is-equiv-map-type-duality :
    type-is-small-is-equiv-map-type-duality ≃ A
  inv-equiv-is-small-is-equiv-map-type-duality =
    ( map-inv-equiv-is-small-is-equiv-map-type-duality ,
      is-equiv-map-inv-equiv-is-small-is-equiv-map-type-duality)

  equiv-is-small-is-equiv-map-type-duality :
    A ≃ type-is-small-is-equiv-map-type-duality
  equiv-is-small-is-equiv-map-type-duality =
    inv-equiv inv-equiv-is-small-is-equiv-map-type-duality

  is-small-is-equiv-map-type-duality : is-small l A
  is-small-is-equiv-map-type-duality =
    ( type-is-small-is-equiv-map-type-duality ,
      equiv-is-small-is-equiv-map-type-duality)
```

Since `map-type-duality` is always an embedding, it suffices to show it is
surjective.

```agda
module _
  {l l1 : Level} {A : UU l1}
  (H : is-locally-small l A)
  (E : is-surjective (map-type-duality H))
  where

  is-small-is-surjective-map-type-duality : is-small l A
  is-small-is-surjective-map-type-duality =
    is-small-is-equiv-map-type-duality H
      ( is-equiv-is-emb-is-surjective E (is-emb-map-type-duality H))
```

### Type duality formulated using `l1 ⊔ l2`

```agda
Fiber : {l l1 : Level} (A : UU l1) → Slice l A → A → UU (l1 ⊔ l)
Fiber A f = fiber (pr2 f)

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → Slice (l1 ⊔ l) A
pr1 (Pr1 A B) = Σ A B
pr2 (Pr1 A B) = pr1

is-section-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Fiber {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
is-section-Pr1 B = eq-equiv-fam (equiv-fiber-pr1 B)

is-retraction-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fiber {l1 ⊔ l2} A) ~ id
is-retraction-Pr1 {A = A} (X , f) =
  eq-equiv-slice
    ( Pr1 A (Fiber A (X , f)))
    ( X , f)
    ( equiv-total-fiber f , triangle-map-equiv-total-fiber f)

is-equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fiber {l1 ⊔ l2} A)
is-equiv-Fiber l2 A =
  is-equiv-is-invertible
    ( Pr1 A)
    ( is-section-Pr1 {l2 = l2})
    ( is-retraction-Pr1 {l2 = l2})

equiv-Fiber :
  {l1 : Level} (l2 : Level) (A : UU l1) → Slice (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
pr1 (equiv-Fiber l2 A) = Fiber A
pr2 (equiv-Fiber l2 A) = is-equiv-Fiber l2 A

is-equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
is-equiv-Pr1 {l1} l2 A =
  is-equiv-is-invertible
    ( Fiber A)
    ( is-retraction-Pr1 {l2 = l2})
    ( is-section-Pr1 {l2 = l2})

equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → (A → UU (l1 ⊔ l2)) ≃ Slice (l1 ⊔ l2) A
pr1 (equiv-Pr1 l2 A) = Pr1 A
pr2 (equiv-Pr1 l2 A) = is-equiv-Pr1 l2 A
```

The type of all function from `A → B` is equivalent to the type of function
`Y : B → 𝒰` with an equivalence `A ≃ Σ B Y `

```agda
fiber-Σ :
  {l1 l2 : Level} (X : UU l1) (A : UU l2) →
  (X → A) ≃ Σ (A → UU (l1 ⊔ l2)) (λ Y → X ≃ Σ A Y)
fiber-Σ {l1} {l2} X A =
  ( equiv-Σ
    ( λ Z → X ≃ Σ A Z)
    ( equiv-Fiber l1 A)
    ( λ s → equiv-postcomp-equiv (inv-equiv-total-fiber (pr2 s)) X)) ∘e
  ( equiv-right-swap-Σ) ∘e
  ( inv-left-unit-law-Σ-is-contr
    ( is-contr-is-small-lmax l2 X)
    ( is-small-lmax l2 X)) ∘e
  ( equiv-precomp (inv-equiv-is-small (is-small-lmax l2 X)) A)
```

## See also

- In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we
  show that [binary relations](foundation.binary-relations.md) are equivalently
  described as [spans of types](foundation.spans.md).
- [Subtype duality](foundation.subtype-duality.md)
- In
  [`structured-types.pointed-type-duality`](structured-types.pointed-type-duality.md)
  we show that families of [pointed types](structured-types.pointed-types.md)
  are equivalently described as
  [retractive types](structured-types.retractive-types.md).
