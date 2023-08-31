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
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.functoriality-function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.small-types

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given a univalent universe `𝒰`, we can define two closely related functors
acting on all types. First there is the covariant functor given by

```text
  P_𝒰(A) := Σ (X : 𝒰), X → A.
```

This is a polynomial endofunctor. Second, there is the contravariant functor
given by

```text
  P^𝒰(A) := A → 𝒰.
```

If the type `A` is locally 𝒰-small, then there is a map `φ_A : P_𝒰(A) → P^𝒰(A)`.
This map is natural in `A`, and it is always an embedding. Furthermore, the map
`φ_A` is an equivalence if and only if `A` is 𝒰-small.

## Definitions

### The polynomial endofunctor of a universe

```agda
type-polynomial-endofunctor-UU :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
type-polynomial-endofunctor-UU l = Slice l

map-polynomial-endofunctor-UU :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-polynomial-endofunctor-UU l A → type-polynomial-endofunctor-UU l B
map-polynomial-endofunctor-UU l = map-polynomial-endofunctor (UU l) (λ X → X)
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

### If `A` is locally `l`-small, then we can construct an embedding `type-polynomial-endofunctor l A ↪ type-exp-UU A`

```agda
map-type-duality :
  {l l1 : Level} {A : UU l1} → is-locally-small l A →
  type-polynomial-endofunctor-UU l A → type-exp-UU l A
map-type-duality H (X , f) a =
  Σ X (λ x → type-is-small (H (f x) a))

is-emb-map-type-duality :
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A) →
  is-emb (map-type-duality H)
is-emb-map-type-duality
  {l} {l1} {A} H (X , f) =
  fundamental-theorem-id
    ( is-contr-equiv
      ( Σ ( type-polynomial-endofunctor-UU l A) (λ Y → (X , f) ＝ Y))
      ( equiv-tot
        ( λ (Y , g) →
          equivalence-reasoning
            ( map-type-duality H
                (X , f) ＝
              map-type-duality H
                (Y , g))
            ≃ ( (a : A) →
                Σ X (λ x → type-is-small (H (f x) a)) ＝
                Σ Y (λ y → type-is-small (H (g y) a)))
              by equiv-funext
            ≃ ( (a : A) →
                Σ X (λ x → type-is-small (H (f x) a)) ≃
                Σ Y (λ y → type-is-small (H (g y) a)))
              by equiv-map-Π (λ a → equiv-univalence)
            ≃ ( (a : A) →
                fib f a ≃ Σ Y (λ y → type-is-small (H (g y) a)))
              by
              equiv-map-Π
                ( λ a →
                  equiv-precomp-equiv
                    ( equiv-tot (λ x → equiv-is-small (H (f x) a)))
                    ( Σ Y (λ y → type-is-small (H (g y) a))))
            ≃ ( (a : A) → fib f a ≃ fib g a)
              by
              equiv-map-Π
                ( λ a →
                  equiv-postcomp-equiv
                    ( equiv-tot (λ y → inv-equiv (equiv-is-small (H (g y) a))))
                    ( fib f a))
            ≃ equiv-slice f g
              by inv-equiv (equiv-fam-equiv-equiv-slice f g)
            ≃ ( (X , f) ＝ (Y , g))
              by
              inv-equiv (extensionality-Slice (X , f) (Y , g))))
      ( is-contr-total-path (X , f)))
    ( λ Y → ap (map-type-duality H))

emb-type-duality :
  {l l1 : Level} {A : UU l1} → is-locally-small l A →
  type-polynomial-endofunctor-UU l A ↪ type-exp-UU l A
pr1 (emb-type-duality H) =
  map-type-duality H
pr2 (emb-type-duality H) =
  is-emb-map-type-duality H
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
    type-is-small (is-small-Σ {l3 = l} {l4 = l} H (λ a → is-small' {l} {B a}))
  pr2 (map-inv-type-duality B) =
    ( pr1) ∘
    ( map-inv-equiv
      ( equiv-is-small
        ( is-small-Σ {l3 = l} {l4 = l} H (λ a → is-small' {l} {B a}))))

  is-section-map-inv-type-duality :
    ( map-type-duality (is-locally-small-is-small H) ∘ map-inv-type-duality) ~
    id
  is-section-map-inv-type-duality B =
    eq-equiv-fam
      ( λ a →
        equivalence-reasoning
          map-type-duality
            ( is-locally-small-is-small H)
            ( map-inv-type-duality B)
            ( a)
          ≃ fib
            ( ( pr1 {B = B}) ∘
              ( map-inv-equiv
                ( equiv-is-small
                  ( is-small-Σ H (λ a → is-small'))))) a
            by
            equiv-tot
              ( λ x →
                inv-equiv
                  ( equiv-is-small
                    ( is-locally-small-is-small H
                      ( pr2 (map-inv-type-duality B) x)
                      ( a))))
          ≃ Σ ( fib (pr1 {B = B}) a)
              ( λ b →
                fib
                  ( map-inv-equiv
                    ( equiv-is-small
                      ( is-small-Σ H (λ a → is-small' {l} {B a}))))
                  ( pr1 b))
            by equiv-compute-fib-comp pr1 _ a
          ≃ fib (pr1 {B = B}) a
            by
            right-unit-law-Σ-is-contr
              ( λ b →
                is-contr-map-is-equiv
                  ( is-equiv-map-inv-equiv
                    ( equiv-is-small
                      ( is-small-Σ H (λ a → is-small' {l} {B a}))))
                  ( pr1 b))
          ≃ B a
            by
            equiv-fib-pr1 B a)

  is-retraction-map-inv-type-duality :
    ( map-inv-type-duality ∘ map-type-duality (is-locally-small-is-small H)) ~
    id
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
  {l l1 : Level} {A : UU l1} (H : is-locally-small l A)
  where

  is-small-is-equiv-map-type-duality :
    is-equiv (map-type-duality H) → is-small l A
  pr1 (is-small-is-equiv-map-type-duality E) =
    pr1 (map-inv-is-equiv E (λ a → raise-unit l))
  pr2 (is-small-is-equiv-map-type-duality E) =
    inv-equiv
      ( pair
        ( pr2 (map-inv-is-equiv E (λ a → raise-unit l)))
        ( is-equiv-is-contr-map
          ( λ a →
            is-contr-equiv
              ( raise-unit l)
              ( ( equiv-eq-fam _ _
                  ( is-section-map-inv-is-equiv E (λ _ → raise-unit l))
                  ( a)) ∘e
                ( equiv-tot
                  ( λ x →
                    equiv-is-small
                      ( H ( pr2 (map-inv-is-equiv E (λ _ → raise-unit l)) x)
                          ( a)))))
              ( is-contr-raise-unit))))
```

### Type duality formulated using `l1 ⊔ l2`

```agda
Fib : {l l1 : Level} (A : UU l1) → Slice l A → A → UU (l1 ⊔ l)
Fib A f = fib (pr2 f)

Pr1 : {l l1 : Level} (A : UU l1) → (A → UU l) → Slice (l1 ⊔ l) A
pr1 (Pr1 A B) = Σ A B
pr2 (Pr1 A B) = pr1

is-section-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Fib {l1 ⊔ l2} A ∘ Pr1 {l1 ⊔ l2} A) ~ id
is-section-Pr1 B = eq-equiv-fam (equiv-fib-pr1 B)

is-retraction-Pr1 :
  {l1 l2 : Level} {A : UU l1} → (Pr1 {l1 ⊔ l2} A ∘ Fib {l1 ⊔ l2} A) ~ id
is-retraction-Pr1 {A = A} (pair X f) =
  eq-equiv-slice
    ( Pr1 A (Fib A (pair X f)))
    ( pair X f)
    ( pair (equiv-total-fib f) (triangle-map-equiv-total-fib f))

is-equiv-Fib :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Fib {l1 ⊔ l2} A)
is-equiv-Fib l2 A =
  is-equiv-is-invertible
    ( Pr1 A)
    ( is-section-Pr1 {l2 = l2})
    ( is-retraction-Pr1 {l2 = l2})

equiv-Fib :
  {l1 : Level} (l2 : Level) (A : UU l1) → Slice (l1 ⊔ l2) A ≃ (A → UU (l1 ⊔ l2))
pr1 (equiv-Fib l2 A) = Fib A
pr2 (equiv-Fib l2 A) = is-equiv-Fib l2 A

is-equiv-Pr1 :
  {l1 : Level} (l2 : Level) (A : UU l1) → is-equiv (Pr1 {l1 ⊔ l2} A)
is-equiv-Pr1 {l1} l2 A =
  is-equiv-is-invertible
    ( Fib A)
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
fib-Σ :
  {l1 l2 : Level} (X : UU l1) (A : UU l2) →
  (X → A) ≃
    Σ (A → UU (l2 ⊔ l1)) (λ Y → X ≃ Σ A Y)
fib-Σ {l1} {l2} X A =
  ( ( equiv-Σ
      ( λ Z → X ≃ Σ A Z)
      ( equiv-Fib l1 A)
      ( λ s →
        inv-equiv ( equiv-postcomp-equiv (equiv-total-fib (pr2 s)) X))) ∘e
    ( ( equiv-right-swap-Σ) ∘e
      ( ( inv-left-unit-law-Σ-is-contr
          ( is-contr-is-small-lmax l2 X)
          ( is-small-lmax l2 X)) ∘e
        ( equiv-precomp (inv-equiv (equiv-is-small (is-small-lmax l2 X))) A))))
```
