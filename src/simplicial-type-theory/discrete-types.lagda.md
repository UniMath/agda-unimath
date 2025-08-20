# Simplicially discrete types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.discrete-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.connected-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.diagonal-maps-of-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.equivalences-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import orthogonal-factorization-systems.null-maps
open import orthogonal-factorization-systems.null-types

open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.fully-faithful-maps I
open import simplicial-type-theory.inequality-directed-interval I

open import synthetic-homotopy-theory.circle
```

</details>

## Idea

A type `A` is
{{#concept "simplicially discrete" Disambiguation="type" Agda=is-discrete▵}} if
the canonical map

```text
  hom▵-eq : (x ＝ y) → (x →▵ y)
```

is an [equivalence](foundation-core.equivalences.md) for all `x y : A`. A
simplicially discrete type bears only trivial simplicial structure in the sense
that its simplices act precisely as its identifications. In particular,
simplicially discrete types are Rezk complete and Segal.

## Definitions

### The predicate on types of being simplicially discrete

```agda
module _
  {l : Level} (A : UU l)
  where

  is-discrete▵ : UU (I1 ⊔ l)
  is-discrete▵ = (x y : A) → is-equiv (hom▵-eq {x = x} {y})

  is-prop-is-discrete▵ : is-prop is-discrete▵
  is-prop-is-discrete▵ =
    is-prop-Π (λ x → is-prop-Π (λ y → is-property-is-equiv hom▵-eq))

  is-discrete▵-Prop : Prop (I1 ⊔ l)
  is-discrete▵-Prop = (is-discrete▵ , is-prop-is-discrete▵)
```

### The type of simplicially discrete types

```agda
Discrete-Type▵ : (l : Level) → UU (I1 ⊔ lsuc l)
Discrete-Type▵ l = Σ (UU l) (is-discrete▵)

module _
  {l : Level} (A : Discrete-Type▵ l)
  where

  type-Discrete-Type▵ : UU l
  type-Discrete-Type▵ = pr1 A

  is-discrete▵-Discrete-Type▵ : is-discrete▵ type-Discrete-Type▵
  is-discrete▵-Discrete-Type▵ = pr2 A
```

## Properties

### To show a type is simplicially discrete it suffices to construct a section of `hom▵-eq`

```agda
module _
  {l : Level} (A : UU l)
  where

  is-discrete▵-section-hom▵-eq :
    ((x y : A) → section (hom▵-eq {x = x} {y})) → is-discrete▵ A
  is-discrete▵-section-hom▵-eq s x =
    fundamental-theorem-id-section x (λ y → hom▵-eq) (s x)
```

### Being simplicially discrete is equivalent to being `Δ¹`-null

**Proof.** We have the [equivalence of maps](foundation.equivalences-arrows.md)

```text
            ~
     A -------> Σ (x y : A), (x ＝ y)
     |                 |
   Δ |                 | Σ² hom▵-eq
     ∨                 ∨
  (Δ¹ → A) ----> Σ (x y : A), (x →▵ y),
            ~
```

which implies that the diagonal map is an equivalence if and only if the total
map of `hom▵-eq` is, and the total map is an equivalence if and only if the
fiberwise map is.

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-tot-hom▵-eq-diagonal-exponential-Δ¹ :
    equiv-arrow
      ( diagonal-exponential A Δ¹)
      ( tot (λ x → tot (λ y → hom▵-eq {x = x} {y})))
  equiv-tot-hom▵-eq-diagonal-exponential-Δ¹ =
    ( compute-total-Id , compute-total-hom▵ , refl-htpy)

  abstract
    is-discrete▵-is-Δ¹-null : is-null Δ¹ A → is-discrete▵ A
    is-discrete▵-is-Δ¹-null H x =
      is-fiberwise-equiv-is-equiv-tot
        ( is-fiberwise-equiv-is-equiv-tot
          ( is-equiv-target-is-equiv-source-equiv-arrow
            ( diagonal-exponential A Δ¹)
            ( tot (λ x → tot (λ y → hom▵-eq {x = x} {y})))
            ( equiv-tot-hom▵-eq-diagonal-exponential-Δ¹)
            ( H))
          ( x))

  abstract
    is-Δ¹-null-is-discrete▵ : is-discrete▵ A → is-null Δ¹ A
    is-Δ¹-null-is-discrete▵ H =
      is-equiv-source-is-equiv-target-equiv-arrow
        ( diagonal-exponential A Δ¹)
        ( tot (λ x → tot (λ y → hom▵-eq {x = x} {y})))
        ( equiv-tot-hom▵-eq-diagonal-exponential-Δ¹)
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ x → is-equiv-tot-is-fiberwise-equiv (H x)))

  iff-is-Δ¹-null-is-discrete▵ : is-discrete▵ A ↔ is-null Δ¹ A
  iff-is-Δ¹-null-is-discrete▵ =
    ( is-Δ¹-null-is-discrete▵ , is-discrete▵-is-Δ¹-null)
```

### Simplicially discrete types are closed under retracts

```agda
is-discrete▵-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → is-discrete▵ B → is-discrete▵ A
is-discrete▵-retract r H =
  is-discrete▵-is-Δ¹-null (is-null-retract-base r (is-Δ¹-null-is-discrete▵ H))
```

### Simplicially discrete types are closed under equivalences

```agda
is-discrete▵-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A ≃ B → is-discrete▵ B → is-discrete▵ A
is-discrete▵-equiv e H =
  is-discrete▵-is-Δ¹-null (is-null-equiv-base e (is-Δ¹-null-is-discrete▵ H))
```

### Simplicially discrete types are closed under dependent products

```agda
is-discrete▵-Π :
  {l1 l2 : Level} {I : UU l1} {B : I → UU l2} →
  ((i : I) → is-discrete▵ (B i)) →
  is-discrete▵ ((i : I) → B i)
is-discrete▵-Π H =
  is-discrete▵-is-Δ¹-null (is-null-Π (λ i → is-Δ¹-null-is-discrete▵ (H i)))
```

### Simplicially discrete types are closed under exponentiation

```agda
is-discrete▵-function-type :
  {l1 l2 : Level} {I : UU l1} {B : UU l2} →
  is-discrete▵ B → is-discrete▵ (I → B)
is-discrete▵-function-type H = is-discrete▵-Π (λ _ → H)
```

### Simplicially discrete types are closed under cartesian products

```agda
is-discrete▵-product :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  is-discrete▵ A → is-discrete▵ B → is-discrete▵ (A × B)
is-discrete▵-product is-disc-A is-disc-B =
  is-discrete▵-is-Δ¹-null
    ( is-null-product
      ( is-Δ¹-null-is-discrete▵ is-disc-A)
      ( is-Δ¹-null-is-discrete▵ is-disc-B))
```

### Simplicially discrete types are closed under dependent sums

```agda
is-discrete▵-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-discrete▵ A → ((x : A) → is-discrete▵ (B x)) → is-discrete▵ (Σ A B)
is-discrete▵-Σ is-disc-A is-disc-B =
  is-discrete▵-is-Δ¹-null
    ( is-null-Σ
      ( is-Δ¹-null-is-discrete▵ is-disc-A)
      ( λ x → is-Δ¹-null-is-discrete▵ (is-disc-B x)))
```

### A family over a simplicially discrete type is a family of simplicially discrete types if and only if the dependent sum is

One direction was established above, the converse is recorded below.

```agda
is-discrete▵-family-is-discrete▵-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-discrete▵ A → is-discrete▵ (Σ A B) → (x : A) → is-discrete▵ (B x)
is-discrete▵-family-is-discrete▵-Σ
  is-disc-A is-disc-ΣAB x =
  is-discrete▵-is-Δ¹-null
    ( is-null-family-is-null-Σ
      ( is-Δ¹-null-is-discrete▵ is-disc-A)
      ( is-Δ¹-null-is-discrete▵ is-disc-ΣAB)
      ( x))
```

### Simplicially discrete types are Segal

This remains to be formalized. The proof boils down to showing that `Λ²₁ ↪ Δ²`
is anodyne with respect to `Δ¹ → 1`.

### A type is simplicially discrete if and only if it is pregroupoidal and Rezk complete

> This remains to be formalized. This is proposition 10.10 of {{#cite RS17}}.

<!-- TODO triangle `iso-eq`, `hom-iso`, `hom-eq` -->

## Examples

### The directed interval is not simplicially discrete

```agda
is-not-discrete▵-Δ¹ : ¬ (is-discrete▵ Δ¹)
is-not-discrete▵-Δ¹ H =
  is-nontrivial-Δ¹ (map-inv-is-equiv (H 0▵ 1▵) representing-hom-Δ¹)
```

### Propositions are simplicially discrete

```agda
is-discrete▵-is-prop : {l : Level} {P : UU l} → is-prop P → is-discrete▵ P
is-discrete▵-is-prop =
  is-discrete▵-is-Δ¹-null ∘ is-null-is-prop-is-inhabited' 0▵
```

### Contractible types are simplicially discrete

```agda
is-discrete▵-is-contr : {l : Level} {P : UU l} → is-contr P → is-discrete▵ P
is-discrete▵-is-contr is-contr-P =
  is-discrete▵-is-prop (is-prop-is-contr is-contr-P)
```

### Empty types are simplicially discrete

```agda
is-discrete▵-is-empty : {l : Level} {P : UU l} → is-empty P → is-discrete▵ P
is-discrete▵-is-empty is-empty-P =
  is-discrete▵-is-prop (is-prop-is-empty is-empty-P)
```

## References

{{#bibliography}} {{#reference RS17}}
