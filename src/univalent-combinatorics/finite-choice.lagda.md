# Finite choice

```agda
module univalent-combinatorics.finite-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.well-ordering-principle-standard-finite-types

open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-subtypes
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universal-property-coproduct-types
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-decidable-subtypes
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Propositional truncations distributes over finite products.

## Theorems

```agda
abstract
  finite-choice-Fin :
    {l1 : Level} (k : ℕ) {Y : Fin k → UU l1} →
    ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
  finite-choice-Fin {l1} zero-ℕ {Y} H = unit-trunc-Prop ind-empty
  finite-choice-Fin {l1} (succ-ℕ k) {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coprod Y)
      ( map-inv-distributive-trunc-prod-Prop
        ( pair
          ( finite-choice-Fin k (λ x → H (inl x)))
          ( map-inv-equiv-trunc-Prop
            ( equiv-dependent-universal-property-unit (Y ∘ inr))
            ( H (inr star)))))

abstract
  finite-choice-count :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice-count {l1} {l2} {X} {Y} (pair k e) H =
    map-inv-equiv-trunc-Prop
      ( equiv-precomp-Π e Y)
      ( finite-choice-Fin k (λ x → H (map-equiv e x)))

abstract
  finite-choice :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice {l1} {l2} {X} {Y} is-finite-X H =
    apply-universal-property-trunc-Prop is-finite-X
      ( trunc-Prop ((x : X) → Y x))
      ( λ e → finite-choice-count e H)
```

```agda
abstract
  ε-operator-count :
    {l : Level} {A : UU l} → count A → ε-operator-Hilbert A
  ε-operator-count (pair zero-ℕ e) t =
    ex-falso
      ( is-empty-type-trunc-Prop
        ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
        ( t))
  ε-operator-count (pair (succ-ℕ k) e) t = map-equiv e (zero-Fin k)

abstract
  ε-operator-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : decidable-subtype l2 A) →
    ε-operator-Hilbert (type-decidable-subtype P)
  ε-operator-decidable-subtype-count e P =
    ε-operator-equiv
      ( equiv-Σ-equiv-base (is-in-decidable-subtype P) (equiv-count e))
      ( ε-operator-decidable-subtype-Fin
        ( number-of-elements-count e)
        ( λ x → P (map-equiv-count e x)))
```

```agda
abstract
  ε-operator-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} →
    (f : B ↪d A) → ε-operator-Hilbert B
  ε-operator-emb-count e f t =
    map-equiv-total-fib
      ( map-decidable-emb f)
      ( ε-operator-decidable-subtype-count e
        ( decidable-subtype-decidable-emb f)
        ( map-trunc-Prop
          ( map-inv-equiv-total-fib (map-decidable-emb f))
          ( t)))
```

```agda
abstract
  choice-count-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
  choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
    ε-operator-count
      ( count-domain-emb-is-finite-domain-emb e
        ( fiber-inclusion-emb (pair A K) B x)
        ( g x))
      ( H x)

abstract
  choice-is-finite-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
  choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
    apply-universal-property-trunc-Prop f
      ( trunc-Prop ((x : A) → B x))
      ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))
```
