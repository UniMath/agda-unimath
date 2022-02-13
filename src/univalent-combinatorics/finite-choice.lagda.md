# Finite choice

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.finite-choice where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import elementary-number-theory.standard-finite-types using (Fin; zero-Fin)
open import
  elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( global-choice-decidable-subtype-Fin)

open import foundation.coproduct-types using (inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (_↪_; map-emb)
open import foundation.empty-types using
  ( ind-empty; ex-falso; is-empty-type-trunc-Prop)
open import foundation.equivalences using (equiv-precomp-Π; map-equiv)
open import foundation.fiber-inclusions using (fiber-inclusion-emb)
open import foundation.fibers-of-maps using
  ( fib; map-equiv-total-fib; map-inv-equiv-total-fib)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-Σ-equiv-base)
open import foundation.functoriality-propositional-truncation using
  ( map-inv-equiv-trunc-Prop; functor-trunc-Prop)
open import foundation.global-choice using (global-choice; global-choice-equiv)
open import foundation.identity-types using (refl)
open import foundation.propositional-maps using (fib-emb-Prop)
open import foundation.propositional-truncations using
  ( type-trunc-Prop; unit-trunc-Prop; map-inv-distributive-trunc-prod-Prop;
    apply-universal-property-trunc-Prop; trunc-Prop)
open import foundation.propositions using (UU-Prop; type-Prop)
open import foundation.sets using (is-set)
open import foundation.subtypes using (type-subtype)
open import foundation.unit-type using (unit; star)
open import foundation.universal-property-coproduct-types using
  ( equiv-dependent-universal-property-coprod)
open import foundation.universal-property-unit-type using
  ( equiv-dependent-universal-property-unit)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; is-empty-is-zero-number-of-elements-count; equiv-count;
    map-equiv-count)
open import univalent-combinatorics.counting-decidable-subtypes using
  ( count-domain-emb-is-finite-domain-emb)
open import univalent-combinatorics.finite-types using (is-finite)
```

## Idea

Propositional truncations distributes over finite products.

## Theorems

```agda
abstract
  finite-choice-Fin :
    {l1 : Level} {k : ℕ} {Y : Fin k → UU l1} →
    ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
  finite-choice-Fin {l1} {zero-ℕ} {Y} H = unit-trunc-Prop ind-empty
  finite-choice-Fin {l1} {succ-ℕ k} {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coprod Y)
      ( map-inv-distributive-trunc-prod-Prop
        ( pair
          ( finite-choice-Fin (λ x → H (inl x)))
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
      ( finite-choice-Fin (λ x → H (map-equiv e x)))

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
  global-choice-count :
    {l : Level} {A : UU l} → count A → global-choice A
  global-choice-count (pair zero-ℕ e) t =
    ex-falso
      ( is-empty-type-trunc-Prop
        ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
        ( t))
  global-choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

abstract
  global-choice-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
    ((x : A) → is-decidable (type-Prop (P x))) →
    global-choice (type-subtype P)
  global-choice-decidable-subtype-count e P d =
    global-choice-equiv
      ( equiv-Σ-equiv-base (type-Prop ∘ P) (equiv-count e))
      ( global-choice-decidable-subtype-Fin
        ( λ x → P (map-equiv-count e x))
        ( λ x → d (map-equiv-count e x)))
```

```agda
abstract
  global-choice-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
    ((x : A) → is-decidable (fib (map-emb f) x)) → global-choice B
  global-choice-emb-count e f d t =
    map-equiv-total-fib
      ( map-emb f)
      ( global-choice-decidable-subtype-count e
        ( fib-emb-Prop f)
        ( d)
        ( functor-trunc-Prop
          ( map-inv-equiv-total-fib (map-emb f))
          ( t)))
```

```agda
abstract
  choice-count-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
  choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
    global-choice-count
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
