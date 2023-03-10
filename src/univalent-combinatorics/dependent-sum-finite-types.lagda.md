# Dependent sums of finite types

```agda
module univalent-combinatorics.dependent-sum-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.complements
open import foundation.contractible-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-propositions
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A dependent sum of finite types indexed by a finite type is finite.

```agda
abstract
  is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
  is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (Σ X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop
          ( finite-choice is-finite-X is-finite-Y)
          ( is-finite-Prop (Σ X Y))
          ( is-finite-count ∘ (count-Σ e)))

Σ-𝔽 : {l1 l2 : Level} (X : 𝔽 l1) (Y : type-𝔽 X → 𝔽 l2) → 𝔽 (l1 ⊔ l2)
pr1 (Σ-𝔽 X Y) = Σ (type-𝔽 X) (λ x → type-𝔽 (Y x))
pr2 (Σ-𝔽 X Y) =
  is-finite-Σ
    ( is-finite-type-𝔽 X)
    ( λ x → is-finite-type-𝔽 (Y x))

-- Theorem 16.3.6 (iii) (a) and (c) implies (b)

abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → is-finite (Σ X Y) → (x : X) → is-finite (Y x)
  is-finite-fiber-is-finite-Σ {l1} {l2} {X} {Y} f g x =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop (Y x))
      ( λ e → map-trunc-Prop (λ h → count-fiber-count-Σ e h x) g)

-- Theorem 16.3.6 (iii) (b), (c), B has a section implies (a)

abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop A)
      ( λ e →
        is-finite-count
          ( count-equiv
            ( ( equiv-total-fib-map-section b) ∘e
              ( equiv-tot
                ( λ t →
                  ( equiv-tot (λ x → equiv-eq-pair-Σ (map-section b x) t)) ∘e
                  ( ( assoc-Σ A
                      ( λ (x : A) → Id x (pr1 t))
                      ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                    ( inv-left-unit-law-Σ-is-contr
                      ( is-contr-total-path' (pr1 t))
                      ( pair (pr1 t) refl))))))
            ( count-Σ e
              ( λ t →
                count-eq
                  ( has-decidable-equality-is-finite (g (pr1 t)))
                  ( b (pr1 t))
                  ( pr2 t)))))

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop A)
      ( λ b → is-finite-base-is-finite-Σ-section b f g)
```

```agda
abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
    is-finite-base-is-finite-Σ-mere-section
      ( choice-is-finite-Σ-is-finite-fiber K f g b)
      ( f)
      ( g)
```

```agda
abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (x : A) → is-finite (B x)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-prop-is-inhabited-or-empty (B x))
              ( is-inhabited-or-empty-is-finite (g x)))) ∘e
        ( inv-equiv
          ( left-distributive-Σ-coprod A
            ( λ x → type-trunc-Prop (B x))
            ( λ x → is-empty (B x)))))
      ( is-finite-coprod
        ( is-finite-base-is-finite-Σ-merely-inhabited
          ( is-set-type-subtype (λ x → trunc-Prop _) K)
          ( λ t → pr2 t)
          ( is-finite-equiv
            ( equiv-right-swap-Σ)
            ( is-finite-Σ
              ( f)
              ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
          ( λ x → g (pr1 x)))
        ( h))
```
