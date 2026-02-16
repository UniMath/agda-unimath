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
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.double-negation
open import foundation.empty-types
open import foundation.equivalences
open import foundation.fiber-inclusions
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
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

[Propositional truncations](foundation.propositional-truncations.md) distributes
over finite products.

## Theorems

### Finite choice

```agda
abstract
  finite-choice-Fin :
    {l1 : Level} (k : ℕ) {Y : Fin k → UU l1} →
    ((x : Fin k) → is-inhabited (Y x)) → is-inhabited ((x : Fin k) → Y x)
  finite-choice-Fin 0 H = unit-trunc-Prop ind-empty
  finite-choice-Fin (succ-ℕ k) {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coproduct Y)
      ( map-inv-distributive-trunc-product-Prop
        ( pair
          ( finite-choice-Fin k (λ x → H (inl x)))
          ( map-inv-equiv-trunc-Prop
            ( equiv-dependent-universal-property-unit (Y ∘ inr))
            ( H (inr star)))))

module _
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  where

  abstract
    finite-choice-count :
      count X →
      ((x : X) → is-inhabited (Y x)) → is-inhabited ((x : X) → Y x)
    finite-choice-count (k , e) H =
      map-inv-equiv-trunc-Prop
        ( equiv-precomp-Π e Y)
        ( finite-choice-Fin k (H ∘ map-equiv e))

  abstract
    finite-choice :
      is-finite X →
      ((x : X) → is-inhabited (Y x)) → is-inhabited ((x : X) → Y x)
    finite-choice is-finite-X H =
      apply-universal-property-trunc-Prop is-finite-X
        ( trunc-Prop ((x : X) → Y x))
        ( λ e → finite-choice-count e H)
```

```agda
abstract
  ε-operator-count :
    {l : Level} {A : UU l} → count A → ε-operator-Hilbert A
  ε-operator-count (0 , e) t =
    ex-falso
      ( is-empty-type-trunc-Prop
        ( is-empty-is-zero-number-of-elements-count (0 , e) refl)
        ( t))
  ε-operator-count (succ-ℕ k , e) t = map-equiv e (zero-Fin k)

abstract
  ε-operator-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : decidable-subtype l2 A) →
    ε-operator-Hilbert (type-decidable-subtype P)
  ε-operator-decidable-subtype-count e P =
    ε-operator-equiv
      ( equiv-Σ-equiv-base (is-in-decidable-subtype P) (equiv-count e))
      ( ε-operator-decidable-subtype-Fin
        ( number-of-elements-count e)
        ( P ∘ map-equiv-count e))
```

```agda
abstract
  ε-operator-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} →
    (f : B ↪ᵈ A) → ε-operator-Hilbert B
  ε-operator-emb-count e f t =
    map-equiv-total-fiber
      ( map-decidable-emb f)
      ( ε-operator-decidable-subtype-count e
        ( decidable-subtype-decidable-emb f)
        ( map-trunc-Prop
          ( map-inv-equiv-total-fiber (map-decidable-emb f))
          ( t)))
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    choice-count-Σ-is-finite-fiber :
      is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
      ((x : A) → is-inhabited (B x)) → (x : A) → B x
    choice-count-Σ-is-finite-fiber K e g H x =
      ε-operator-count
        ( count-domain-emb-is-finite-domain-emb e
          ( fiber-inclusion-emb (A , K) B x)
          ( g x))
        ( H x)

  abstract
    choice-is-finite-Σ-is-finite-fiber :
      is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
      ((x : A) → is-inhabited (B x)) → is-inhabited ((x : A) → B x)
    choice-is-finite-Σ-is-finite-fiber K f g H =
      apply-universal-property-trunc-Prop f
        ( trunc-Prop ((x : A) → B x))
        ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))
```

### Finite choice with respect to double negation

```agda
abstract
  finite-double-negation-choice-Fin :
    {l1 : Level} (k : ℕ) {Y : Fin k → UU l1} →
    ((x : Fin k) → ¬¬ (Y x)) → ¬¬ ((x : Fin k) → Y x)
  finite-double-negation-choice-Fin 0 H = intro-double-negation ind-empty
  finite-double-negation-choice-Fin (succ-ℕ k) {Y} H =
    map-double-negation
      ( λ p → ind-coproduct Y (pr1 p) (pr2 p))
      ( map-inv-distributive-double-negation-product
        ( finite-double-negation-choice-Fin k (H ∘ inl) ,
          map-double-negation ind-unit (H (inr star))))

module _
  {l1 l2 : Level} {X : UU l1} {Y : X → UU l2}
  where

  abstract
    finite-double-negation-choice-count :
      count X → ((x : X) → ¬¬ (Y x)) → ¬¬ ((x : X) → Y x)
    finite-double-negation-choice-count (k , e) H =
      map-double-negation
        ( map-inv-equiv (equiv-precomp-Π e Y))
        ( finite-double-negation-choice-Fin k (H ∘ map-equiv e))

  abstract
    finite-double-negation-choice-double-negation-count :
      ¬¬ count X → ((x : X) → ¬¬ (Y x)) → ¬¬ ((x : X) → Y x)
    finite-double-negation-choice-double-negation-count nnc H nf =
      nnc (λ c → finite-double-negation-choice-count c H nf)

  abstract
    finite-double-negation-choice :
      is-finite X → ((x : X) → ¬¬ (Y x)) → ¬¬ ((x : X) → Y x)
    finite-double-negation-choice is-finite-X H =
      apply-universal-property-trunc-Prop is-finite-X
        ( double-negation-type-Prop ((x : X) → Y x))
        ( λ e → finite-double-negation-choice-count e H)
```

## See also

- [Distributivity of set truncation over finite products](univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.md)
