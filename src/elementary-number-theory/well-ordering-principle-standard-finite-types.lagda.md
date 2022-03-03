# The Well-Ordering Principle of the standard finite types

```agda
{-# OPTIONS --without-K --exact-split #-}

module
  elementary-number-theory.well-ordering-principle-standard-finite-types
  where

open import elementary-number-theory.decidable-dependent-pair-types using
  ( is-decidable-Σ-Fin)
open import elementary-number-theory.inequality-standard-finite-types using
  ( leq-Fin; leq-neg-one-Fin; refl-leq-Fin; is-prop-leq-Fin;
    antisymmetric-leq-Fin)
open import elementary-number-theory.modular-arithmetic-standard-finite-types
  using (mod-succ-ℕ; issec-nat-Fin)
open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import
  elementary-number-theory.well-ordering-principle-natural-numbers using
  ( global-choice-decidable-subtype-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (inl; inr; ind-coprod)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-fam; is-decidable-iff)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using
  ( ex-falso; ind-empty; empty-Prop; is-empty-type-trunc-Prop)
open import foundation.equivalences using
  ( _∘e_; htpy-eq-equiv; id-equiv; map-equiv; map-inv-equiv; right-inverse-law-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.functoriality-dependent-pair-types using
  ( map-Σ; map-Σ-map-base)
open import foundation.functoriality-propositional-truncation using
  ( functor-trunc-Prop; map-equiv-trunc-Prop)
open import foundation.global-choice using (global-choice)
open import foundation.identity-types using (tr; inv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; type-trunc-Prop)
open import foundation.propositions using
  ( is-prop; is-prop-Π; is-prop-function-type; UU-Prop; all-elements-equal;
    prod-Prop; is-prop-all-elements-equal; type-Prop)
open import foundation.subtypes using (eq-subtype; type-subtype)
open import foundation.type-arithmetic-coproduct-types using
  ( right-distributive-Σ-coprod)
open import foundation.type-arithmetic-empty-type using
  ( right-unit-law-coprod-is-empty)
open import foundation.type-arithmetic-unit-type using (left-unit-law-Σ)
open import foundation.unit-type using (unit; star; ind-unit)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.standard-finite-types using
  ( Fin; inl-Fin; neg-one-Fin; nat-Fin)
open import univalent-combinatorics.counting using (count; number-of-elements-count)
```

# The well-ordering principle on the standard finite types

```agda
exists-not-not-forall-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} → (is-decidable-fam P) →
  ¬ ((x : Fin k) → P x) → Σ (Fin k) (λ x → ¬ (P x))
exists-not-not-forall-Fin {l} {zero-ℕ} d H = ex-falso (H ind-empty)
exists-not-not-forall-Fin {l} {succ-ℕ k} {P} d H with d (inr star)
... | inl p =
  T ( exists-not-not-forall-Fin
      ( λ x → d (inl x))
      ( λ f → H (ind-coprod P f (ind-unit p))))
  where
  T : Σ (Fin k) (λ x → ¬ (P (inl x))) → Σ (Fin (succ-ℕ k)) (λ x → ¬ (P x))
  T z = pair (inl (pr1 z)) (pr2 z)
... | inr f = pair (inr star) f

exists-not-not-forall-count :
  {l1 l2 : Level} {X : UU l1} (P : X → UU l2) →
  (is-decidable-fam P) → count X →
  ¬ ((x : X) → P x) → Σ X (λ x → ¬ (P x))
exists-not-not-forall-count {l1} {l2} {X} P p e =
  g ∘ ((exists-not-not-forall-Fin (p ∘ (map-equiv (pr2 e)) )) ∘ f)
  where
  k : ℕ
  k = number-of-elements-count e
  P' : Fin k → UU l2
  P' = P ∘ map-equiv (pr2 e)
  f : ¬ ((x : X) → P x) → ¬ ((x : Fin k) → P' x)
  f nf f' =
    nf
      ( λ x →
        tr P (htpy-eq-equiv (right-inverse-law-equiv (pr2 e)) x) (f' (map-inv-equiv (pr2 e) x)))
  g : Σ (Fin k) (λ x → ¬ (P' x)) → Σ X (λ x → ¬ (P x))
  pr1 (g (pair l np)) = map-equiv (pr2 e) l
  pr2 (g (pair l np)) x = np x

```

```agda
is-lower-bound-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → Fin k → UU l
is-lower-bound-Fin {l} {k} P x =
  (y : Fin k) → P y → leq-Fin x y

abstract
  is-prop-is-lower-bound-Fin :
    {l : Level} {k : ℕ} {P : Fin k → UU l} (x : Fin k) →
    is-prop (is-lower-bound-Fin P x)
  is-prop-is-lower-bound-Fin x =
    is-prop-Π (λ y → is-prop-function-type (is-prop-leq-Fin x y))

  is-lower-bound-fin-Prop :
    {l : Level} {k : ℕ} (P : Fin k → UU l) (x : Fin k) → UU-Prop l
  pr1 (is-lower-bound-fin-Prop P x) = is-lower-bound-Fin P x
  pr2 (is-lower-bound-fin-Prop P x) = is-prop-is-lower-bound-Fin x

minimal-element-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → UU l
minimal-element-Fin {l} {k} P =
  Σ (Fin k) (λ x → (P x) × is-lower-bound-Fin P x)

abstract
  all-elements-equal-minimal-element-Fin :
    {l : Level} {k : ℕ} (P : Fin k → UU l) →
    ((x : Fin k) → is-prop (P x)) → all-elements-equal (minimal-element-Fin P)
  all-elements-equal-minimal-element-Fin P H
    (pair x (pair p l)) (pair y (pair q m)) =
    eq-subtype
      ( λ t → prod-Prop (pair _ (H t)) (is-lower-bound-fin-Prop P t))
      ( antisymmetric-leq-Fin (l y q) (m x p))

abstract
  is-prop-minimal-element-Fin :
    {l : Level} {k : ℕ} (P : Fin k → UU l) →
    ((x : Fin k) → is-prop (P x)) → is-prop (minimal-element-Fin P)
  is-prop-minimal-element-Fin P H =
    is-prop-all-elements-equal (all-elements-equal-minimal-element-Fin P H)

minimal-element-Fin-Prop :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → ((x : Fin k) → is-prop (P x)) →
  UU-Prop l
pr1 (minimal-element-Fin-Prop P H) = minimal-element-Fin P
pr2 (minimal-element-Fin-Prop P H) = is-prop-minimal-element-Fin P H

is-lower-bound-inl-Fin :
  {l : Level} {k : ℕ} {P : Fin (succ-ℕ k) → UU l} {x : Fin k} →
  is-lower-bound-Fin (P ∘ inl) x → is-lower-bound-Fin P (inl-Fin k x)
is-lower-bound-inl-Fin H (inl y) p = H y p
is-lower-bound-inl-Fin {l} {k} {P} {x} H (inr star) p =
  ( leq-neg-one-Fin (inl x))

minimal-element-decidable-subtype-Fin :
  {l : Level} {k : ℕ} {P : Fin k → UU l} →
  ((x : Fin k) → is-decidable (P x)) →
  Σ (Fin k) P → minimal-element-Fin P
pr1 (minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} d (pair (inl x) p)) =
  inl
    ( pr1
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr1
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  pr1
    ( pr2
      ( minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)))
pr2
  ( pr2
    ( minimal-element-decidable-subtype-Fin
      {l} {succ-ℕ k} d (pair (inl x) p))) =
  is-lower-bound-inl-Fin (pr2 (pr2 m))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) (pair x p)
minimal-element-decidable-subtype-Fin {l} {succ-ℕ k} {P} d (pair (inr star) p)
  with
  is-decidable-Σ-Fin (λ t → d (inl t))
... | inl t =
  pair
    ( inl (pr1 m))
    ( pair
      ( pr1 (pr2 m))
      ( is-lower-bound-inl-Fin (pr2 (pr2 m))))
  where
  m = minimal-element-decidable-subtype-Fin (λ x' → d (inl x')) t
... | inr f =
  pair
    ( inr star)
    ( pair p g)
  where
  g : (y : Fin (succ-ℕ k)) → P y → leq-Fin (neg-one-Fin {k}) y
  g (inl y) q = ex-falso (f (pair y q))
  g (inr star) q = refl-leq-Fin (neg-one-Fin {k})
```

### Global choice

```agda
global-choice-decidable-subtype-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU-Prop l) →
  ((x : Fin k) → is-decidable (type-Prop (P x))) →
  global-choice (type-subtype P)
global-choice-decidable-subtype-Fin {l} {zero-ℕ} P d t =
  ex-falso (apply-universal-property-trunc-Prop t empty-Prop pr1)
global-choice-decidable-subtype-Fin {l} {succ-ℕ k} P d t =
  map-Σ
    ( λ x → type-Prop (P x))
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( global-choice-total-Q
      ( functor-trunc-Prop
        ( map-Σ
          ( type-Prop ∘ Q)
          ( nat-Fin)
          ( λ x → tr (type-Prop ∘ P) (inv (issec-nat-Fin x))))
        ( t)))
  where
  Q : ℕ → UU-Prop l
  Q n = P (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (type-Prop (Q n))
  is-decidable-Q n = d (mod-succ-ℕ k n)
  global-choice-total-Q : global-choice (type-subtype Q)
  global-choice-total-Q =
    global-choice-decidable-subtype-ℕ Q is-decidable-Q
```

```agda
abstract
  elim-trunc-decidable-fam-Fin :
    {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
    ((x : Fin k) → is-decidable (B x)) →
    type-trunc-Prop (Σ (Fin k) B) → Σ (Fin k) B
  elim-trunc-decidable-fam-Fin {l1} {zero-ℕ} {B} d y =
    ex-falso (is-empty-type-trunc-Prop pr1 y)
  elim-trunc-decidable-fam-Fin {l1} {succ-ℕ k} {B} d y
    with d (inr star)
  ... | inl x = pair (inr star) x
  ... | inr f =
    map-Σ-map-base inl B
      ( elim-trunc-decidable-fam-Fin {l1} {k} {B ∘ inl}
        ( λ x → d (inl x))
        ( map-equiv-trunc-Prop
          ( ( ( right-unit-law-coprod-is-empty
                ( Σ (Fin k) (B ∘ inl))
                ( B (inr star)) f) ∘e
              ( equiv-coprod id-equiv (left-unit-law-Σ (B ∘ inr)))) ∘e
            ( right-distributive-Σ-coprod (Fin k) unit B))
          ( y)))
```
