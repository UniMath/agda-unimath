# Orbits


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.orbits where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using (mul-ℕ)
open import elementary-number-theory.decidable-dependent-pair-types using
  ( is-decidable-bounded-Σ-ℕ)
open import elementary-number-theory.equality-natural-numbers using (has-decidable-equality-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( contradiction-le-ℕ; le-ℕ; succ-le-ℕ; _≤-ℕ_; is-nonzero-le-ℕ; is-decidable-le-ℕ; decide-leq-ℕ;
    le-leq-neq-ℕ; leq-le-ℕ; subtraction-leq-ℕ; leq-mul-is-nonzero-ℕ)
open import elementary-number-theory.iterating-functions using
  ( iterate; iterate-add-ℕ)
open import elementary-number-theory.lower-bounds-natural-numbers using (is-lower-bound-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; succ-ℕ; zero-ℕ; is-nonzero-ℕ; is-nonzero-succ-ℕ; is-successor-ℕ; is-successor-is-nonzero-ℕ)
open import elementary-number-theory.well-ordering-principle-natural-numbers using
  ( minimal-element-ℕ; well-ordering-principle-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inr-inl)
open import foundation.decidable-equality using (has-decidable-equality-equiv)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using (_≃_; map-equiv; inv-equiv)
open import foundation.equivalence-relations using (Eq-Rel)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬; reductio-ad-absurdum)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop;
    trunc-Prop; unit-trunc-Prop)
open import foundation.universe-levels using (Level; UU; lzero)

open import foundation-core.embeddings using (is-emb)
open import foundation-core.fibers-of-maps using (fib)

open import univalent-combinatorics.counting using
  ( count; count-Fin; equiv-count; number-of-elements-count)
open import univalent-combinatorics.equality-standard-finite-types using (has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using (UU-Fin-Level; type-UU-Fin-Level; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.pigeonhole-principle using (two-points-same-image-le-count)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-injective-nat-Fin; nat-Fin; succ-Fin)
```

## Idea

The orbit of a point `x` for a permutation `f` is the set of point obtained by iterating `f` on `x`.

...

## Definitions

```agda
module _
  {l : Level} (X : UU l) (eX : count X) (f : X ≃ X) (a : X)
  where
  
  min-repeating :
    minimal-element-ℕ
      (λ n →
        Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
  min-repeating =
    well-ordering-principle-ℕ
      ( (λ n →
        Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a)))))
      ( λ n →
        is-decidable-bounded-Σ-ℕ n ( λ m → le-ℕ m n)
          ( λ m → (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a)))
          ( λ m → is-decidable-le-ℕ m n)
          ( λ m →
            has-decidable-equality-equiv
              ( inv-equiv (equiv-count eX))
              ( has-decidable-equality-Fin)
              ( iterate n (map-equiv f) a)
              ( iterate m (map-equiv f) a))
          ( λ m p → leq-le-ℕ {m} {n} p))
      ( two-points-iterate-ordered-ℕ (decide-leq-ℕ first-point second-point))
    where
    two-points-iterate-Fin :
      Σ (Fin (succ-ℕ (number-of-elements-count eX)))
        ( λ k1 → Σ (Fin (succ-ℕ (number-of-elements-count eX)))
          ( λ k2 → (Id (iterate (nat-Fin k1) (map-equiv f) a) (iterate (nat-Fin k2) (map-equiv f) a)) × ¬ (Id k1 k2)))
    two-points-iterate-Fin =
      two-points-same-image-le-count
        ( count-Fin (succ-ℕ (number-of-elements-count eX)))
        ( eX)
        ( λ k → iterate (nat-Fin k) (map-equiv f) a)
        ( succ-le-ℕ (number-of-elements-count eX))
    first-point : ℕ
    first-point = nat-Fin (pr1 two-points-iterate-Fin)
    second-point : ℕ
    second-point = nat-Fin (pr1 (pr2 two-points-iterate-Fin))
    neq-points : ¬ (Id first-point second-point)
    neq-points = λ p → pr2 (pr2 (pr2 two-points-iterate-Fin)) (is-injective-nat-Fin p)
    two-points-iterate-ordered-ℕ :
      coprod (first-point ≤-ℕ second-point) (second-point ≤-ℕ first-point) →
        Σ ℕ (λ n →
          Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
    two-points-iterate-ordered-ℕ (inl p) =
      pair second-point
        ( pair first-point
          ( pair (le-leq-neq-ℕ p neq-points)
            ( inv (pr1 (pr2 (pr2 two-points-iterate-Fin))))))
    two-points-iterate-ordered-ℕ (inr p) =
      pair first-point
        ( pair second-point
          ( pair (le-leq-neq-ℕ p λ e → neq-points (inv e))
            ( pr1 (pr2 (pr2 two-points-iterate-Fin)))))

  first-point-min-repeating : ℕ
  first-point-min-repeating = pr1 min-repeating
    
  second-point-min-repeating : ℕ
  second-point-min-repeating = pr1 (pr1 (pr2 min-repeating))

  le-min-reporting : le-ℕ second-point-min-repeating first-point-min-repeating
  le-min-reporting = pr1 (pr2 (pr1 (pr2 min-repeating)))

  is-lower-bound-min-reporting :
    is-lower-bound-ℕ
      ( λ n → Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
      ( first-point-min-repeating)
  is-lower-bound-min-reporting = pr2 (pr2 min-repeating)

  same-image-iterate-min-reporting :
    Id (iterate first-point-min-repeating (map-equiv f) a) (iterate second-point-min-repeating (map-equiv f) a)
  same-image-iterate-min-reporting = pr2 (pr2 (pr1 (pr2 min-repeating)))
  
  has-finite-orbits' : is-decidable (Id second-point-min-repeating zero-ℕ) →
    Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits' (inl p) =
    pair
      ( first-point-min-repeating)
      ( pair
        ( is-nonzero-le-ℕ second-point-min-repeating first-point-min-repeating le-min-reporting)
        ( tr
          ( λ x → Id (iterate first-point-min-repeating (map-equiv f) a) (iterate x (map-equiv f) a))
          ( p)
          ( same-image-iterate-min-reporting)))
  has-finite-orbits' (inr np) =
    ex-falso
      ( contradiction-le-ℕ
        ( pred-first)
        ( first-point-min-repeating)
        ( tr (λ x → le-ℕ pred-first x) (inv equality-pred-first) (succ-le-ℕ pred-first))
        ( is-lower-bound-min-reporting
          ( pred-first)
          ( pair
            ( pred-second)
            ( pair
              ( tr
                ( λ x → le-ℕ (succ-ℕ pred-second) x)
                ( equality-pred-first)
                ( tr (λ x → le-ℕ x first-point-min-repeating) equality-pred-second le-min-reporting))
              ( is-injective-map-equiv
                ( f)
                ( tr
                  ( λ x → Id (iterate x (map-equiv f) a) (iterate (succ-ℕ pred-second) (map-equiv f) a))
                  ( equality-pred-first)
                  ( tr
                    ( λ x → Id (iterate first-point-min-repeating (map-equiv f) a) (iterate x (map-equiv f) a))
                    ( equality-pred-second)
                    ( same-image-iterate-min-reporting))))))))
    where
    is-successor-first-point-min-repeating : is-successor-ℕ first-point-min-repeating
    is-successor-first-point-min-repeating =
      is-successor-is-nonzero-ℕ
        ( is-nonzero-le-ℕ second-point-min-repeating first-point-min-repeating le-min-reporting)
    pred-first : ℕ
    pred-first = pr1 is-successor-first-point-min-repeating
    equality-pred-first : Id first-point-min-repeating (succ-ℕ pred-first)
    equality-pred-first = pr2 is-successor-first-point-min-repeating
    is-successor-second-point-min-repeating : is-successor-ℕ second-point-min-repeating
    is-successor-second-point-min-repeating = is-successor-is-nonzero-ℕ np
    pred-second : ℕ
    pred-second = pr1 is-successor-second-point-min-repeating
    equality-pred-second : Id second-point-min-repeating (succ-ℕ pred-second)
    equality-pred-second = pr2 is-successor-second-point-min-repeating

  has-finite-orbits : Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits = has-finite-orbits' (has-decidable-equality-ℕ second-point-min-repeating zero-ℕ)

module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (f : (type-UU-Fin-Level X ≃ type-UU-Fin-Level X)) 
  where

  same-orbits : Eq-Rel l (type-UU-Fin-Level X)
  (pr1 same-orbits) a b = trunc-Prop (Σ ℕ (λ k → Id (iterate k (map-equiv f) a) b))
  pr1 (pr2 same-orbits) = unit-trunc-Prop (pair 0 refl)
  pr1 (pr2 (pr2 same-orbits)) {a} {b} P =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits b a)
      ( λ (pair k p) →
        apply-universal-property-trunc-Prop
          ( mere-equiv-UU-Fin-Level X)
          ( pr1 same-orbits b a)
          ( λ h →
            unit-trunc-Prop
              (pair
                ( pr1 (lemma h k))
                ( ap (iterate (pr1 (lemma h k)) (map-equiv f)) (inv p) ∙
                  ( inv (iterate-add-ℕ (pr1 (lemma h k)) k (map-equiv f) a) ∙
                    ( ap (λ x → iterate x (map-equiv f) a) (pr2 (lemma h k)) ∙
                      ( multiple-has-finite-orbits-a h k)))))))
    where
    has-finite-orbits-a : (h : Fin n ≃ type-UU-Fin-Level X) → Σ ℕ (λ l → (is-nonzero-ℕ l) × Id (iterate l (map-equiv f) a) a)
    has-finite-orbits-a h = has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a
    multiple-has-finite-orbits-a :
      (h : Fin n ≃ type-UU-Fin-Level X) (k : ℕ) → Id (iterate (mul-ℕ k (pr1 (has-finite-orbits-a h))) (map-equiv f) a) a
    multiple-has-finite-orbits-a h zero-ℕ = refl
    multiple-has-finite-orbits-a h (succ-ℕ k) =
      ( iterate-add-ℕ (mul-ℕ k (pr1 (has-finite-orbits-a h))) (pr1 (has-finite-orbits-a h)) (map-equiv f) a) ∙
        ( ap (iterate (mul-ℕ k (pr1 (has-finite-orbits-a h))) (map-equiv f)) (pr2 (pr2 (has-finite-orbits-a h))) ∙
          ( multiple-has-finite-orbits-a h k))
    lemma : (h : Fin n ≃ type-UU-Fin-Level X) (k : ℕ) →
      Σ ℕ (λ j → Id (add-ℕ j k) (mul-ℕ k (pr1 (has-finite-orbits-a h))))
    lemma h k =
      subtraction-leq-ℕ
        ( k)
        ( mul-ℕ k (pr1 (has-finite-orbits-a h)))
        ( leq-mul-is-nonzero-ℕ (pr1 (has-finite-orbits-a h)) k (pr1 (pr2 (has-finite-orbits-a h))))
  pr2 (pr2 (pr2 same-orbits)) {a} {b} {c} P Q =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits a c)
      ( λ (pair k1 p) →
        apply-universal-property-trunc-Prop
          ( Q)
          ( (pr1 same-orbits a c))
          ( λ (pair k2 q) →
            ( unit-trunc-Prop (pair
              ( add-ℕ k2 k1)
              ( (iterate-add-ℕ k2 k1 (map-equiv f) a) ∙
                ( (ap (iterate k2 (map-equiv f)) p ∙ q)))))))
```
