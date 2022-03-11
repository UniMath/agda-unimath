# Orbits of permutations


```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.orbits-permutations where

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; commutative-add-ℕ)
open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ; ℕ-Set)
open import elementary-number-theory.euclidean-division-natural-numbers using
  ( remainder-euclidean-division-ℕ; strict-upper-bound-remainder-euclidean-division-ℕ;
    quotient-euclidean-division-ℕ; eq-euclidean-division-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using (mul-ℕ)
open import elementary-number-theory.decidable-dependent-pair-types using
  ( is-decidable-bounded-Σ-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( contradiction-le-ℕ; concatenate-leq-le-ℕ; concatenate-le-leq-ℕ; le-ℕ; succ-le-ℕ; _≤-ℕ_;
    is-nonzero-le-ℕ; is-decidable-le-ℕ; is-decidable-leq-ℕ; decide-leq-ℕ; le-leq-neq-ℕ; leq-le-ℕ;
    leq-le-succ-ℕ; subtraction-leq-ℕ; transitive-leq-ℕ; leq-mul-is-nonzero-ℕ)
open import elementary-number-theory.iterating-functions using
  ( iterate; iterate-add-ℕ)
open import elementary-number-theory.lower-bounds-natural-numbers using (is-lower-bound-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; succ-ℕ; zero-ℕ; is-nonzero-ℕ; is-nonzero-succ-ℕ; is-successor-ℕ; is-successor-is-nonzero-ℕ)
open import elementary-number-theory.well-ordering-principle-natural-numbers using
  ( minimal-element-ℕ; well-ordering-principle-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inr-inl)
open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-equiv; is-prop-has-decidable-equality;
    has-decidable-equality-Σ)
open import foundation.decidable-types using (is-decidable; is-decidable-Prop; is-decidable-trunc-Prop-is-merely-decidable)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.double-negation using (¬¬)
open import foundation.empty-types using (ex-falso)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (_≃_; map-equiv; inv-equiv; map-inv-is-equiv)
open import foundation.equivalence-relations using (Eq-Rel; prop-Eq-Rel; type-Eq-Rel)
open import foundation.equivalence-classes using
  ( large-set-quotient; large-quotient-Set; quotient-map-large-set-quotient;
    is-surjective-quotient-map-large-set-quotient; type-class-large-set-quotient;
    class-large-set-quotient; related-eq-quotient; is-equiv-related-eq-quotient)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬; reductio-ad-absurdum)
open import foundation.propositions using (UU-Prop; eq-is-prop; is-prop-type-Prop)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop;
    trunc-Prop; unit-trunc-Prop; all-elements-equal-type-trunc-Prop)
open import foundation.sets using (Id-Prop)
open import foundation.universe-levels using (Level; UU; lzero)

open import foundation-core.embeddings using (is-emb)
open import foundation-core.fibers-of-maps using (fib)

open import univalent-combinatorics.counting using
  ( count; count-Fin; equiv-count; number-of-elements-count)
open import univalent-combinatorics.equality-standard-finite-types using (has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-type-UU-Fin-Level; UU-Fin-Level; type-UU-Fin-Level; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.image-of-maps using (is-finite-codomain)
open import univalent-combinatorics.pigeonhole-principle using (two-points-same-image-le-count)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-injective-nat-Fin; nat-Fin; succ-Fin; strict-upper-bound-nat-Fin)
```

## Idea

The orbit of a point `x` for a permutation `f` is the set of point obtained by iterating `f` on `x`.

...

## Definitions

```agda
module _
  {l : Level} (X : UU l) (eX : count X) (f : X ≃ X) (a : X)
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

  point1-iterate-ℕ : ℕ
  point1-iterate-ℕ = nat-Fin (pr1 two-points-iterate-Fin)

  point2-iterate-ℕ : ℕ
  point2-iterate-ℕ = nat-Fin (pr1 (pr2 two-points-iterate-Fin))

  neq-points-iterate-ℕ : ¬ (Id point1-iterate-ℕ point2-iterate-ℕ)
  neq-points-iterate-ℕ = λ p → pr2 (pr2 (pr2 two-points-iterate-Fin)) (is-injective-nat-Fin p)
 
  two-points-iterate-ordered-ℕ :
    coprod (point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ) (point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ) →
      Σ ℕ (λ n →
        Σ ℕ (λ m → (le-ℕ m n) × (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
  two-points-iterate-ordered-ℕ (inl p) =
    pair point2-iterate-ℕ
      ( pair point1-iterate-ℕ
        ( pair (le-leq-neq-ℕ p neq-points-iterate-ℕ)
          ( inv (pr1 (pr2 (pr2 two-points-iterate-Fin))))))
  two-points-iterate-ordered-ℕ (inr p) =
    pair point1-iterate-ℕ
      ( pair point2-iterate-ℕ
        ( pair (le-leq-neq-ℕ p λ e → neq-points-iterate-ℕ (inv e))
          ( pr1 (pr2 (pr2 two-points-iterate-Fin)))))

  leq-greater-point-number-elements :
    (p : coprod (point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ) (point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ)) →
    (pr1 (two-points-iterate-ordered-ℕ p) ≤-ℕ number-of-elements-count eX)
  leq-greater-point-number-elements (inl p) =
    leq-le-succ-ℕ {pr1 (two-points-iterate-ordered-ℕ (inl p))} (strict-upper-bound-nat-Fin (pr1 (pr2 two-points-iterate-Fin)))
  leq-greater-point-number-elements (inr p) =
    leq-le-succ-ℕ {pr1 (two-points-iterate-ordered-ℕ (inr p))} (strict-upper-bound-nat-Fin (pr1 two-points-iterate-Fin))
          
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
      ( two-points-iterate-ordered-ℕ (decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))

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

  leq-first-point-min-reporting-succ-number-elements : first-point-min-repeating ≤-ℕ (number-of-elements-count eX)
  leq-first-point-min-reporting-succ-number-elements =
    transitive-leq-ℕ
      ( first-point-min-repeating)
      ( pr1 (two-points-iterate-ordered-ℕ (decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ)))
      ( number-of-elements-count eX)
      ( is-lower-bound-min-reporting
        (pr1 (two-points-iterate-ordered-ℕ (decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ)))
        (pr2 (two-points-iterate-ordered-ℕ (decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))))
      ( leq-greater-point-number-elements (decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))

  same-image-iterate-min-reporting :
    Id (iterate first-point-min-repeating (map-equiv f) a) (iterate second-point-min-repeating (map-equiv f) a)
  same-image-iterate-min-reporting = pr2 (pr2 (pr1 (pr2 min-repeating)))
  
  not-not-eq-second-point-zero-min-reporting : ¬¬ (Id second-point-min-repeating zero-ℕ)
  not-not-eq-second-point-zero-min-reporting np =
    contradiction-le-ℕ
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
                  ( same-image-iterate-min-reporting)))))))
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
  has-finite-orbits' (inr np) = ex-falso (not-not-eq-second-point-zero-min-reporting np)
      
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

  leq-has-finite-orbits-number-elements : (pr1 has-finite-orbits) ≤-ℕ (number-of-elements-count eX)
  leq-has-finite-orbits-number-elements = cases-second-point (has-decidable-equality-ℕ second-point-min-repeating zero-ℕ)
    where
    cases-second-point : is-decidable (Id second-point-min-repeating zero-ℕ) →
      (pr1 has-finite-orbits) ≤-ℕ (number-of-elements-count eX)
    cases-second-point (inl p) =
      tr
        ( λ x → (pr1 (has-finite-orbits' x)) ≤-ℕ (number-of-elements-count eX))
        { x = inl p} {y = has-decidable-equality-ℕ second-point-min-repeating zero-ℕ}
        ( eq-is-prop (is-prop-type-Prop (is-decidable-Prop (Id-Prop ℕ-Set second-point-min-repeating zero-ℕ))))
        ( leq-first-point-min-reporting-succ-number-elements)
    cases-second-point (inr np) = ex-falso (not-not-eq-second-point-zero-min-reporting np)
                       
  mult-has-finite-orbits :
    (k : ℕ) → Id (iterate (mul-ℕ k (pr1 has-finite-orbits)) (map-equiv f) a) a
  mult-has-finite-orbits zero-ℕ = refl
  mult-has-finite-orbits (succ-ℕ k) =
    ( iterate-add-ℕ (mul-ℕ k (pr1 has-finite-orbits)) (pr1 has-finite-orbits) (map-equiv f) a) ∙
      ( ap (iterate (mul-ℕ k (pr1 has-finite-orbits)) (map-equiv f)) (pr2 (pr2 has-finite-orbits)) ∙
        ( mult-has-finite-orbits k))
      
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
                      ( mult-has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a k)))))))
    where
    has-finite-orbits-a : (h : Fin n ≃ type-UU-Fin-Level X) → Σ ℕ (λ l → (is-nonzero-ℕ l) × Id (iterate l (map-equiv f) a) a)
    has-finite-orbits-a h = has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a
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

  is-decidable-same-orbits : (a b : type-UU-Fin-Level X) → is-decidable (type-Eq-Rel same-orbits a b) 
  is-decidable-same-orbits a b =
    apply-universal-property-trunc-Prop
      ( mere-equiv-UU-Fin-Level X)
      ( is-decidable-Prop (prop-Eq-Rel same-orbits a b))
      ( λ h → is-decidable-trunc-Prop-is-merely-decidable
        ( Σ ℕ (λ k → Id (iterate k (map-equiv f) a) b))
        ( unit-trunc-Prop
          ( is-decidable-iterate-is-decidable-bounded h a b
            ( is-decidable-bounded-Σ-ℕ n (λ z → z ≤-ℕ n) (λ z → Id (iterate z (map-equiv f) a) b)
              ( λ z → is-decidable-leq-ℕ z n)
              ( λ z → has-decidable-equality-equiv (inv-equiv h) has-decidable-equality-Fin (iterate z (map-equiv f) a) b)
              ( λ m p → p)))))
    where
    is-decidable-iterate-is-decidable-bounded : (Fin n ≃ type-UU-Fin-Level X) → (a b : type-UU-Fin-Level X) →
      is-decidable (Σ ℕ (λ m → (m ≤-ℕ n) × (Id (iterate m (map-equiv f) a) b))) →
      is-decidable (Σ ℕ (λ m → Id (iterate m (map-equiv f) a) b))
    is-decidable-iterate-is-decidable-bounded h a b (inl p) = inl (pair (pr1 p) (pr2 (pr2 p)))
    is-decidable-iterate-is-decidable-bounded h a b (inr np) =
      inr (λ p → np
        (pair
          ( remainder-euclidean-division-ℕ m (pr1 p))
          (pair
            ( leq-le-ℕ
              { x = remainder-euclidean-division-ℕ m (pr1 p)}
              ( concatenate-le-leq-ℕ
                { y = m}
                ( strict-upper-bound-remainder-euclidean-division-ℕ
                  ( m)
                  ( pr1 p)
                  ( pr1 (pr2 (has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a))))
              ( leq-has-finite-orbits-number-elements (type-UU-Fin-Level X) (pair n h) f a)))
            ( (ap
               ( iterate (remainder-euclidean-division-ℕ m (pr1 p)) (map-equiv f))
               ( inv
                 ( mult-has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a (quotient-euclidean-division-ℕ m (pr1 p))))) ∙
              ( (inv
                ( iterate-add-ℕ
                  ( remainder-euclidean-division-ℕ m (pr1 p))
                  ( mul-ℕ (quotient-euclidean-division-ℕ m (pr1 p)) m)
                  ( map-equiv f)
                  ( a))) ∙
                ( (ap
                  ( λ x → iterate x (map-equiv f) a)
                  ( (commutative-add-ℕ
                    ( remainder-euclidean-division-ℕ m (pr1 p))
                    ( mul-ℕ (quotient-euclidean-division-ℕ m (pr1 p)) m)) ∙
                    ( eq-euclidean-division-ℕ m (pr1 p)))) ∙
                  ( pr2 p)))))))
      where
      m : ℕ
      m = pr1 (has-finite-orbits (type-UU-Fin-Level X) (pair n h) f a)

  has-finite-number-orbits : is-finite (large-set-quotient same-orbits)
  has-finite-number-orbits =
    is-finite-codomain
      ( is-finite-type-UU-Fin-Level X)
      ( is-surjective-quotient-map-large-set-quotient same-orbits)
      ( apply-universal-property-trunc-Prop
        ( mere-equiv-UU-Fin-Level X)
        ( pair (has-decidable-equality (large-set-quotient same-orbits)) is-prop-has-decidable-equality)
      ( λ h T1 T2 →
        ( apply-universal-property-trunc-Prop
          ( (pr2 T1))
          ( is-decidable-Prop (Id-Prop (large-quotient-Set same-orbits) T1 T2))
          ( λ (pair t1 p1) → cases-decidable-equality T1 T2 t1
            ( eq-pair-Σ (inv p1) (all-elements-equal-type-trunc-Prop _ _))
            ( apply-universal-property-trunc-Prop
              ( pr2 T2)
              ( is-decidable-Prop (class-large-set-quotient same-orbits T2 t1))
              ( λ (pair t2 p2) →
               ( cases-decidable-type-class-large-set-quotient T2 t1 t2
                 ( eq-pair-Σ (inv p2) (all-elements-equal-type-trunc-Prop _ _))
                 ( is-decidable-same-orbits t2 t1))))))))
    where
    cases-decidable-equality :
      (T1 T2 : large-set-quotient same-orbits) (t1 : type-UU-Fin-Level X) →
      Id T1 (quotient-map-large-set-quotient same-orbits t1) → is-decidable (type-class-large-set-quotient same-orbits T2 t1) →
      is-decidable (Id T1 T2)
    cases-decidable-equality T1 T2 t1 p1 (inl p) =
      inl (p1 ∙ map-inv-is-equiv (is-equiv-related-eq-quotient same-orbits t1 T2) p)
    cases-decidable-equality T1 T2 t1 p1 (inr np) =
      inr (λ p → np (related-eq-quotient same-orbits t1 T2 (inv p1 ∙ p)))
    cases-decidable-type-class-large-set-quotient :
      (T2 : large-set-quotient same-orbits) (t1 t2 : type-UU-Fin-Level X) →
      Id T2 (quotient-map-large-set-quotient same-orbits t2) → is-decidable (type-Eq-Rel same-orbits t2 t1) →
      is-decidable (type-class-large-set-quotient same-orbits T2 t1)
    cases-decidable-type-class-large-set-quotient T2 t1 t2 p2 (inl p) =
      inl (tr (λ x → type-class-large-set-quotient same-orbits x t1) (inv p2) p)
    cases-decidable-type-class-large-set-quotient T2 t1 t2 p2 (inr np) =
      inr (λ p → np (tr (λ x → type-class-large-set-quotient same-orbits x t1) p2 p))
    is-decidable-iterate-is-decidable-bounded : (Fin n ≃ type-UU-Fin-Level X) → (t1 t2 : type-UU-Fin-Level X) →
      is-decidable (Σ ℕ (λ m → (m ≤-ℕ n) × (Id (iterate m (map-equiv f) t2) t1))) →
      is-decidable (Σ ℕ (λ m → Id (iterate m (map-equiv f) t2) t1))
    is-decidable-iterate-is-decidable-bounded h t1 t2 (inl p) = inl (pair (pr1 p) (pr2 (pr2 p)))
    is-decidable-iterate-is-decidable-bounded h t1 t2 (inr np) =
      inr (λ p → np
        (pair
          ( remainder-euclidean-division-ℕ m (pr1 p))
          (pair
            ( leq-le-ℕ
              { x = remainder-euclidean-division-ℕ m (pr1 p)}
              ( concatenate-le-leq-ℕ
                { y = m}
                ( strict-upper-bound-remainder-euclidean-division-ℕ
                  ( m)
                  ( pr1 p)
                  ( pr1 (pr2 (has-finite-orbits (type-UU-Fin-Level X) (pair n h) f t2))))
              ( leq-has-finite-orbits-number-elements (type-UU-Fin-Level X) (pair n h) f t2)))
            ( (ap
               ( iterate (remainder-euclidean-division-ℕ m (pr1 p)) (map-equiv f))
               ( inv
                 ( mult-has-finite-orbits (type-UU-Fin-Level X) (pair n h) f t2 (quotient-euclidean-division-ℕ m (pr1 p))))) ∙
              ( (inv
                ( iterate-add-ℕ
                  ( remainder-euclidean-division-ℕ m (pr1 p))
                  ( mul-ℕ (quotient-euclidean-division-ℕ m (pr1 p)) m)
                  ( map-equiv f)
                  ( t2))) ∙
                ( (ap
                  ( λ x → iterate x (map-equiv f) t2)
                  ( (commutative-add-ℕ
                    ( remainder-euclidean-division-ℕ m (pr1 p))
                    ( mul-ℕ (quotient-euclidean-division-ℕ m (pr1 p)) m)) ∙
                    ( eq-euclidean-division-ℕ m (pr1 p)))) ∙
                  ( pr2 p)))))))
      where
      m : ℕ
      m = pr1 (has-finite-orbits (type-UU-Fin-Level X) (pair n h) f t2)
```
