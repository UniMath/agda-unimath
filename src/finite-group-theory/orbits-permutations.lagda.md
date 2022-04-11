# Orbits of permutations

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-group-theory.orbits-permutations where

open import finite-group-theory.transpositions using
  ( transposition; standard-transposition; map-standard-transposition;
    is-fixed-point-standard-transposition;
    right-computation-standard-transposition;
    left-computation-standard-transposition;
    is-involution-map-transposition; permutation-list-transpositions;
    two-elements-transposition)

open import elementary-number-theory.addition-natural-numbers using
  ( add-ℕ; commutative-add-ℕ)
open import elementary-number-theory.decidable-types using
  ( is-decidable-bounded-Σ-ℕ)
open import elementary-number-theory.equality-natural-numbers using
  ( has-decidable-equality-ℕ; ℕ-Set)
open import elementary-number-theory.euclidean-division-natural-numbers using
  ( remainder-euclidean-division-ℕ;
    strict-upper-bound-remainder-euclidean-division-ℕ;
    quotient-euclidean-division-ℕ; eq-euclidean-division-ℕ)
open import elementary-number-theory.inequality-natural-numbers using
  ( contradiction-le-ℕ; concatenate-leq-le-ℕ; concatenate-le-leq-ℕ; le-ℕ;
    succ-le-ℕ; _≤-ℕ_; is-nonzero-le-ℕ; is-decidable-le-ℕ; is-decidable-leq-ℕ;
    decide-leq-ℕ; le-leq-neq-ℕ; leq-le-ℕ; leq-le-succ-ℕ; subtraction-leq-ℕ;
    transitive-leq-ℕ; leq-mul-is-nonzero-ℕ; subtraction-le-ℕ; le-subtraction-ℕ;
    transitive-le-ℕ; le-succ-ℕ)
open import elementary-number-theory.iterating-functions using
  ( iterate; iterate-add-ℕ)
open import elementary-number-theory.lower-bounds-natural-numbers using
  ( is-lower-bound-ℕ)
open import
  elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-two-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)
open import elementary-number-theory.natural-numbers using
  ( ℕ; succ-ℕ; zero-ℕ; is-nonzero-ℕ; is-nonzero-succ-ℕ; is-successor-ℕ;
    is-successor-is-nonzero-ℕ; is-zero-ℕ)
open import
  elementary-number-theory.well-ordering-principle-natural-numbers using
  ( minimal-element-ℕ; well-ordering-principle-ℕ; minimal-element-ℕ-Prop)

open import foundation.automorphisms using (Aut)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using
  ( coprod; inl; inr; neq-inr-inl; coprod-Prop)
open import foundation.decidable-equality using
  ( has-decidable-equality; has-decidable-equality-equiv;
    is-prop-has-decidable-equality; has-decidable-equality-Σ)
open import foundation.decidable-maps using (is-decidable-map)
open import foundation.decidable-propositions using
  ( decidable-Prop; type-decidable-Prop)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-Prop;
    is-decidable-trunc-Prop-is-merely-decidable; is-decidable-coprod;
    is-decidable-prod; is-decidable-neg; is-prop-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.double-negation using (¬¬)
open import foundation.embeddings using (is-emb)
open import foundation.empty-types using (ex-falso; empty-Prop)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalence-classes using
  ( large-set-quotient; large-quotient-Set; quotient-map-large-set-quotient;
    is-surjective-quotient-map-large-set-quotient;
    type-class-large-set-quotient; class-large-set-quotient;
    related-eq-quotient; is-equiv-related-eq-quotient;
    transitive-type-class-large-set-quotient; eq-effective-quotient';
    is-prop-type-class-large-set-quotient; is-decidable-type-class-large-set-quotient-is-decidable)
open import foundation.equivalence-relations using
  ( Eq-Rel; prop-Eq-Rel; type-Eq-Rel; refl-Eq-Rel; symm-Eq-Rel; trans-Eq-Rel)
open import foundation.equivalences using
  ( _≃_; _∘e_; htpy-equiv; map-equiv; inv-equiv; map-inv-is-equiv;
    is-equiv-has-inverse; eq-htpy-equiv; left-inverse-law-equiv;
    right-inverse-law-equiv; map-inv-equiv; id-equiv; htpy-eq-equiv)
open import foundation.fibers-of-maps using (fib)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_)
open import foundation.functoriality-coproduct-types using (map-coprod)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬; reductio-ad-absurdum)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop;
    trunc-Prop; unit-trunc-Prop; all-elements-equal-type-trunc-Prop;
    type-trunc-Prop; universal-property-trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; eq-is-prop; is-prop-is-prop; is-prop-type-Prop; is-equiv-is-prop;
    is-prop; is-prop-Σ)
open import foundation.sets using (Id-Prop)
open import foundation.unit-type using (star; unit)
open import foundation.univalence using (eq-equiv)
open import foundation.universal-property-propositional-truncation using
  ( htpy-is-propositional-truncation)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.2-element-decidable-subtypes using
  ( standard-2-Element-Decidable-Subtype)
open import univalent-combinatorics.2-element-types using
  ( is-involution-aut-Fin-two-ℕ)
open import univalent-combinatorics.counting using
  ( count; count-Fin; equiv-count; inv-equiv-count; map-equiv-count;
    map-inv-equiv-count; number-of-elements-count; has-decidable-equality-count)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin)
open import univalent-combinatorics.finite-types using
  ( is-finite; is-finite-type-UU-Fin-Level; UU-Fin-Level; type-UU-Fin-Level;
    mere-equiv-UU-Fin-Level; number-of-elements-is-finite;
    number-of-elements-has-finite-cardinality; has-finite-cardinality-is-finite;
    has-finite-cardinality-count; all-elements-equal-has-finite-cardinality;
    has-cardinality)
open import univalent-combinatorics.image-of-maps using (is-finite-codomain)
open import univalent-combinatorics.lists using (list; length-list; cons; nil)
open import univalent-combinatorics.pigeonhole-principle using
  ( two-points-same-image-le-count)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; is-injective-nat-Fin; nat-Fin; succ-Fin; strict-upper-bound-nat-Fin;
    zero-Fin; equiv-succ-Fin)
```

## Idea

The orbit of a point `x` for a permutation `f` is the set of point obtained by iterating `f` on `x`.

## Properties

### For type equipped with a counting, orbits of permutations are finite

```agda
module _
  {l : Level} (X : UU l) (eX : count X) (f : Aut X) (a : X)
  where
  
  two-points-iterate-Fin :
    Σ ( Fin (succ-ℕ (number-of-elements-count eX)))
      ( λ k1 →
        Σ ( Fin (succ-ℕ (number-of-elements-count eX)))
          ( λ k2 →
            ( Id ( iterate (nat-Fin k1) (map-equiv f) a)
                 ( iterate (nat-Fin k2) (map-equiv f) a)) ×
            ¬ (Id k1 k2)))
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
  neq-points-iterate-ℕ p =
    pr2 (pr2 (pr2 two-points-iterate-Fin)) (is-injective-nat-Fin p)
 
  two-points-iterate-ordered-ℕ :
    coprod
      ( point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ)
      ( point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ) →
    Σ ( ℕ)
      ( λ n →
        Σ ( ℕ)
          ( λ m →
            ( le-ℕ m n) ×
            ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
  pr1 (two-points-iterate-ordered-ℕ (inl p)) = point2-iterate-ℕ
  pr1 (pr2 (two-points-iterate-ordered-ℕ (inl p))) = point1-iterate-ℕ
  pr1 (pr2 (pr2 (two-points-iterate-ordered-ℕ (inl p)))) =
    le-leq-neq-ℕ p neq-points-iterate-ℕ
  pr2 (pr2 (pr2 (two-points-iterate-ordered-ℕ (inl p)))) =
    inv (pr1 (pr2 (pr2 two-points-iterate-Fin)))
  pr1 (two-points-iterate-ordered-ℕ (inr p)) = point1-iterate-ℕ
  pr1 (pr2 (two-points-iterate-ordered-ℕ (inr p))) = point2-iterate-ℕ
  pr1 (pr2 (pr2 (two-points-iterate-ordered-ℕ (inr p)))) =
    le-leq-neq-ℕ p λ e → neq-points-iterate-ℕ (inv e)
  pr2 (pr2 (pr2 (two-points-iterate-ordered-ℕ (inr p)))) =
    pr1 (pr2 (pr2 two-points-iterate-Fin))

  leq-greater-point-number-elements :
    ( p :
      coprod
        ( point1-iterate-ℕ ≤-ℕ point2-iterate-ℕ)
        ( point2-iterate-ℕ ≤-ℕ point1-iterate-ℕ)) →
    pr1 (two-points-iterate-ordered-ℕ p) ≤-ℕ number-of-elements-count eX
  leq-greater-point-number-elements (inl p) =
    leq-le-succ-ℕ
      { pr1 (two-points-iterate-ordered-ℕ (inl p))}
      ( strict-upper-bound-nat-Fin (pr1 (pr2 two-points-iterate-Fin)))
  leq-greater-point-number-elements (inr p) =
    leq-le-succ-ℕ
      { pr1 (two-points-iterate-ordered-ℕ (inr p))}
      ( strict-upper-bound-nat-Fin (pr1 two-points-iterate-Fin))
          
  min-repeating :
    minimal-element-ℕ
      ( λ n →
        Σ ( ℕ)
          ( λ m →
            ( le-ℕ m n) ×
            ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
  min-repeating =
    well-ordering-principle-ℕ
      ( λ n →
        Σ ( ℕ)
          ( λ m →
            ( le-ℕ m n) ×
            ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
      ( λ n →
        is-decidable-bounded-Σ-ℕ n ( λ m → le-ℕ m n)
          ( λ m → (Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a)))
          ( λ m → is-decidable-le-ℕ m n)
          ( λ m →
            has-decidable-equality-count eX
              ( iterate n (map-equiv f) a)
              ( iterate m (map-equiv f) a))
          ( λ m p → leq-le-ℕ {m} {n} p))
      ( two-points-iterate-ordered-ℕ
        ( decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))

  first-point-min-repeating : ℕ
  first-point-min-repeating = pr1 min-repeating
    
  second-point-min-repeating : ℕ
  second-point-min-repeating = pr1 (pr1 (pr2 min-repeating))

  le-min-reporting : le-ℕ second-point-min-repeating first-point-min-repeating
  le-min-reporting = pr1 (pr2 (pr1 (pr2 min-repeating)))

  is-lower-bound-min-reporting :
    is-lower-bound-ℕ
      ( λ n →
        Σ ( ℕ)
          ( λ m →
            ( le-ℕ m n) ×
            ( Id (iterate n (map-equiv f) a) (iterate m (map-equiv f) a))))
      ( first-point-min-repeating)
  is-lower-bound-min-reporting = pr2 (pr2 min-repeating)

  leq-first-point-min-reporting-succ-number-elements :
    first-point-min-repeating ≤-ℕ (number-of-elements-count eX)
  leq-first-point-min-reporting-succ-number-elements =
    transitive-leq-ℕ
      ( first-point-min-repeating)
      ( pr1
        ( two-points-iterate-ordered-ℕ
          ( decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ)))
      ( number-of-elements-count eX)
      ( is-lower-bound-min-reporting
        ( pr1
          ( two-points-iterate-ordered-ℕ
            ( decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ)))
        ( pr2
          ( two-points-iterate-ordered-ℕ
            ( decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))))
      ( leq-greater-point-number-elements
        ( decide-leq-ℕ point1-iterate-ℕ point2-iterate-ℕ))

  same-image-iterate-min-reporting :
    Id ( iterate first-point-min-repeating (map-equiv f) a)
       ( iterate second-point-min-repeating (map-equiv f) a)
  same-image-iterate-min-reporting = pr2 (pr2 (pr1 (pr2 min-repeating)))
  
  abstract
    not-not-eq-second-point-zero-min-reporting :
      ¬¬ (Id second-point-min-repeating zero-ℕ)
    not-not-eq-second-point-zero-min-reporting np =
      contradiction-le-ℕ
        ( pred-first)
        ( first-point-min-repeating)
        ( tr
          ( λ x → le-ℕ pred-first x)
          ( inv equality-pred-first)
          ( succ-le-ℕ pred-first))
        ( is-lower-bound-min-reporting
          ( pred-first)
          ( pair
            ( pred-second)
            ( pair
              ( tr
                ( λ x → le-ℕ (succ-ℕ pred-second) x)
                ( equality-pred-first)
                ( tr
                  ( λ x → le-ℕ x first-point-min-repeating)
                  ( equality-pred-second)
                  ( le-min-reporting)))
              ( is-injective-map-equiv
                ( f)
                ( tr
                  ( λ x →
                    Id ( iterate x (map-equiv f) a)
                       ( iterate (succ-ℕ pred-second) (map-equiv f) a))
                  ( equality-pred-first)
                  ( tr
                    ( λ x →
                      Id ( iterate first-point-min-repeating (map-equiv f) a)
                         ( iterate x (map-equiv f) a))
                    ( equality-pred-second)
                    ( same-image-iterate-min-reporting)))))))
      where
      is-successor-first-point-min-repeating :
        is-successor-ℕ first-point-min-repeating
      is-successor-first-point-min-repeating =
        is-successor-is-nonzero-ℕ
          ( is-nonzero-le-ℕ
              second-point-min-repeating
              first-point-min-repeating
              le-min-reporting)
      pred-first : ℕ
      pred-first = pr1 is-successor-first-point-min-repeating
      equality-pred-first : Id first-point-min-repeating (succ-ℕ pred-first)
      equality-pred-first = pr2 is-successor-first-point-min-repeating
      is-successor-second-point-min-repeating :
        is-successor-ℕ second-point-min-repeating
      is-successor-second-point-min-repeating = is-successor-is-nonzero-ℕ np
      pred-second : ℕ
      pred-second = pr1 is-successor-second-point-min-repeating
      equality-pred-second : Id second-point-min-repeating (succ-ℕ pred-second)
      equality-pred-second = pr2 is-successor-second-point-min-repeating
  
  has-finite-orbits-permutation' :
    is-decidable (Id second-point-min-repeating zero-ℕ) →
    Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  pr1 (has-finite-orbits-permutation' (inl p)) = first-point-min-repeating
  pr1 (pr2 (has-finite-orbits-permutation' (inl p))) =
    is-nonzero-le-ℕ
      second-point-min-repeating
      first-point-min-repeating
      le-min-reporting
  pr2 (pr2 (has-finite-orbits-permutation' (inl p))) =
    tr
      ( λ x →
        Id ( iterate first-point-min-repeating (map-equiv f) a)
           ( iterate x (map-equiv f) a))
      ( p)
      ( same-image-iterate-min-reporting)
  has-finite-orbits-permutation' (inr np) =
    ex-falso (not-not-eq-second-point-zero-min-reporting np)
    where
    is-successor-first-point-min-repeating :
      is-successor-ℕ first-point-min-repeating
    is-successor-first-point-min-repeating =
      is-successor-is-nonzero-ℕ
        ( is-nonzero-le-ℕ
            second-point-min-repeating
            first-point-min-repeating
            le-min-reporting)
    pred-first : ℕ
    pred-first = pr1 is-successor-first-point-min-repeating
    equality-pred-first : Id first-point-min-repeating (succ-ℕ pred-first)
    equality-pred-first = pr2 is-successor-first-point-min-repeating
    is-successor-second-point-min-repeating :
      is-successor-ℕ second-point-min-repeating
    is-successor-second-point-min-repeating = is-successor-is-nonzero-ℕ np
    pred-second : ℕ
    pred-second = pr1 is-successor-second-point-min-repeating
    equality-pred-second : Id second-point-min-repeating (succ-ℕ pred-second)
    equality-pred-second = pr2 is-successor-second-point-min-repeating

  has-finite-orbits-permutation :
    Σ ℕ (λ k → (is-nonzero-ℕ k) × Id (iterate k (map-equiv f) a) a)
  has-finite-orbits-permutation =
    has-finite-orbits-permutation'
      ( has-decidable-equality-ℕ second-point-min-repeating zero-ℕ)

  leq-has-finite-orbits-permutation-number-elements :
    ( pr1 has-finite-orbits-permutation) ≤-ℕ (number-of-elements-count eX)
  leq-has-finite-orbits-permutation-number-elements =
    cases-second-point
      ( has-decidable-equality-ℕ second-point-min-repeating zero-ℕ)
    where
    cases-second-point :
      is-decidable (Id second-point-min-repeating zero-ℕ) →
      (pr1 has-finite-orbits-permutation) ≤-ℕ (number-of-elements-count eX)
    cases-second-point (inl p) =
      tr
        ( λ x →
          ( pr1 (has-finite-orbits-permutation' x)) ≤-ℕ
          ( number-of-elements-count eX))
        { x = inl p}
        { y = has-decidable-equality-ℕ second-point-min-repeating zero-ℕ}
        ( eq-is-prop
          ( is-prop-type-Prop
            ( is-decidable-Prop
              ( Id-Prop ℕ-Set second-point-min-repeating zero-ℕ))))
        ( leq-first-point-min-reporting-succ-number-elements)
    cases-second-point (inr np) =
      ex-falso (not-not-eq-second-point-zero-min-reporting np)
                       
  mult-has-finite-orbits-permutation :
    (k : ℕ) →
    Id (iterate (mul-ℕ k (pr1 has-finite-orbits-permutation)) (map-equiv f) a) a
  mult-has-finite-orbits-permutation zero-ℕ = refl
  mult-has-finite-orbits-permutation (succ-ℕ k) =
    ( iterate-add-ℕ
      ( mul-ℕ k (pr1 has-finite-orbits-permutation))
      ( pr1 has-finite-orbits-permutation)
      ( map-equiv f)
      ( a)) ∙
    ( ( ap
        ( iterate (mul-ℕ k (pr1 has-finite-orbits-permutation)) (map-equiv f))
        ( pr2 (pr2 has-finite-orbits-permutation))) ∙
      ( mult-has-finite-orbits-permutation k))
```
      
### For finite types, the number of orbits-permutation of a permutation is finite.

```agda
module _
  {l : Level} (n : ℕ) (X : UU-Fin-Level l n) (f : Aut (type-UU-Fin-Level X)) 
  where

  same-orbits-permutation : Eq-Rel l (type-UU-Fin-Level X)
  (pr1 same-orbits-permutation) a b =
    trunc-Prop (Σ ℕ (λ k → Id (iterate k (map-equiv f) a) b))
  pr1 (pr2 same-orbits-permutation) = unit-trunc-Prop (pair 0 refl)
  pr1 (pr2 (pr2 same-orbits-permutation)) {a} {b} P =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits-permutation b a)
      ( λ (pair k p) →
        apply-universal-property-trunc-Prop
          ( mere-equiv-UU-Fin-Level X)
          ( pr1 same-orbits-permutation b a)
          ( λ h →
            unit-trunc-Prop
              (pair
                ( pr1 (lemma h k))
                ( ( ap (iterate (pr1 (lemma h k)) (map-equiv f)) (inv p)) ∙
                  ( ( inv (iterate-add-ℕ (pr1 (lemma h k)) k (map-equiv f) a)) ∙
                    ( ( ap
                        ( λ x → iterate x (map-equiv f) a)
                        ( pr2 (lemma h k))) ∙
                      ( mult-has-finite-orbits-permutation
                        ( type-UU-Fin-Level X)
                        ( pair n h)
                        ( f)
                        ( a)
                        ( k))))))))
    where
    has-finite-orbits-permutation-a :
      (h : Fin n ≃ type-UU-Fin-Level X) →
      Σ ℕ (λ l → (is-nonzero-ℕ l) × Id (iterate l (map-equiv f) a) a)
    has-finite-orbits-permutation-a h =
      has-finite-orbits-permutation (type-UU-Fin-Level X) (pair n h) f a
    lemma : (h : Fin n ≃ type-UU-Fin-Level X) (k : ℕ) →
      Σ ( ℕ)
        ( λ j →
          Id (add-ℕ j k) (mul-ℕ k (pr1 (has-finite-orbits-permutation-a h))))
    lemma h k =
      subtraction-leq-ℕ
        ( k)
        ( mul-ℕ k (pr1 (has-finite-orbits-permutation-a h)))
        ( leq-mul-is-nonzero-ℕ
          ( pr1 (has-finite-orbits-permutation-a h))
          ( k)
          ( pr1 (pr2 (has-finite-orbits-permutation-a h))))
  pr2 (pr2 (pr2 same-orbits-permutation)) {a} {b} {c} P Q =
    apply-universal-property-trunc-Prop
      ( P)
      ( pr1 same-orbits-permutation a c)
      ( λ (pair k1 p) →
        apply-universal-property-trunc-Prop
          ( Q)
          ( pr1 same-orbits-permutation a c)
          ( λ { (pair k2 q) →
                ( unit-trunc-Prop
                  ( pair
                    ( add-ℕ k2 k1)
                    ( (iterate-add-ℕ k2 k1 (map-equiv f) a) ∙
                      ( ap (iterate k2 (map-equiv f)) p ∙ q))))}))

  abstract
    is-decidable-same-orbits-permutation :
      ( a b : type-UU-Fin-Level X) →
      is-decidable (type-Eq-Rel same-orbits-permutation a b) 
    is-decidable-same-orbits-permutation a b =
      apply-universal-property-trunc-Prop
        ( mere-equiv-UU-Fin-Level X)
        ( is-decidable-Prop (prop-Eq-Rel same-orbits-permutation a b))
        ( λ h →
          is-decidable-trunc-Prop-is-merely-decidable
            ( Σ ℕ (λ k → Id (iterate k (map-equiv f) a) b))
            ( unit-trunc-Prop
              ( is-decidable-iterate-is-decidable-bounded h a b
                ( is-decidable-bounded-Σ-ℕ n
                  ( λ z → z ≤-ℕ n)
                  ( λ z → Id (iterate z (map-equiv f) a) b)
                  ( λ z → is-decidable-leq-ℕ z n)
                  ( λ z →
                    has-decidable-equality-equiv
                      ( inv-equiv h)
                      ( has-decidable-equality-Fin)
                      ( iterate z (map-equiv f) a)
                      ( b))
                  ( λ m p → p)))))
      where
      is-decidable-iterate-is-decidable-bounded :
        ( h : Fin n ≃ type-UU-Fin-Level X) (a b : type-UU-Fin-Level X) →
        is-decidable
          ( Σ ℕ (λ m → (m ≤-ℕ n) × (Id (iterate m (map-equiv f) a) b))) →
        is-decidable (Σ ℕ (λ m → Id (iterate m (map-equiv f) a) b))
      is-decidable-iterate-is-decidable-bounded h a b (inl p) =
        inl (pair (pr1 p) (pr2 (pr2 p)))
      is-decidable-iterate-is-decidable-bounded h a b (inr np) =
        inr
          ( λ p →
            np ( pair
                 ( remainder-euclidean-division-ℕ m (pr1 p))
                 ( pair
                   ( leq-le-ℕ
                     { x = remainder-euclidean-division-ℕ m (pr1 p)}
                     ( concatenate-le-leq-ℕ
                       { y = m}
                       ( strict-upper-bound-remainder-euclidean-division-ℕ
                         ( m)
                         ( pr1 p)
                         ( pr1
                           ( pr2
                             ( has-finite-orbits-permutation
                               ( type-UU-Fin-Level X)
                               ( pair n h)
                               ( f)
                               ( a)))))
                       ( leq-has-finite-orbits-permutation-number-elements
                         ( type-UU-Fin-Level X)
                         ( pair n h)
                         ( f)
                         ( a))))
                   ( ( ap
                       ( iterate
                         ( remainder-euclidean-division-ℕ m (pr1 p))
                         ( map-equiv f))
                       ( inv
                         ( mult-has-finite-orbits-permutation
                           ( type-UU-Fin-Level X)
                           ( pair n h)
                           ( f)
                           ( a)
                           ( quotient-euclidean-division-ℕ m (pr1 p))))) ∙
                     ( ( inv
                         ( iterate-add-ℕ
                           ( remainder-euclidean-division-ℕ m (pr1 p))
                           ( mul-ℕ (quotient-euclidean-division-ℕ m (pr1 p)) m)
                           ( map-equiv f)
                           ( a))) ∙
                       ( ( ap
                           ( λ x → iterate x (map-equiv f) a)
                           ( ( commutative-add-ℕ
                               ( remainder-euclidean-division-ℕ m (pr1 p))
                               ( mul-ℕ
                                 ( quotient-euclidean-division-ℕ m (pr1 p))
                                 ( m))) ∙
                             ( eq-euclidean-division-ℕ m (pr1 p)))) ∙
                         ( pr2 p)))))))
        where
        m : ℕ
        m = pr1
            ( has-finite-orbits-permutation
              ( type-UU-Fin-Level X)
              ( pair n h)
              ( f)
              ( a))

  abstract
    is-decidable-type-class-large-set-quotient-same-orbits-permutation :
      (T : large-set-quotient same-orbits-permutation) →
      (a : type-UU-Fin-Level X) →
      is-decidable (type-class-large-set-quotient same-orbits-permutation T a)
    is-decidable-type-class-large-set-quotient-same-orbits-permutation T a =
      is-decidable-type-class-large-set-quotient-is-decidable
        ( same-orbits-permutation)
        ( is-decidable-same-orbits-permutation)
        ( T)
        ( a)

  abstract
    has-finite-number-orbits-permutation :
      is-finite (large-set-quotient same-orbits-permutation)
    has-finite-number-orbits-permutation =
      is-finite-codomain
        ( is-finite-type-UU-Fin-Level X)
        ( is-surjective-quotient-map-large-set-quotient same-orbits-permutation)
        ( apply-universal-property-trunc-Prop
          ( mere-equiv-UU-Fin-Level X)
          ( pair
            ( has-decidable-equality
              ( large-set-quotient same-orbits-permutation))
            ( is-prop-has-decidable-equality))
        ( λ h T1 T2 →
          apply-universal-property-trunc-Prop
          ( pr2 T1)
          ( is-decidable-Prop
            ( Id-Prop (large-quotient-Set same-orbits-permutation) T1 T2))
          ( λ (pair t1 p1) →
            cases-decidable-equality T1 T2 t1
              ( eq-pair-Σ (inv p1) (all-elements-equal-type-trunc-Prop _ _))
              ( is-decidable-type-class-large-set-quotient-same-orbits-permutation T2 t1))))
      where
      cases-decidable-equality :
        (T1 T2 : large-set-quotient same-orbits-permutation)
        (t1 : type-UU-Fin-Level X) →
        Id T1 (quotient-map-large-set-quotient same-orbits-permutation t1) →
        is-decidable
          ( type-class-large-set-quotient same-orbits-permutation T2 t1) →
        is-decidable (Id T1 T2)
      cases-decidable-equality T1 T2 t1 p1 (inl p) =
        inl
          ( ( p1) ∙
            ( map-inv-is-equiv
              ( is-equiv-related-eq-quotient same-orbits-permutation t1 T2) p))
      cases-decidable-equality T1 T2 t1 p1 (inr np) =
        inr
          ( λ p →
            np (related-eq-quotient same-orbits-permutation t1 T2 (inv p1 ∙ p)))

  number-of-orbits-permutation : ℕ
  number-of-orbits-permutation =
    number-of-elements-is-finite has-finite-number-orbits-permutation

  sign-permutation-orbit : Fin 2
  sign-permutation-orbit =
    iterate (add-ℕ n number-of-orbits-permutation) (succ-Fin {k = 2}) zero-Fin
```

```agda
module _
  {l1 : Level} (X : UU l1) (eX : count X) (a b : X) (np : ¬ (Id a b))
  where

  composition-transposition-a-b : (X ≃ X) → (X ≃ X)
  composition-transposition-a-b g =
    ( standard-transposition (has-decidable-equality-count eX) np) ∘e g

  composition-transposition-a-b-involution :
    ( g : X ≃ X) →
    htpy-equiv
      ( composition-transposition-a-b (composition-transposition-a-b g))
      ( g)
  composition-transposition-a-b-involution g x =
    is-involution-map-transposition
      ( standard-2-Element-Decidable-Subtype
        ( has-decidable-equality-count eX)
        ( np))
      ( map-equiv g x)

  same-orbits-permutation-count : (X ≃ X) → Eq-Rel l1 X
  same-orbits-permutation-count =
    same-orbits-permutation
      ( number-of-elements-count eX)
      ( pair X (unit-trunc-Prop (equiv-count eX)))

  minimal-element-iterate :
    (g : X ≃ X) (x y : X) → Σ ℕ (λ k → Id (iterate k (map-equiv g) x) y) →
    minimal-element-ℕ (λ k → Id (iterate k (map-equiv g) x) y)
  minimal-element-iterate g x y =
    well-ordering-principle-ℕ
      ( λ k → Id (iterate k (map-equiv g) x) y)
      ( λ k → has-decidable-equality-count eX (iterate k (map-equiv g) x) y)

  minimal-element-iterate-nonzero :
    (g : X ≃ X) (x y : X) →
    Σ ℕ (λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) x) y) →
    minimal-element-ℕ
      ( λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) x) y)
  minimal-element-iterate-nonzero g x y =
    well-ordering-principle-ℕ
      ( λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) x) y)
      ( λ k →
        is-decidable-prod
          ( is-decidable-neg (has-decidable-equality-ℕ k zero-ℕ))
          ( has-decidable-equality-count eX (iterate k (map-equiv g) x) y))

  minimal-element-iterate-2 :
    (g : X ≃ X) (x y z : X) →
    Σ ( ℕ)
      ( λ k →
        coprod
          ( Id (iterate k (map-equiv g) x) y)
          ( Id (iterate k (map-equiv g) x) z)) →
    minimal-element-ℕ
      ( λ k →
        coprod
          ( Id (iterate k (map-equiv g) x) y)
          ( Id (iterate k (map-equiv g) x) z))
  minimal-element-iterate-2 g x y z p =
    well-ordering-principle-ℕ
      ( λ k →
        coprod
          ( Id (iterate k (map-equiv g) x) y)
          ( Id (iterate k (map-equiv g) x) z))
      ( λ k →
        is-decidable-coprod
        ( has-decidable-equality-count eX (iterate k (map-equiv g) x) y)
        ( has-decidable-equality-count eX (iterate k (map-equiv g) x) z))
      ( p)

  abstract
    equal-iterate-transposition :
      {l2 : Level} (x : X) (g : X ≃ X) (C : ℕ → UU l2)
      ( F :
        (k : ℕ) → C k →
        ( ¬ (Id (iterate k (map-equiv g) x) a)) ×
        ( ¬ (Id (iterate k (map-equiv g) x) b)))
      ( Ind :
        (n : ℕ) → C (succ-ℕ n) → is-nonzero-ℕ n → C n) →
      (k : ℕ) → coprod (is-zero-ℕ k) (C k) →
      Id ( iterate k (map-equiv (composition-transposition-a-b g)) x)
         ( iterate k (map-equiv g) x)
    equal-iterate-transposition x g C F Ind zero-ℕ p = refl
    equal-iterate-transposition x g C F Ind (succ-ℕ k) (inl p) =
      ex-falso (is-nonzero-succ-ℕ k p)
    equal-iterate-transposition x g C F Ind (succ-ℕ k) (inr p) =
      cases-equal-iterate-transposition
        ( has-decidable-equality-count eX
          ( iterate (succ-ℕ k) (map-equiv g) x)
          ( a))
        ( has-decidable-equality-count eX
          ( iterate (succ-ℕ k) (map-equiv g) x)
          ( b))
      where
      induction-cases-equal-iterate-transposition :
        is-decidable (Id k zero-ℕ) →
        Id ( iterate k (map-equiv (composition-transposition-a-b g)) x)
           ( iterate k (map-equiv g) x)
      induction-cases-equal-iterate-transposition (inl s) =
        tr
          ( λ k →
            Id (iterate k (map-equiv (composition-transposition-a-b g)) x)
            (iterate k (map-equiv g) x))
          ( inv s)
          ( refl)
      induction-cases-equal-iterate-transposition (inr s) =
        equal-iterate-transposition x g C F Ind k (inr (Ind k p s))
      cases-equal-iterate-transposition :
        is-decidable (Id (iterate (succ-ℕ k) (map-equiv g) x) a) →
        is-decidable (Id (iterate (succ-ℕ k) (map-equiv g) x) b) →
        Id
          ( iterate (succ-ℕ k) (map-equiv (composition-transposition-a-b g)) x)
          ( iterate (succ-ℕ k) (map-equiv g) x)
      cases-equal-iterate-transposition (inl q) r =
        ex-falso (pr1 (F (succ-ℕ k) p) q) 
      cases-equal-iterate-transposition (inr q) (inl r) =
        ex-falso (pr2 (F (succ-ℕ k) p) r) 
      cases-equal-iterate-transposition (inr q) (inr r) =
        ( ap
          ( λ n →
            iterate n (map-equiv (composition-transposition-a-b g)) x)
          ( commutative-add-ℕ k (succ-ℕ zero-ℕ))) ∙
        ( ( iterate-add-ℕ
            ( succ-ℕ zero-ℕ)
            ( k)
            ( map-equiv (composition-transposition-a-b g))
            ( x)) ∙
          ( ( ap
              ( map-equiv (composition-transposition-a-b g))
              ( induction-cases-equal-iterate-transposition
                ( has-decidable-equality-ℕ k zero-ℕ))) ∙
            ( is-fixed-point-standard-transposition
              ( has-decidable-equality-count eX)
              ( np)
              ( iterate (succ-ℕ k) (map-equiv g) x)
              ( λ q' → q (inv q'))
              ( λ r' → r (inv r')))))

  abstract
    conserves-other-orbits-transposition : (g : X ≃ X) (x y : X) →
      ¬ (type-Eq-Rel (same-orbits-permutation-count g) x a) →
      ¬ (type-Eq-Rel (same-orbits-permutation-count g) x b) →
      ( ( type-Eq-Rel (same-orbits-permutation-count g) x y) ≃
        ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x y))
    conserves-other-orbits-transposition g x y NA NB =
      pair 
        ( λ P' → apply-universal-property-trunc-Prop P'
          ( prop-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x y)
          ( λ (pair k p) → unit-trunc-Prop
            (pair k
              ( (equal-iterate-transposition-other-orbits k) ∙
                ( p)))))
        ( is-equiv-is-prop is-prop-type-trunc-Prop is-prop-type-trunc-Prop
          ( λ P' → apply-universal-property-trunc-Prop P'
            ( prop-Eq-Rel (same-orbits-permutation-count g) x y)
            ( λ (pair k p) → unit-trunc-Prop
              ( pair k
                ( (inv (equal-iterate-transposition-other-orbits k)) ∙
                  ( p))))))
      where
      equal-iterate-transposition-other-orbits :
        (k : ℕ) → Id (iterate k (map-equiv (composition-transposition-a-b g)) x) (iterate k (map-equiv g) x) 
      equal-iterate-transposition-other-orbits k =
        equal-iterate-transposition x g (λ k' → unit)
          (λ k' _ →
            pair
              ( λ q → NA (unit-trunc-Prop (pair k' q)))
              ( λ r → NB (unit-trunc-Prop (pair k' r))))
          (λ _ _ _ → star) k (inr star)

  conserves-other-orbits-transposition-quotient : (g : X ≃ X) →
    (T : large-set-quotient (same-orbits-permutation-count g)) →
    ¬ (type-class-large-set-quotient (same-orbits-permutation-count g) T a) →
    ¬ (type-class-large-set-quotient (same-orbits-permutation-count g) T b) →
    large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
  pr1 (conserves-other-orbits-transposition-quotient g T nq nr) = pr1 T
  pr2 (conserves-other-orbits-transposition-quotient g T nq nr) =
    apply-universal-property-trunc-Prop
      ( pr2 T)
      ( trunc-Prop
        ( fib
          ( prop-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)))
          ( pr1 T)))
      ( λ (pair x Q) →
        unit-trunc-Prop
          ( pair x
            ( eq-htpy
              ( λ y → eq-pair-Σ
                ( eq-equiv
                  ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x y)
                  ( type-Eq-Rel (same-orbits-permutation-count g) x y)
                  ( inv-equiv
                    ( conserves-other-orbits-transposition g x y
                      ( λ S → nq
                        ( tr (λ w → type-class-large-set-quotient (same-orbits-permutation-count g) w a)
                          ( eq-pair-Σ Q
                            ( all-elements-equal-type-trunc-Prop
                              ( tr
                                ( λ z → type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count g)) z))
                                ( Q)
                                ( unit-trunc-Prop (pair x refl)))
                              ( pr2 T)))
                            ( S)))
                      ( λ S → nr
                        ( tr (λ w → type-class-large-set-quotient (same-orbits-permutation-count g) w b)
                          ( eq-pair-Σ Q
                            ( all-elements-equal-type-trunc-Prop
                              ( tr
                                ( λ z → type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count g)) z))
                                ( Q)
                                ( unit-trunc-Prop (pair x refl)))
                              ( pr2 T)))
                            ( S))))))
                ( eq-is-prop (is-prop-is-prop (type-trunc-Prop (Σ ℕ (λ k1 → Id (iterate k1 (map-equiv g) x) y)))))) ∙
              ( Q))))

  abstract
    not-same-orbits-transposition-same-orbits : (g : X ≃ X) →
      (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
      ¬ (type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) a b)
    not-same-orbits-transposition-same-orbits g P Q =
      apply-universal-property-trunc-Prop Q empty-Prop
        ( λ (pair k2 q) →
          ( apply-universal-property-trunc-Prop P empty-Prop
            ( λ p → lemma3 p k2 q)))
      where
      neq-iterate-nonzero-le-minimal-element : (pa : Σ ℕ (λ k → Id (iterate k (map-equiv g) a) b)) (k : ℕ) →
        ( is-nonzero-ℕ k × le-ℕ k (pr1 (minimal-element-iterate g a b pa))) →
        ¬ (Id (iterate k (map-equiv g) a) a) × ¬ (Id (iterate k (map-equiv g) a) b)
      pr1 (neq-iterate-nonzero-le-minimal-element pa k (pair nz ineq)) = λ q →
        contradiction-le-ℕ
          ( pr1 pair-k2)
          ( pr1 (minimal-element-iterate g a b pa))
          ( le-subtraction-ℕ
            ( pr1 (pair-k2))
            ( pr1 (minimal-element-iterate g a b pa))
            ( k)
            ( nz)
            ( commutative-add-ℕ k (pr1 (pair-k2)) ∙ pr2 (pr2 pair-k2)))
          ( pr2
            ( pr2 (minimal-element-iterate g a b pa))
            ( pr1 pair-k2)
            ( (ap (iterate (pr1 pair-k2) (map-equiv g)) (inv q)) ∙
              ( (inv (iterate-add-ℕ (pr1 pair-k2) k (map-equiv g) a)) ∙
                ( ap (λ n → iterate n (map-equiv g) a) (pr2 (pr2 pair-k2)) ∙ pr1 (pr2 (minimal-element-iterate g a b pa))))))
        where
        pair-k2 : Σ ℕ λ l → is-nonzero-ℕ l × Id (add-ℕ l k) (pr1 (minimal-element-iterate g a b pa))
        pair-k2 = (subtraction-le-ℕ k (pr1 (minimal-element-iterate g a b pa)) ineq)
      pr2 (neq-iterate-nonzero-le-minimal-element pa k (pair nz ineq)) = λ r →
        ex-falso
          ( contradiction-le-ℕ k (pr1 (minimal-element-iterate g a b pa))
            ineq (pr2 (pr2 (minimal-element-iterate g a b pa)) k r))
      equal-iterate-transposition-a : (pa : Σ ℕ (λ k → Id (iterate k (map-equiv g) a) b)) →
        (k : ℕ) → le-ℕ k (pr1 (minimal-element-iterate g a b pa)) →
        (Id (iterate k (map-equiv (composition-transposition-a-b g)) a) (iterate k (map-equiv g) a))
      equal-iterate-transposition-a pa k ineq =
        equal-iterate-transposition a g
          ( λ k' → (is-nonzero-ℕ k') × (le-ℕ k' (pr1 (minimal-element-iterate g a b pa))))
          ( neq-iterate-nonzero-le-minimal-element pa)
          ( λ n (pair _ s) nz → pair nz (transitive-le-ℕ n (succ-ℕ n) (pr1 (minimal-element-iterate g a b pa)) (le-succ-ℕ {x = n}) s))
          ( k)
          ( cases-equal-iterate-transposition-a (has-decidable-equality-ℕ k zero-ℕ))
        where
        cases-equal-iterate-transposition-a : is-decidable (is-zero-ℕ k) →
          coprod (is-zero-ℕ k) (is-nonzero-ℕ k × le-ℕ k (pr1 (minimal-element-iterate g a b pa)))
        cases-equal-iterate-transposition-a (inl s) = inl s
        cases-equal-iterate-transposition-a (inr s) = inr (pair s ineq)
      lemma2 : (pa : Σ ℕ (λ k → Id (iterate k (map-equiv g) a) b)) →
        is-decidable (Id (pr1 (minimal-element-iterate g a b pa)) zero-ℕ) →
        Id (iterate (pr1 (minimal-element-iterate g a b pa)) (map-equiv (composition-transposition-a-b g)) a) a
      lemma2 pa (inl p) =
        ex-falso (np (tr (λ v → Id (iterate v (map-equiv g) a) b) p (pr1 (pr2 (minimal-element-iterate g a b pa)))))
      lemma2 pa (inr p) =
        ( ap (λ n → iterate n (map-equiv (composition-transposition-a-b g)) a)
          ( pr2 (is-successor-k1) ∙ commutative-add-ℕ (pr1 is-successor-k1) (succ-ℕ zero-ℕ))) ∙
          ( (iterate-add-ℕ (succ-ℕ zero-ℕ) (pr1 is-successor-k1) (map-equiv (composition-transposition-a-b g)) a) ∙
            ( (ap
              ( map-equiv (composition-transposition-a-b g))
                ( equal-iterate-transposition-a pa (pr1 is-successor-k1)
                  ( tr (λ n → le-ℕ (pr1 is-successor-k1) n) (inv (pr2 is-successor-k1)) (le-succ-ℕ {x = pr1 is-successor-k1})))) ∙
              ( (ap
                ( λ n →
                  map-standard-transposition
                    ( has-decidable-equality-count eX)
                    ( np)
                    ( iterate n (map-equiv g) a))
                ( inv (pr2 is-successor-k1))) ∙
                ( ( ap
                    ( map-standard-transposition
                      ( has-decidable-equality-count eX) np)
                    ( pr1 (pr2 (minimal-element-iterate g a b pa)))) ∙
                  ( right-computation-standard-transposition
                    ( has-decidable-equality-count eX)
                    ( np))))))
        where
        is-successor-k1 : is-successor-ℕ (pr1 (minimal-element-iterate g a b pa))
        is-successor-k1 = is-successor-is-nonzero-ℕ p
      mult-lemma2 : (pa : Σ ℕ (λ k → Id (iterate k (map-equiv g) a) b)) → (k : ℕ) →
        Id (iterate (mul-ℕ k (pr1 (minimal-element-iterate g a b pa))) (map-equiv (composition-transposition-a-b g)) a) a
      mult-lemma2 pa zero-ℕ = refl
      mult-lemma2 pa (succ-ℕ k) =
        ( iterate-add-ℕ (mul-ℕ k (pr1 (minimal-element-iterate g a b pa)))
          ( pr1 (minimal-element-iterate g a b pa)) (map-equiv (composition-transposition-a-b g)) a) ∙
          ( ap
            ( iterate (mul-ℕ k (pr1 (minimal-element-iterate g a b pa))) (map-equiv (composition-transposition-a-b g)))
            ( lemma2 pa (has-decidable-equality-ℕ (pr1 (minimal-element-iterate g a b pa)) zero-ℕ)) ∙
            ( mult-lemma2 pa k))
      lemma3 : (pa : Σ ℕ (λ k → Id (iterate k (map-equiv g) a) b)) → (k : ℕ) →
        ¬ (Id (iterate k (map-equiv (composition-transposition-a-b g)) a) b)
      lemma3 pa k q =
        contradiction-le-ℕ
          ( r)
          ( pr1 (minimal-element-iterate g a b pa))
          ( ineq)
          ( pr2 (pr2 (minimal-element-iterate g a b pa)) r (inv (equal-iterate-transposition-a pa r ineq) ∙
            ( (ap (iterate r (map-equiv (composition-transposition-a-b g))) (inv (mult-lemma2 pa quo))) ∙
              ( (inv
                ( iterate-add-ℕ r (mul-ℕ quo (pr1 (minimal-element-iterate g a b pa)))
                  (map-equiv (composition-transposition-a-b g)) a)) ∙
                ( (ap (λ n → iterate n (map-equiv (composition-transposition-a-b g)) a)
                  ( commutative-add-ℕ r (mul-ℕ quo (pr1 (minimal-element-iterate g a b pa))) ∙
                    ( eq-euclidean-division-ℕ (pr1 (minimal-element-iterate g a b pa)) k))) ∙
                  ( q))))))
        where
        r : ℕ
        r = remainder-euclidean-division-ℕ (pr1 (minimal-element-iterate g a b pa)) k
        quo : ℕ
        quo = quotient-euclidean-division-ℕ (pr1 (minimal-element-iterate g a b pa)) k
        ineq : le-ℕ r (pr1 (minimal-element-iterate g a b pa))
        ineq =
          strict-upper-bound-remainder-euclidean-division-ℕ (pr1 (minimal-element-iterate g a b pa)) k
            ( λ p → (np (tr (λ v → Id (iterate v (map-equiv g) a) b) p (pr1 (pr2 (minimal-element-iterate g a b pa))))))

  coprod-type-Eq-Rel-a-b-Prop : (g : X ≃ X) →
    (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
    (x : X) → UU-Prop l1
  coprod-type-Eq-Rel-a-b-Prop g P x =
    coprod-Prop
      ( prop-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x a)
      ( prop-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x b)
      ( λ T1 T2 → not-same-orbits-transposition-same-orbits g P
        ( trans-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g))
          ( symm-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) T1)
          ( T2)))

  abstract
    split-orbits-a-b-transposition : (g : X ≃ X) →
      (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
      (x : X) →
      ( ( type-Eq-Rel (same-orbits-permutation-count g) x a) ≃
        ( coprod
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x a)
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x b)))
    split-orbits-a-b-transposition g P x =
      pair
        ( λ T →
          apply-universal-property-trunc-Prop T (coprod-type-Eq-Rel-a-b-Prop g P x)
            (λ pa → lemma2 g (pair (pr1 pa) (inl (pr2 pa)))))
        ( is-equiv-is-prop is-prop-type-trunc-Prop (is-prop-type-Prop (coprod-type-Eq-Rel-a-b-Prop g P x))
          ( λ {
            (inl T) →
              apply-universal-property-trunc-Prop T (prop-Eq-Rel (same-orbits-permutation-count g) x a)
                (λ pa → lemma3 (lemma2 (composition-transposition-a-b g) (pair (pr1 pa) (inl (pr2 pa)))))
            ; (inr T) →
              apply-universal-property-trunc-Prop T (prop-Eq-Rel (same-orbits-permutation-count g) x a)
                (λ pa → lemma3 (lemma2 (composition-transposition-a-b g) (pair (pr1 pa) (inr (pr2 pa)))))}))
      where
      minimal-element-iterate-2-a-b : (g : X ≃ X) →
        (Σ ℕ (λ k → coprod (Id (iterate k (map-equiv g) x) a) (Id (iterate k (map-equiv g) x) b))) →
        minimal-element-ℕ (λ k → coprod (Id (iterate k (map-equiv g) x) a) (Id (iterate k (map-equiv g) x) b))
      minimal-element-iterate-2-a-b g = minimal-element-iterate-2 g x a b
      equal-iterate-transposition-same-orbits : (g : X ≃ X) →
        (pa : Σ ℕ (λ k → coprod (Id (iterate k (map-equiv g) x) a) (Id (iterate k (map-equiv g) x) b))) (k : ℕ) →
        (le-ℕ k (pr1 (minimal-element-iterate-2-a-b g pa))) →
        Id (iterate k (map-equiv (composition-transposition-a-b g)) x) (iterate k (map-equiv g) x) 
      equal-iterate-transposition-same-orbits g pa k ineq =
        equal-iterate-transposition x g
          ( λ k' → le-ℕ k' (pr1 (minimal-element-iterate-2-a-b g pa)))
          ( λ k' p → pair
            ( λ q → ( contradiction-le-ℕ k' ( pr1 (minimal-element-iterate-2-a-b g pa)) p
              ( pr2 (pr2 (minimal-element-iterate-2-a-b g pa)) k' (inl q))))
            ( λ r → ( contradiction-le-ℕ k' (pr1 (minimal-element-iterate-2-a-b g pa)) p
              ( pr2 (pr2 (minimal-element-iterate-2-a-b g pa)) k' (inr r)))))
          ( λ k' ineq' _ →
            (transitive-le-ℕ k' (succ-ℕ k') (pr1 (minimal-element-iterate-2-a-b g pa)) (le-succ-ℕ {x = k'}) ineq'))
          k (inr ineq)
      lemma2 : (g : X ≃ X) (pa : Σ ℕ (λ k → coprod (Id (iterate k (map-equiv g) x) a) (Id (iterate k (map-equiv g) x) b))) →
        coprod
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x a)
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x b)
      lemma2 g pa =
        cases-lemma2
          ( has-decidable-equality-ℕ (pr1 (minimal-element-iterate-2-a-b g pa)) zero-ℕ)
          ( pr1 (pr2 (minimal-element-iterate-2-a-b g pa)))
          ( refl)
        where
        cases-lemma2 : is-decidable (Id (pr1 (minimal-element-iterate-2-a-b g pa)) zero-ℕ) →
          (c : coprod
            (Id (iterate (pr1 (minimal-element-iterate-2-a-b g pa)) (map-equiv g) x) a)
            (Id (iterate (pr1 (minimal-element-iterate-2-a-b g pa)) (map-equiv g) x) b)) →
          Id c (pr1 (pr2 (minimal-element-iterate-2-a-b g pa))) →
          coprod
            ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x a)
            ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) x b)
        cases-lemma2 (inl q) (inl c) r =
          inl (unit-trunc-Prop (pair zero-ℕ (tr (λ z → Id (iterate z (map-equiv g) x) a) q c)))
        cases-lemma2 (inl q) (inr c) r =
          inr (unit-trunc-Prop (pair zero-ℕ (tr (λ z → Id (iterate z (map-equiv g) x) b) q c)))
        cases-lemma2 (inr q) (inl c) r = inr (unit-trunc-Prop
          ( pair
            ( pr1 (minimal-element-iterate-2-a-b g pa))
            ( ( ap (λ n → iterate n (map-equiv (composition-transposition-a-b g)) x)
              ( pr2 (is-successor-k1) ∙ commutative-add-ℕ (pr1 is-successor-k1) (succ-ℕ zero-ℕ))) ∙
              ( (iterate-add-ℕ (succ-ℕ zero-ℕ) (pr1 is-successor-k1) (map-equiv (composition-transposition-a-b g)) x) ∙
                ( (ap
                  ( map-equiv (composition-transposition-a-b g))
                  ( equal-iterate-transposition-same-orbits g pa (pr1 is-successor-k1)
                    ( tr (λ n → le-ℕ (pr1 is-successor-k1) n) (inv (pr2 is-successor-k1)) (le-succ-ℕ {x = pr1 is-successor-k1})))) ∙
                  ( (ap
                    ( λ n →
                      map-standard-transposition
                        ( has-decidable-equality-count eX)
                        ( np)
                        ( iterate n (map-equiv g) x))
                    ( inv (pr2 is-successor-k1))) ∙
                    ( ( ap
                        ( map-standard-transposition
                          ( has-decidable-equality-count eX)
                          ( np))
                        ( c)) ∙
                      left-computation-standard-transposition
                        ( has-decidable-equality-count eX)
                        ( np))))))))
          where
          is-successor-k1 : is-successor-ℕ (pr1 (minimal-element-iterate-2-a-b g pa))
          is-successor-k1 = is-successor-is-nonzero-ℕ q
        cases-lemma2 (inr q) (inr c) r = inl (unit-trunc-Prop
          ( pair
            ( pr1 (minimal-element-iterate-2-a-b g pa))
            (( ap (λ n → iterate n (map-equiv (composition-transposition-a-b g)) x)
              ( pr2 (is-successor-k1) ∙ commutative-add-ℕ (pr1 is-successor-k1) (succ-ℕ zero-ℕ))) ∙
              ( (iterate-add-ℕ (succ-ℕ zero-ℕ) (pr1 is-successor-k1) (map-equiv (composition-transposition-a-b g)) x) ∙
                ( (ap
                  ( map-equiv (composition-transposition-a-b g))
                  ( equal-iterate-transposition-same-orbits g pa (pr1 is-successor-k1)
                    ( tr (λ n → le-ℕ (pr1 is-successor-k1) n) (inv (pr2 is-successor-k1)) (le-succ-ℕ {x = pr1 is-successor-k1})))) ∙
                  ( (ap
                    ( λ n →
                      map-standard-transposition
                        ( has-decidable-equality-count eX)
                        ( np)
                        ( iterate n (map-equiv g) x))
                    ( inv (pr2 is-successor-k1))) ∙
                    ( ( ap
                        ( map-standard-transposition
                          ( has-decidable-equality-count eX)
                          ( np))
                        ( c)) ∙
                      right-computation-standard-transposition
                        ( has-decidable-equality-count eX)
                        ( np))))))))
          where
          is-successor-k1 : is-successor-ℕ (pr1 (minimal-element-iterate-2-a-b g pa))
          is-successor-k1 = is-successor-is-nonzero-ℕ q
      lemma3 : 
        (coprod
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b (composition-transposition-a-b g))) x a)
          ( type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b (composition-transposition-a-b g))) x b)) →
          type-Eq-Rel (same-orbits-permutation-count g) x a
      lemma3 (inl T) =
        tr (λ f → type-Eq-Rel (same-orbits-permutation-count f) x a)
          { x = composition-transposition-a-b (composition-transposition-a-b g)} {y = g}
          ( eq-htpy-equiv (composition-transposition-a-b-involution g)) T 
      lemma3 (inr T) =
        trans-Eq-Rel (same-orbits-permutation-count g)
          ( tr (λ g → type-Eq-Rel (same-orbits-permutation-count g) x b)
            { x = composition-transposition-a-b (composition-transposition-a-b g)} {y = g}
            ( eq-htpy-equiv (composition-transposition-a-b-involution g))
            ( T))
          ( symm-Eq-Rel (same-orbits-permutation-count g) P)

  private
    module _
      (g : X ≃ X)
      (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b))
      (h :
        count
          ( large-set-quotient
            ( same-orbits-permutation ( number-of-elements-count eX) ( pair X (unit-trunc-Prop (equiv-count eX))) ( g))))
      where
      
      h'-inl : ( k : Fin (number-of-elements-count h)) →
        ( T : large-set-quotient (same-orbits-permutation-count g)) → 
        Id (map-equiv-count h k) T →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g) T a) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g) T b) →
        large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
      h'-inl k T p (inl q) r =
        quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) a
      h'-inl k T p (inr nq) (inl r) = ex-falso (nq
        ( transitive-type-class-large-set-quotient (same-orbits-permutation-count g) T b a r
        ( symm-Eq-Rel (same-orbits-permutation-count g) P)))
      h'-inl k T p (inr nq) (inr nr) = conserves-other-orbits-transposition-quotient g T nq nr
      h' : Fin (succ-ℕ (number-of-elements-count h)) →
        large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
      h' (inl k) = h'-inl k (map-equiv-count h k) refl 
        ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
          (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g (map-equiv-count h k) a)
        ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
          (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g (map-equiv-count h k) b)
      h' (inr k) = quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b
      cases-inv-h' : (T : large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b) →
        Fin (succ-ℕ (number-of-elements-count h)) 
      cases-inv-h' T (inl Q) R =
        inl
          ( map-inv-equiv-count h (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
      cases-inv-h' T (inr NQ) (inl R) = inr star
      cases-inv-h' T (inr NQ) (inr NR) = inl
        ( map-inv-equiv-count h
          ( pair
            ( pr1 T)
            ( tr
              ( λ f → type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count f)) (pr1 T)))
              { x = composition-transposition-a-b (composition-transposition-a-b g)} {y = g}
              ( eq-htpy-equiv (composition-transposition-a-b-involution g))
              ( pr2 (conserves-other-orbits-transposition-quotient (composition-transposition-a-b g) T NQ NR)))))
      inv-h' : (T : large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))) →
        Fin (succ-ℕ (number-of-elements-count h)) 
      inv-h' T =
        cases-inv-h' T
          ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
            (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            (composition-transposition-a-b g) T a)
          ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
            (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            (composition-transposition-a-b g) T b)
      H-conserves : (T : large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))) →
        ( NQ : ¬ (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a)) →
        ( NR : ¬ (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b)) →
        type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count g)) (pr1 T))
      H-conserves T NQ NR =
        tr
          ( λ f → type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count f)) (pr1 T)))
          { x = composition-transposition-a-b (composition-transposition-a-b g)} {y = g}
          ( eq-htpy-equiv (composition-transposition-a-b-involution g))
          ( pr2 (conserves-other-orbits-transposition-quotient (composition-transposition-a-b g) T NQ NR))
      retr-h'-inr-inr : (T : large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))) →
        ( NQ : ¬ (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a)) →
        ( NR : ¬ (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b)) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g)
          (pair (pr1 T) (H-conserves T NQ NR)) a) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g)
          (pair (pr1 T) (H-conserves T NQ NR)) b) →
        Id
          ( h' (inl (map-inv-equiv-count h
            ( pair
              ( pr1 T)
              ( tr
                ( λ f → type-trunc-Prop (fib (prop-Eq-Rel (same-orbits-permutation-count f)) (pr1 T)))
                { x = composition-transposition-a-b (composition-transposition-a-b g)} {y = g}
                ( eq-htpy-equiv (composition-transposition-a-b-involution g))
                ( pr2 (conserves-other-orbits-transposition-quotient (composition-transposition-a-b g) T NQ NR)))))))
          ( T)
      retr-h'-inr-inr T NQ NR (inl Q') R' = ex-falso (NQ Q')
      retr-h'-inr-inr T NQ NR (inr NQ') (inl R') = ex-falso (NR R')
      retr-h'-inr-inr T NQ NR (inr NQ') (inr NR') =
        ( ap
          ( λ w →
            h'-inl
              ( map-inv-equiv-count h (pair (pr1 T) (H-conserves T NQ NR)))
              ( map-equiv (pr1 w) (pair (pr1 T) (H-conserves T NQ NR)))
              ( pr2 w)
              ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
                  ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                  ( map-equiv (pr1 w) (pair (pr1 T) (H-conserves T NQ NR))) a)
              ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
                  ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                  ( map-equiv (pr1 w) (pair (pr1 T) (H-conserves T NQ NR))) b))
          { x = pair ((equiv-count h) ∘e (inv-equiv-count h)) refl}
          { y = pair
            id-equiv
            ( ap ( λ f → map-equiv f (pair (pr1 T) (H-conserves T NQ NR))) ( right-inverse-law-equiv (equiv-count h)))}
          ( eq-pair-Σ
            ( right-inverse-law-equiv (equiv-count h))
            ( eq-is-prop
              ( is-prop-type-Prop
                ( Id-Prop
                  ( large-quotient-Set (same-orbits-permutation-count g))
                  ( map-equiv-count h ( map-inv-equiv-count h (pair (pr1 T) (H-conserves T NQ NR))))
                  ( pair (pr1 T) (H-conserves T NQ NR))))))) ∙
          ( ap
            (λ w →
              h'-inl
                ( map-inv-equiv-count h (pair (pr1 T) (H-conserves T NQ NR)))
                ( pair (pr1 T) (H-conserves T NQ NR))
                ( ap ( λ f → map-equiv f (pair (pr1 T) (H-conserves T NQ NR))) ( right-inverse-law-equiv (equiv-count h)))
                ( w)
                ( is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
                  (pair X (unit-trunc-Prop (equiv-count eX))) g (pair (pr1 T) (H-conserves T NQ NR)) b))
            { x = is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
              (pair X (unit-trunc-Prop (equiv-count eX))) g (pair (pr1 T) (H-conserves T NQ NR)) a}
            { y = inr NQ'}
            ( eq-is-prop
              ( is-prop-is-decidable
                ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count g)
                  ( pair (pr1 T) (H-conserves T NQ NR)) a))) ∙
            ( (ap
              ( λ w →
                h'-inl
                  ( map-inv-equiv-count h (pair (pr1 T) (H-conserves T NQ NR)))
                  ( pair (pr1 T) (H-conserves T NQ NR))
                  ( ap ( λ f → map-equiv f (pair (pr1 T) (H-conserves T NQ NR))) ( right-inverse-law-equiv (equiv-count h)))
                  ( inr NQ')
                  ( w))
              { x = is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
                (pair X (unit-trunc-Prop (equiv-count eX))) g (pair (pr1 T) (H-conserves T NQ NR)) b}
              { y = inr NR'}
              ( eq-is-prop
                ( is-prop-is-decidable
                  ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count g)
                    (pair (pr1 T) (H-conserves T NQ NR)) b))) ∙
              ( eq-pair-Σ refl ( eq-is-prop is-prop-type-trunc-Prop)))))
      retr-h' : (T : large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a) →
        is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b) →
        Id (h' (inv-h' T)) T
      retr-h' T (inl Q) R =
        tr
          (λ w → Id (h' (cases-inv-h' T w
            ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T b)))
            ( T))
          {x = inl Q}
          {y = (is-decidable-type-class-large-set-quotient-same-orbits-permutation
            ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g) T a)}
          ( eq-is-prop
            ( is-prop-is-decidable
              ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a)))
          ( ap
            ( λ w →
              h'-inl
                ( map-inv-equiv-count h (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
                ( map-equiv (pr1 w) (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
                (pr2 w)
                ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
                    ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                    ( map-equiv (pr1 w) (quotient-map-large-set-quotient (same-orbits-permutation-count g) a)) a)
                ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
                    ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                    ( map-equiv (pr1 w) (quotient-map-large-set-quotient (same-orbits-permutation-count g) a)) b))
            { x = pair ((equiv-count h) ∘e (inv-equiv-count h)) refl}
            { y = pair
              id-equiv
              ( ap
                ( λ f → map-equiv f (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
                ( right-inverse-law-equiv (equiv-count h)))}
            ( eq-pair-Σ
              ( right-inverse-law-equiv (equiv-count h))
              ( eq-is-prop
                ( is-prop-type-Prop
                  ( Id-Prop
                    ( large-quotient-Set (same-orbits-permutation-count g))
                    ( map-equiv-count h
                      ( map-inv-equiv-count h
                        ( quotient-map-large-set-quotient (same-orbits-permutation-count g) a)))
                    (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))))) ∙
            ( (ap
              (λ w →
                h'-inl
                  ( map-inv-equiv-count h (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
                  (quotient-map-large-set-quotient (same-orbits-permutation-count g) a)
                  ( ap
                    ( λ f → map-equiv f (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
                    ( right-inverse-law-equiv (equiv-count h)))
                  ( w)
                  ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
                      ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                      (quotient-map-large-set-quotient (same-orbits-permutation-count g) a) b))
              { x = is-decidable-type-class-large-set-quotient-same-orbits-permutation
                ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
                ( map-equiv id-equiv (quotient-map-large-set-quotient (same-orbits-permutation-count g) a)) a}
              { y =
                inl
                  ( related-eq-quotient (same-orbits-permutation-count g) a
                    ( quotient-map-large-set-quotient (same-orbits-permutation-count g) a) refl)}
              ( eq-is-prop ( is-prop-is-decidable
                ( is-prop-type-class-large-set-quotient ( same-orbits-permutation-count g)
                ( quotient-map-large-set-quotient (same-orbits-permutation-count g) a) a)))) ∙
              ( eq-effective-quotient' (same-orbits-permutation-count (composition-transposition-a-b g)) a T Q)))
      retr-h' T (inr NQ) (inl R) =
        tr
          (λ w → Id (h' (cases-inv-h' T (pr1 w) (pr2 w))) T)
          {x = pair (inr NQ) (inl R)}
          {y = pair
            (is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T a)
            (is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T b)}
          ( eq-is-prop
            ( is-prop-Σ (is-prop-is-decidable
              ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a))
              ( λ _ → is-prop-is-decidable
                ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b))))
          ( eq-effective-quotient' (same-orbits-permutation-count (composition-transposition-a-b g)) b T R)
      retr-h' T (inr NQ) (inr NR) =
        tr
          (λ w → Id (h' (cases-inv-h' T (pr1 w) (pr2 w))) T)
          {x = pair (inr NQ) (inr NR)}
          {y = pair
            (is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T a)
            (is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T b)}
          ( eq-is-prop
            ( is-prop-Σ (is-prop-is-decidable
              ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T a))
              ( λ _ → is-prop-is-decidable
                ( is-prop-type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) T b))))
          ( retr-h'-inr-inr T NQ NR
            ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
              ( pair (pr1 T) (H-conserves T NQ NR)) a)
            ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g
              ( pair (pr1 T) (H-conserves T NQ NR)) b))
      sec-h'-inl : (k : Fin (number-of-elements-count h)) →
        ( Q : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g) (map-equiv-count h k) a)) →
        ( R : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count g) (map-equiv-count h k) b)) →
        ( Q' : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
          (h'-inl k (map-equiv-count h k) refl Q R) a)) →
        ( R' : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
          (h'-inl k (map-equiv-count h k) refl Q R) b)) →
        Id (cases-inv-h' (h'-inl k (map-equiv-count h k) refl Q R) Q' R') (inl k)
      sec-h'-inl k (inl Q) R (inl Q') R' =
        ap inl
          ( is-injective-map-equiv (equiv-count h)
            ( ap (λ f → map-equiv f (quotient-map-large-set-quotient (same-orbits-permutation-count g) a))
              ( right-inverse-law-equiv (equiv-count h)) ∙
              ( eq-effective-quotient' (same-orbits-permutation-count g) a (map-equiv-count h k) Q)))
      sec-h'-inl k (inl Q) R (inr NQ') R' = ex-falso
        ( NQ'
          ( related-eq-quotient
            ( same-orbits-permutation-count (composition-transposition-a-b g))
            ( a)
            ( quotient-map-large-set-quotient
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( a))
            ( refl)))
      sec-h'-inl k (inr NQ) (inl R) Q' R' = ex-falso (NQ
        ( transitive-type-class-large-set-quotient (same-orbits-permutation-count g) (map-equiv-count h k) b a R
        ( symm-Eq-Rel (same-orbits-permutation-count g) P)))
      sec-h'-inl k (inr NQ) (inr NR) (inl Q') R' = ex-falso (NQ Q')
      sec-h'-inl k (inr NQ) (inr NR) (inr NQ') (inl R') = ex-falso (NR R')
      sec-h'-inl k (inr NQ) (inr NR) (inr NQ') (inr NR') =
        ap inl
          ( (ap (map-inv-equiv-count h)
            ( eq-pair-Σ
              refl
              ( eq-is-prop is-prop-type-trunc-Prop))) ∙
            ap (λ f → map-equiv f k) (left-inverse-law-equiv (equiv-count h)))
      sec-h'-inr :
        ( Q : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
          ( quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b) a)) →
        ( R : is-decidable (type-class-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g))
          ( quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b) b)) →
        Id (cases-inv-h' (quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b) Q R)
          ( inr star)
      sec-h'-inr (inl Q) R =
        ex-falso (not-same-orbits-transposition-same-orbits g P
          ( symm-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) Q))
      sec-h'-inr (inr Q) (inl R) = refl
      sec-h'-inr (inr Q) (inr NR) =
        ex-falso
          ( NR
            ( related-eq-quotient
              ( same-orbits-permutation-count (composition-transposition-a-b g))
              ( b)
              ( quotient-map-large-set-quotient
                ( same-orbits-permutation-count (composition-transposition-a-b g))
                ( b))
              ( refl)))
      sec-h' : (k : Fin (succ-ℕ (number-of-elements-count h))) →
        Id (inv-h' (h' k)) k 
      sec-h' (inl k) =
        sec-h'-inl k Q R
          ( is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))) (composition-transposition-a-b g)
            ( h'-inl k (map-equiv-count h k) refl Q R) a)
          ( is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX))) (composition-transposition-a-b g)
            ( h'-inl k (map-equiv-count h k) refl Q R) b)
        where
        Q : is-decidable (type-class-large-set-quotient (same-orbits-permutation (number-of-elements-count eX)
          (pair X (unit-trunc-Prop (equiv-count eX))) g) (map-equiv-count h k) a)
        Q = (is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))) g (map-equiv-count h k) a)
        R : is-decidable (type-class-large-set-quotient (same-orbits-permutation (number-of-elements-count eX)
          (pair X (unit-trunc-Prop (equiv-count eX))) g) (map-equiv-count h k) b)
        R = (is-decidable-type-class-large-set-quotient-same-orbits-permutation (number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX))) g (map-equiv-count h k) b)
      sec-h' (inr star) =
        sec-h'-inr
        ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
          ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) (composition-transposition-a-b g)
          ( quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b) a)
        ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
          ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) (composition-transposition-a-b g)
          ( quotient-map-large-set-quotient (same-orbits-permutation-count (composition-transposition-a-b g)) b) b)

  transf-same-orbits-count : (g : X ≃ X) →
    (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
    count
      ( large-set-quotient
        ( same-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))) →
      count
        ( large-set-quotient
          ( same-orbits-permutation
            ( number-of-elements-count eX)
            ( pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g)))
  transf-same-orbits-count g P h =
    pair
      ( succ-ℕ (number-of-elements-count h))
      ( pair
        ( h' g P h)
        ( is-equiv-has-inverse
          ( inv-h' g P h)
          ( λ T → retr-h' g P h T
            ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T a)
            ( is-decidable-type-class-large-set-quotient-same-orbits-permutation
              ( number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              ( composition-transposition-a-b g) T b))
          ( sec-h' g P h)))

  abstract
    number-orbits-composition-transposition : (g : X ≃ X) →
      (P : (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
      Id
        ( succ-ℕ
          ( number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g))
        ( number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
          ( composition-transposition-a-b g))
    number-orbits-composition-transposition g P =
      apply-universal-property-trunc-Prop
        ( has-finite-number-orbits-permutation
          ( number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( g))
        ( Id-Prop
        ( ℕ-Set)
        ( succ-ℕ (number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g))
        ( number-of-orbits-permutation (number-of-elements-count eX)
          ( pair X (unit-trunc-Prop (equiv-count eX)))
          ( composition-transposition-a-b g)))
        ( λ h →
          ( (ap (succ-ℕ ∘ number-of-elements-is-finite) (eq-is-prop is-prop-type-trunc-Prop)) ∙
            ( (ap (succ-ℕ ∘ pr1)
              ( all-elements-equal-has-finite-cardinality
                ( has-finite-cardinality-is-finite (unit-trunc-Prop h))
                ( has-finite-cardinality-count h))) ∙
              (ap pr1
                ( all-elements-equal-has-finite-cardinality
                  ( has-finite-cardinality-count (transf-same-orbits-count g P h))
                  (has-finite-cardinality-is-finite (unit-trunc-Prop (transf-same-orbits-count g P h)))) ∙
                ap number-of-elements-is-finite (eq-is-prop is-prop-type-trunc-Prop)))))

  abstract
    same-orbits-transposition-not-same-orbits : (g : X ≃ X) →
      (NP : ¬ (type-Eq-Rel (same-orbits-permutation-count g) a b)) →
      type-Eq-Rel (same-orbits-permutation-count (composition-transposition-a-b g)) a b
    same-orbits-transposition-not-same-orbits g NP =
      unit-trunc-Prop (pair (pr1 minimal-element-iterate-repeating) lemma)
      where
      minimal-element-iterate-repeating : minimal-element-ℕ (λ k → is-nonzero-ℕ k × Id (iterate k (map-equiv g) a) a)
      minimal-element-iterate-repeating = minimal-element-iterate-nonzero g a a (has-finite-orbits-permutation X eX g a)
      neq-iterate-nonzero-le-minimal-element :
        (k : ℕ) → is-nonzero-ℕ k × le-ℕ k (pr1 minimal-element-iterate-repeating) →
        ¬ (Id (iterate k (map-equiv g) a) a) × ¬ (Id (iterate k (map-equiv g) a) b)
      pr1 (neq-iterate-nonzero-le-minimal-element k (pair nz ineq)) = λ Q →
        contradiction-le-ℕ k (pr1 minimal-element-iterate-repeating) ineq
          (pr2 (pr2 minimal-element-iterate-repeating) k (pair nz Q))
      pr2 (neq-iterate-nonzero-le-minimal-element k (pair nz ineq)) = λ R → NP (unit-trunc-Prop (pair k R))
      equal-iterate-transposition-a : (k : ℕ) → le-ℕ k (pr1 minimal-element-iterate-repeating) →
        (Id (iterate k (map-equiv (composition-transposition-a-b g)) a) (iterate k (map-equiv g) a))
      equal-iterate-transposition-a k ineq =
        equal-iterate-transposition a g
          ( λ k' → (is-nonzero-ℕ k') × (le-ℕ k' (pr1 minimal-element-iterate-repeating)))
          ( neq-iterate-nonzero-le-minimal-element)
          ( λ n (pair _ s) nz → pair nz (transitive-le-ℕ n (succ-ℕ n) (pr1 minimal-element-iterate-repeating) (le-succ-ℕ {x = n}) s))
          ( k)
          ( cases-equal-iterate-transposition-a (has-decidable-equality-ℕ k zero-ℕ))
        where
        cases-equal-iterate-transposition-a : is-decidable (is-zero-ℕ k) →
          coprod (is-zero-ℕ k) (is-nonzero-ℕ k × le-ℕ k (pr1 minimal-element-iterate-repeating))
        cases-equal-iterate-transposition-a (inl s) = inl s
        cases-equal-iterate-transposition-a (inr s) = inr (pair s ineq)
      lemma : Id (iterate (pr1 minimal-element-iterate-repeating) (map-equiv (composition-transposition-a-b g)) a) b
      lemma =
        ( ap (λ n → iterate n (map-equiv (composition-transposition-a-b g)) a)
          ( pr2 (is-successor-k1) ∙ commutative-add-ℕ (pr1 is-successor-k1) (succ-ℕ zero-ℕ))) ∙
          ( (iterate-add-ℕ (succ-ℕ zero-ℕ) (pr1 is-successor-k1) (map-equiv (composition-transposition-a-b g)) a) ∙
            ( (ap
              ( map-equiv (composition-transposition-a-b g))
                ( equal-iterate-transposition-a (pr1 is-successor-k1)
                  ( tr (λ n → le-ℕ (pr1 is-successor-k1) n) (inv (pr2 is-successor-k1)) (le-succ-ℕ {x = pr1 is-successor-k1})))) ∙
              ( (ap
                ( λ n →
                  map-standard-transposition
                    ( has-decidable-equality-count eX)
                    ( np)
                    ( iterate n (map-equiv g) a))
                ( inv (pr2 is-successor-k1))) ∙
                ( ap
                  ( map-standard-transposition
                    ( has-decidable-equality-count eX)
                    ( np))
                  ( pr2 (pr1 (pr2 minimal-element-iterate-repeating))) ∙
                  ( left-computation-standard-transposition
                    ( has-decidable-equality-count eX)
                    np)))))
        where
        is-successor-k1 : is-successor-ℕ (pr1 minimal-element-iterate-repeating)
        is-successor-k1 = is-successor-is-nonzero-ℕ (pr1 (pr1 (pr2 minimal-element-iterate-repeating)))
  
  abstract
    number-orbits-composition-transposition' : (g : X ≃ X) →
      (NP : ¬ (type-Eq-Rel (same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g) a b)) →
      Id
        ( number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g)
        ( succ-ℕ
          ( number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            ( composition-transposition-a-b g)))
    number-orbits-composition-transposition' g NP =
      ( ap
        ( number-of-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))))
        ( inv ( eq-htpy-equiv ( composition-transposition-a-b-involution g)))) ∙
        ( inv
          ( number-orbits-composition-transposition
            ( composition-transposition-a-b g)
            ( same-orbits-transposition-not-same-orbits g NP)))

  abstract
    opposite-sign-composition-transposition-count : (g : X ≃ X) →
      Id
        (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g)
        (succ-Fin (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
          (composition-transposition-a-b g)))
    opposite-sign-composition-transposition-count g =
      cases-opposite-sign-composition-transposition
        (is-decidable-same-orbits-permutation (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g a b)
      where
      cases-opposite-sign-composition-transposition : is-decidable (type-Eq-Rel (same-orbits-permutation-count g) a b) →
        Id
          (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g)
          (succ-Fin (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            (composition-transposition-a-b g)))
      cases-opposite-sign-composition-transposition (inl P) =
        inv (is-involution-aut-Fin-two-ℕ equiv-succ-Fin
          (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) g)) ∙
          ap (λ k → succ-Fin (iterate (add-ℕ (number-of-elements-count eX) k) succ-Fin zero-Fin))
            (number-orbits-composition-transposition g P)
      cases-opposite-sign-composition-transposition (inr NP) =
        ap (λ k → iterate (add-ℕ (number-of-elements-count eX) k) succ-Fin zero-Fin)
          ( number-orbits-composition-transposition' g NP)

module _
  {l : Level} (X : UU l) (eX : count X)
  where
  
  abstract
    sign-list-transpositions-count :
      ( li : list (Σ (X → decidable-Prop l) (λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))) →
      Id
        ( iterate (length-list li) succ-Fin
          ( sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX))) id-equiv))
        ( sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
          ( permutation-list-transpositions li))
    sign-list-transpositions-count nil = refl
    sign-list-transpositions-count (cons t li) =
      ap succ-Fin
        ( (sign-list-transpositions-count li) ∙
          opposite-sign-composition-transposition-count X eX (pr1 two-elements-t) (pr1 (pr2 two-elements-t))
            ( pr1 (pr2 (pr2 two-elements-t))) (permutation-list-transpositions li )) ∙
        ( is-involution-aut-Fin-two-ℕ equiv-succ-Fin
          (sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
            (permutation-list-transpositions
              (cons (standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX)
                (pr1 (pr2 (pr2 two-elements-t)))) li))) ∙
          ( ap
            ( λ g → sign-permutation-orbit (number-of-elements-count eX) (pair X (unit-trunc-Prop (equiv-count eX)))
              (permutation-list-transpositions (cons g li)))
            { x = standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) (pr1 (pr2 (pr2 two-elements-t)))}
            { y = t}
            ( pr2 (pr2 (pr2 two-elements-t)))))
      where
      two-elements-t :
        Σ X (λ x → Σ X (λ y → Σ (¬ (Id x y)) (λ np → Id (standard-2-Element-Decidable-Subtype (has-decidable-equality-count eX) np) t)))
      two-elements-t = two-elements-transposition eX t
```
