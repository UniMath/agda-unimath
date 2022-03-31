# 2-element subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-subtypes where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.congruence-natural-numbers using
  ( cong-zero-ℕ'; trans-cong-ℕ; concatenate-cong-eq-ℕ; symm-cong-ℕ; scalar-invariant-cong-ℕ')
open import elementary-number-theory.distance-natural-numbers using
  ( dist-ℕ; rewrite-left-add-dist-ℕ; symmetric-dist-ℕ)
open import elementary-number-theory.modular-arithmetic-standard-finite-types using
  ( mod-succ-ℕ; mod-two-ℕ; eq-mod-succ-cong-ℕ; add-Fin; ap-add-Fin; cong-add-Fin;
    dist-Fin; ap-dist-Fin; cong-dist-Fin; mul-Fin; ap-mul-Fin; left-zero-law-mul-Fin;
    is-zero-mod-succ-ℕ; cong-eq-mod-succ-ℕ; cong-add-ℕ)
open import elementary-number-theory.multiplication-natural-numbers using (mul-ℕ)
open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import elementary-number-theory.equality-natural-numbers using (has-decidable-equality-ℕ)
open import elementary-number-theory.well-ordering-principle-standard-finite-types using
  ( exists-not-not-forall-count)

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using
  ( is-decidable; is-decidable-equiv; is-decidable-neg; dn-elim-is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop;
    equiv-bool-decidable-Prop)
open import foundation.decidable-subtypes using (decidable-subtype; type-decidable-subtype)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso; equiv-is-empty; empty-Prop)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using (_≃_; _∘e_; inv-equiv; is-equiv-has-inverse)
open import foundation.equivalence-relations using (Eq-Rel)
open import foundation.functions using (_∘_; id)
open import foundation.identity-types using (Id; refl; inv; ap; ap-binary; _∙_)
open import foundation.injective-maps using (is-injective; is-prop-is-injective)
open import foundation.intersection using (intersection-decidable-subtype)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop;
    trunc-Prop)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-function-type; eq-is-prop)
open import foundation.sets using (Id-Prop)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)
open import foundation.unordered-pairs using
  ( unordered-pair; type-unordered-pair; element-unordered-pair;
    has-two-elements-type-unordered-pair)

open import univalent-combinatorics.2-element-types using (type-2-Element-Type)
open import univalent-combinatorics.decidable-subtypes using (is-finite-decidable-subtype)
open import univalent-combinatorics.dependent-product-finite-types using (is-finite-Π)
open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin; has-decidable-equality-is-finite; is-set-is-finite)
open import univalent-combinatorics.equality-standard-finite-types using (Fin-Set)
open import univalent-combinatorics.finite-types using
  ( has-cardinality; UU-Fin-Level; type-UU-Fin-Level; mere-equiv-UU-Fin; is-finite; 
    equiv-has-cardinality-id-number-of-elements-is-finite; number-of-elements-is-finite;
    is-finite-type-UU-Fin-Level; is-finite-equiv; is-finite-Fin;
    number-of-elements-has-finite-cardinality; has-finite-cardinality-is-finite;
    all-elements-equal-has-finite-cardinality; has-finite-cardinality;
    is-finite-has-finite-cardinality; mere-equiv-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; one-Fin; equiv-bool-Fin-two-ℕ; nat-Fin; is-zero-nat-zero-Fin)
open import univalent-combinatorics.symmetric-difference using
  (eq-symmetric-difference; symmetric-difference-decidable-subtype)
```

## Idea

...

## Definition

```agda
module _
  {l1 l2 : Level} (X : UU l1)
  where

  2-Element-Subtype : UU (l1 ⊔ lsuc l2)
  2-Element-Subtype = Σ (X → UU-Prop l2) λ P → has-cardinality 2 (Σ X (λ x → type-Prop (P x)))
  
  decidable-2-Element-Subtype : UU (l1 ⊔ lsuc l2)
  decidable-2-Element-Subtype =
    Σ (X → decidable-Prop l2) λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))

module _
  {l1 l2 : Level} (n : ℕ) (X : UU-Fin-Level l1 n)
  where

  is-finite-2-decidable-Element-Subtype :
    is-finite (decidable-2-Element-Subtype {l2 = l2} (type-UU-Fin-Level X))
  is-finite-2-decidable-Element-Subtype =
    is-finite-decidable-subtype
      (λ P →
        pair
          ( has-cardinality 2 (Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x))))
          ( pair
            ( is-prop-type-trunc-Prop)
            ( is-decidable-equiv
              ( equiv-has-cardinality-id-number-of-elements-is-finite
                ( Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x)))
                ( is-finite-decidable-subtype P (is-finite-type-UU-Fin-Level X)) 2)
              ( has-decidable-equality-ℕ
                ( number-of-elements-is-finite (is-finite-decidable-subtype P (is-finite-type-UU-Fin-Level X)))
                ( 2)))))
      ( is-finite-Π
        ( is-finite-type-UU-Fin-Level X)
        ( λ x → is-finite-equiv (inv-equiv equiv-bool-decidable-Prop ∘e equiv-bool-Fin-two-ℕ) is-finite-Fin))

  D : UU (l1 ⊔ lsuc l2)
  D = ((pair P H) : decidable-2-Element-Subtype {l2 = l2} (type-UU-Fin-Level X)) →
    Σ (type-UU-Fin-Level X) (λ x → type-decidable-Prop (P x))

  decidable-2-element-subtype-subtype-pointwise-difference :
    D → D → decidable-2-Element-Subtype (type-UU-Fin-Level X) → decidable-Prop (l1 ⊔ l2)
  pr1 (decidable-2-element-subtype-subtype-pointwise-difference d d' Y) =
    ¬ (Id (d Y) (d' Y))
  pr1 (pr2 (decidable-2-element-subtype-subtype-pointwise-difference d d' Y)) =
    is-prop-neg
  pr2 (pr2 (decidable-2-element-subtype-subtype-pointwise-difference d d' Y)) =
    is-decidable-neg
      ( has-decidable-equality-is-finite
        ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
        ( d Y)
        ( d' Y))

  is-finite-subtype-pointwise-difference :
    (d d' : D) →
    is-finite
      ( Σ
        ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
        ( λ Y → type-decidable-Prop (decidable-2-element-subtype-subtype-pointwise-difference d d' Y)))
  is-finite-subtype-pointwise-difference d d' =
    is-finite-decidable-subtype
      ( decidable-2-element-subtype-subtype-pointwise-difference d d')
      ( is-finite-2-decidable-Element-Subtype)

  phi : D → D → Fin 2
  phi d d' = mod-two-ℕ (number-of-elements-is-finite (is-finite-subtype-pointwise-difference d d'))

  R : Eq-Rel lzero D
  pr1 R d d' = Id-Prop (Fin-Set 2) zero-Fin (phi d d')
  pr1 (pr2 R) {d} =
    ap
      ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
      ( all-elements-equal-has-finite-cardinality
        ( pair 0 (unit-trunc-Prop (equiv-is-empty id (λ (pair _ np) → np refl))))
        ( has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d)))
  pr1 (pr2 (pr2 R)) {d} {d'} p =
    p ∙
      ap
        ( mod-two-ℕ ∘ number-of-elements-has-finite-cardinality)
        ( all-elements-equal-has-finite-cardinality
          ( has-finite-cardinality-d'-d)
          ( has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d' d)))
    where
    has-finite-cardinality-d'-d :
      has-finite-cardinality
        ( Σ
          ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
          ( λ Y → type-decidable-Prop (decidable-2-element-subtype-subtype-pointwise-difference d' d Y)))
    pr1 has-finite-cardinality-d'-d =
      pr1 (has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d'))
    pr2 has-finite-cardinality-d'-d =
      apply-universal-property-trunc-Prop
        ( pr2 (has-finite-cardinality-is-finite (is-finite-subtype-pointwise-difference d d')))
        ( trunc-Prop
          ( Fin (pr1 has-finite-cardinality-d'-d) ≃
            ( Σ (decidable-2-Element-Subtype (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d' Y) (d Y))))))
        ( λ h → unit-trunc-Prop (h' ∘e h))
      where
      h' :
        (Σ (decidable-2-Element-Subtype (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d Y) (d' Y))) ≃
          Σ (decidable-2-Element-Subtype (type-UU-Fin-Level X)) (λ Y → ¬ (Id (d' Y) (d Y))))
      pr1 h' (pair Y np) = pair Y (λ p' → np (inv p'))
      pr2 h' =
        is-equiv-has-inverse
          ( λ (pair Y np) → pair Y (λ p' → np (inv p')))
          ( λ (pair Y np) → eq-pair-Σ refl (eq-is-prop is-prop-neg))
          ( λ (pair Y np) → eq-pair-Σ refl (eq-is-prop is-prop-neg))
  pr2 (pr2 (pr2 R)) {d1} {d2} {d3} p1 p2 =
    inv
      ( is-zero-mod-succ-ℕ
        ( 1)
        ( dist-ℕ (add-ℕ k1 k2) (mul-ℕ 2 k'))
        ( trans-cong-ℕ
          ( 2)
          ( add-ℕ k1 k2)
          ( zero-ℕ)
          ( mul-ℕ 2 k')
          ( concatenate-cong-eq-ℕ 2
            { x1 = add-ℕ k1 k2}
            ( symm-cong-ℕ 2
              ( add-ℕ (nat-Fin (phi d1 d2)) (nat-Fin (phi d2 d3)))
              ( add-ℕ k1 k2)
              ( cong-add-ℕ k1 k2))
            ( ap-binary
              ( add-ℕ)
              ( ap nat-Fin (inv p1) ∙ is-zero-nat-zero-Fin {k = 2})
              ( ap nat-Fin (inv p2) ∙ is-zero-nat-zero-Fin {k = 2})))
          ( scalar-invariant-cong-ℕ' 2 0 2 k' (cong-zero-ℕ' 2)))) ∙
      (ap
        ( mod-two-ℕ)
        ( ( symmetric-dist-ℕ (add-ℕ k1 k2) (mul-ℕ 2 k')) ∙
          ( inv
            ( rewrite-left-add-dist-ℕ
              ( k)
              ( mul-ℕ 2 k')
              ( add-ℕ k1 k2)
              ( inv
                ( eq-symmetric-difference
                  ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
                  ( is-finite-2-decidable-Element-Subtype)
                  ( decidable-2-element-subtype-subtype-pointwise-difference d1 d2)
                  ( decidable-2-element-subtype-subtype-pointwise-difference d2 d3)))) ∙
           ( ap
             ( number-of-elements-has-finite-cardinality)
             {!!}))) ∙
       {!!})
    where
    k : ℕ
    k =
      number-of-elements-is-finite
        ( is-finite-decidable-subtype
          ( symmetric-difference-decidable-subtype
            ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
            ( decidable-2-element-subtype-subtype-pointwise-difference d1 d2)
            ( decidable-2-element-subtype-subtype-pointwise-difference d2 d3))
          ( is-finite-2-decidable-Element-Subtype))
    k1 : ℕ
    k1 = number-of-elements-is-finite (is-finite-subtype-pointwise-difference d1 d2)
    k2 : ℕ
    k2 = number-of-elements-is-finite (is-finite-subtype-pointwise-difference d2 d3)
    k' : ℕ
    k' =
      number-of-elements-is-finite
        ( is-finite-decidable-subtype
          ( intersection-decidable-subtype
            ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
            ( decidable-2-element-subtype-subtype-pointwise-difference d1 d2)
            ( decidable-2-element-subtype-subtype-pointwise-difference d2 d3))
          ( is-finite-2-decidable-Element-Subtype))
    e :
      ( type-decidable-subtype
        ( symmetric-difference-decidable-subtype
          ( decidable-2-Element-Subtype (type-UU-Fin-Level X))
          ( decidable-2-element-subtype-subtype-pointwise-difference d1 d2)
          ( decidable-2-element-subtype-subtype-pointwise-difference d2 d3)) ≃
        type-decidable-subtype
          ( decidable-2-element-subtype-subtype-pointwise-difference d1 d3))
    pr1 (pr1 e (pair Y G)) = Y
    pr2 (pr1 e (pair Y (inl (pair np nnq)))) r = 
      np (r ∙
        inv
          ( dn-elim-is-decidable
            ( Id (d2 Y) (d3 Y))
            ( has-decidable-equality-is-finite
              ( is-finite-decidable-subtype
                ( pr1 Y)
                ( is-finite-type-UU-Fin-Level X))
              ( d2 Y)
              ( d3 Y))
            ( nnq)))
    pr2 (pr1 e (pair Y (inr (pair nnp nq)))) r = 
      nq
        ( (inv
          ( dn-elim-is-decidable
            ( Id (d1 Y) (d2 Y))
            ( has-decidable-equality-is-finite
              ( is-finite-decidable-subtype
                ( pr1 Y)
                ( is-finite-type-UU-Fin-Level X))
              (d1 Y)
              (d2 Y))
            ( nnp))) ∙
        ( r))
    pr2 e = is-equiv-has-inverse inv-e {!!} {!!}
      where
      cases-inv-e : (Y : decidable-2-Element-Subtype (type-UU-Fin-Level X)) →
        ¬ (Id (d1 Y) (d3 Y)) → (is-decidable (Id (d1 Y) (d2 Y))) →
        is-decidable (Id (d2 Y) (d3 Y)) →
        coprod
          (¬ (Id (d1 Y) (d2 Y)) × ¬ (¬ (Id (d2 Y) (d3 Y))))
          (¬ (¬ (Id (d1 Y) (d2 Y))) × ¬ (Id (d2 Y) (d3 Y)))
      cases-inv-e Y nr (inl p) (inl q) = ex-falso (nr (p ∙ q))
      cases-inv-e Y nr (inl p) (inr nq) = inr (pair (λ f → f p) nq)
      cases-inv-e Y nr (inr np) (inl q) = inl (pair np (λ f → f q))
      cases-inv-e Y nr (inr np) (inr nq) =
        ex-falso
          (apply-universal-property-trunc-Prop
            ( pr2 Y)
            ( empty-Prop)
            ( λ h → {!!}))
      inv-e : type-decidable-subtype
                (decidable-2-element-subtype-subtype-pointwise-difference d1 d3) →
              type-decidable-subtype
                (symmetric-difference-decidable-subtype
                  (decidable-2-Element-Subtype (type-UU-Fin-Level X))
                  (decidable-2-element-subtype-subtype-pointwise-difference d1 d2)
                  (decidable-2-element-subtype-subtype-pointwise-difference d2 d3))
      pr1 (inv-e (pair Y nr)) = Y
      pr2 (inv-e (pair Y nr)) =
        cases-inv-e
          ( Y)
          ( nr)
          ( has-decidable-equality-is-finite
            ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
            ( d1 Y)
            ( d2 Y))
          ( has-decidable-equality-is-finite
            ( is-finite-decidable-subtype (pr1 Y) (is-finite-type-UU-Fin-Level X))
            ( d2 Y)
            ( d3 Y)) 

{-
module _
  {l : Level} {A : UU l}
  where

  is-injective-map-Fin-two-ℕ :
    (f : Fin 2 → A) →
    ¬ (Id (f zero-Fin) (f one-Fin)) → is-injective f
  is-injective-map-Fin-two-ℕ f H {inl (inr star)} {inl (inr star)} p = refl
  is-injective-map-Fin-two-ℕ f H {inl (inr star)} {inr star} p = ex-falso (H p)
  is-injective-map-Fin-two-ℕ f H {inr star} {inl (inr star)} p =
    ex-falso (H (inv p))
  is-injective-map-Fin-two-ℕ f H {inr star} {inr star} p = refl
  
  is-injective-element-unordered-pair :
    (p : unordered-pair A) →
    ¬ ( (x y : type-unordered-pair p) →
        Id (element-unordered-pair p x) (element-unordered-pair p y)) →
    is-injective (element-unordered-pair p)
  is-injective-element-unordered-pair (pair X f) H {x} {y} p =
    apply-universal-property-trunc-Prop
      ( has-two-elements-type-unordered-pair (pair X f))
      ( Id-Prop (set-UU-Fin X) x y)
      ( λ h → {!!})
    where
    first-element : (Fin 2 ≃ (type-2-Element-Type X)) →
      Σ (type-2-Element-Type X) (λ x → ¬ ((y : type-2-Element-Type X) → Id (f x) (f y)))
    first-element h =
      exists-not-not-forall-count (λ z → (w : type-2-Element-Type X) → Id (f z) (f w)) (λ z → {!!})
        {!!} {!!}
    two-elements-different-image : Σ (type-2-Element-Type X) (λ x → Σ (type-2-Element-Type X) (λ y → ¬ (Id (f x) (f y))))
    two-elements-different-image = {!!}
-}
```
