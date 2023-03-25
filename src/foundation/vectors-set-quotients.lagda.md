# Vectors of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.vectors-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-products-set-quotients
open import foundation.coproduct-types
open import foundation.equality-cartesian-product-types
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.universal-property-set-quotients
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.identity-types public
open import foundation-core.homotopies
open import foundation-core.functions
open import foundation-core.equivalence-relations
open import foundation-core.equality-dependent-pair-types
open import foundation-core.retractions
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.equivalences
open import foundation-core.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`. Then, the set quotient of a vector with these types is the vector
of the set quotients of each `Ai`.

## Definition

### The induced relation on the vector of types

```agda
all-sim-Eq-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  ( Eq-Rel l2 (multivariable-input n A))
all-sim-Eq-Rel {l1} {l2} zero-ℕ A R = always-holds-Eq-Rel l2 (raise-unit l1)
all-sim-Eq-Rel (succ-ℕ n) A R =
  prod-Eq-Rel (R (inr star))
    ( all-sim-Eq-Rel n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)))
```

### The set quotient of a vector of types

```agda
set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  UU (l1 ⊔ l2)
set-quotient-vector n A R =
  multivariable-input n (λ i → ( set-quotient (R i)))

is-set-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  is-set (set-quotient-vector n A R)
is-set-set-quotient-vector zero-ℕ A R = is-set-raise-unit
is-set-set-quotient-vector (succ-ℕ n) A R =
  is-set-prod
  ( is-set-set-quotient (R (inr star)))
  ( is-set-set-quotient-vector n
    ( tail-functional-vec n A)
    ( λ x → R (inl x)))

set-quotient-vector-Set :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  Set (l1 ⊔ l2)
pr1 (set-quotient-vector-Set n A R) =
  set-quotient-vector n A R
pr2 (set-quotient-vector-Set n A R) =
  is-set-set-quotient-vector n A R

quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  multivariable-input n A →
  set-quotient-vector n A R
quotient-vector-map zero-ℕ A R a = raise-star
pr1 (quotient-vector-map (succ-ℕ n) A R (a0 , a)) =
  quotient-map (R (inr star)) (a0)
pr2 (quotient-vector-map (succ-ℕ n) A R a) =
  quotient-vector-map n
    ( tail-functional-vec n A)
    ( λ x → R (inl x))
    ( tail-multivariable-input n A a)

reflects-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  reflects-Eq-Rel (all-sim-Eq-Rel n A R) (quotient-vector-map n A R)
reflects-quotient-vector-map zero-ℕ A R p = refl
reflects-quotient-vector-map (succ-ℕ n) A R (p , p') =
  eq-pair
    ( apply-effectiveness-quotient-map' (R (inr star)) p)
    ( reflects-quotient-vector-map n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)) p')

reflecting-map-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  reflecting-map-Eq-Rel
    ( all-sim-Eq-Rel n A R)
    ( set-quotient-vector n A R)
pr1 (reflecting-map-quotient-vector-map n A R) =
  quotient-vector-map n A R
pr2 (reflecting-map-quotient-vector-map n A R) =
  reflects-quotient-vector-map n A R

lemma :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) (succ-ℕ n))
  ( R : (i : Fin (succ-ℕ n)) → Eq-Rel l2 (A i)) →
  ( set-quotient (R (inr star)) ×
    ( set-quotient-vector n
      ( tail-functional-vec n A)
      (λ x → R (inl x)))) ≃
    ( set-quotient (R (inr star)) ×
      ( set-quotient
        ( all-sim-Eq-Rel n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))))

equiv-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  set-quotient-vector n A R ≃ set-quotient (all-sim-Eq-Rel n A R)
pr1 (equiv-set-quotient-vector zero-ℕ A R) _ = quotient-map _ raise-star
pr1 (pr1 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = raise-star
pr2 (pr1 (pr2 (equiv-set-quotient-vector {l1} {l2} zero-ℕ A R))) =
  induction-set-quotient
    ( always-holds-Eq-Rel l2 (raise-unit l1))
    ( λ x → pair _ (is-set-set-quotient _ _ x))
    ( λ x → apply-effectiveness-quotient-map' _ raise-star)
pr1 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = raise-star
pr2 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) (map-raise star) = refl
equiv-set-quotient-vector (succ-ℕ n) A R =
  equivalence-reasoning
    set-quotient (R (inr star)) ×
        ( set-quotient-vector n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))
    ≃ set-quotient (R (inr star)) ×
        ( set-quotient
          (all-sim-Eq-Rel n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
       by lemma n A R
    ≃ set-quotient (all-sim-Eq-Rel (succ-ℕ n) A R)
       by (equiv-quotient-prod-prod-set-quotient _ _)
  -- where
  -- lemma :
  --   ( set-quotient (R (inr star)) ×
  --     ( set-quotient-vector n
  --       ( tail-functional-vec n A)
  --       (λ x → R (inl x)))) ≃
  --     ( set-quotient (R (inr star)) ×
  --       ( set-quotient
  --         ( all-sim-Eq-Rel n
  --           ( tail-functional-vec n A)
  --           ( λ x → R (inl x)))))
  -- pr1 (pr1 lemma (qa0 , qa)) = qa0
  -- pr2 (pr1 lemma (qa0 , qa)) = map-equiv (equiv-set-quotient-vector n _ _) qa
  -- pr1 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) = qa0
  -- pr2 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) =
  --   map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  -- pr2 (pr1 (pr2 lemma)) (qa0 , qa) =
  --   eq-pair refl (issec-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
  -- pr1 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) = qa0
  -- pr2 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) =
  --   map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  -- pr2 (pr2 (pr2 lemma)) (qa0 , qa) =
  --   eq-pair refl (isretr-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)

pr1 (pr1 (lemma n A R) (qa0 , qa)) = qa0
pr2 (pr1 (lemma n A R) (qa0 , qa)) = map-equiv (equiv-set-quotient-vector n _ _) qa 
pr1 (pr1 (pr1 (pr2 (lemma n A R))) (qa0 , qa)) = qa0
pr2 (pr1 (pr1 (pr2 (lemma n A R))) (qa0 , qa)) =
  map-inv-equiv (equiv-set-quotient-vector n _ _) qa
pr2 (pr1 (pr2 (lemma n A R))) (qa0 , qa) =
  eq-pair refl (issec-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
pr1 (pr1 (pr2 (pr2 (lemma n A R))) (qa0 , qa)) = qa0
pr2 (pr1 (pr2 (pr2 (lemma n A R))) (qa0 , qa)) =
  map-inv-equiv (equiv-set-quotient-vector n _ _) qa
pr2 (pr2 (pr2 (lemma n A R))) (qa0 , qa) =
  eq-pair refl (isretr-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)

-- pr1 (pr1 (lemma n A R)) (qa0 , qa) = qa0
-- pr2 (pr1 lemma n A R (qa0 , qa)) = map-equiv (equiv-set-quotient-vector n _ _) qa
-- pr1 (pr1 (pr1 (pr2 lemma)) n A R (qa0 , qa)) = qa0
-- pr2 (pr1 (pr1 (pr2 lemma n A R) (qa0 , qa)) =
--   map-inv-equiv (equiv-set-quotient-vector n _ _) qa
-- pr2 (pr1 (pr2 lemma)) n A R (qa0 , qa) =
--   eq-pair refl (issec-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
-- pr1 (pr1 (pr2 (pr2 lemma)) n A R (qa0 , qa)) = qa0
-- pr2 (pr1 (pr2 (pr2 lemma)) n A R (qa0 , qa)) =
--   map-inv-equiv (equiv-set-quotient-vector n _ _) qa
-- pr2 (pr2 (pr2 lemma)) n A R (qa0 , qa) =
--   eq-pair refl (isretr-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)

map-equiv-equiv-set-quotient-vector-quotient-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  ( map-equiv (equiv-set-quotient-vector n A R) ∘
    ( quotient-vector-map n A R)) ~
  ( quotient-map (all-sim-Eq-Rel n A R))
map-equiv-equiv-set-quotient-vector-quotient-map zero-ℕ A R (map-raise star) =
  refl
map-equiv-equiv-set-quotient-vector-quotient-map (succ-ℕ n) A R (a0 , a) =
  ap
    ( λ qa →
      map-equiv
        ( equiv-quotient-prod-prod-set-quotient _ _)
        ( quotient-map (R (inr star)) a0 , qa))
    ( map-equiv-equiv-set-quotient-vector-quotient-map n
        ( tail-functional-vec n A)
        ( λ x → R (inl x)) a) ∙
  ( triangle-uniqueness-prod-set-quotient
    ( R (inr star))
    ( all-sim-Eq-Rel n (λ z → tail-functional-vec n A z)
    ( λ i → R (inl i)))
    ( a0 , a))

inv-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  (X : Set l) →
  reflecting-map-Eq-Rel (all-sim-Eq-Rel n A R) (type-Set X) →
  ((set-quotient-vector n A R) → type-Set X)
inv-precomp-vector-set-quotient zero-ℕ A R X f (map-raise star) = pr1 f raise-star
inv-precomp-vector-set-quotient (succ-ℕ n) A R X f (qa0 , qa) =
  inv-precomp-set-quotient-prod-set-quotient
     ( R (inr star))
     ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
      X f
     (qa0 , map-equiv (equiv-set-quotient-vector n _ _) qa)

issec-inv-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  ( X : Set l) →
  sec (precomp-Set-Quotient (all-sim-Eq-Rel n A R) (set-quotient-vector-Set n A R) (reflecting-map-quotient-vector-map n A R) X)
pr1 (issec-inv-precomp-vector-set-quotient n A R X) = inv-precomp-vector-set-quotient n A R X
pr2 (issec-inv-precomp-vector-set-quotient {l1} {l2} {l3} zero-ℕ A R X) f =
  eq-pair-Σ (eq-htpy (λ { (map-raise star) → refl}))
   ( eq-is-prop (is-prop-reflects-Eq-Rel (always-holds-Eq-Rel l3 (raise-unit l2)) X (pr1 f) ))
pr2 (issec-inv-precomp-vector-set-quotient (succ-ℕ n) A R X) f =
  eq-pair-Σ
    (eq-htpy (λ (a0 , a) →
       goal (a0 , a)    ) )
    (eq-is-prop (is-prop-reflects-Eq-Rel (all-sim-Eq-Rel (succ-ℕ n) A R) X (pr1 f) ) )
  where
  lemmao :
    ( (a0 , a)  : A (inr star) × multivariable-input n (tail-functional-vec n A)) →
          Id
            (pr1
             ((precomp-Set-Quotient
               (prod-Eq-Rel (R (inr star))
                (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
               (prod-set-quotient-Set (R (inr star))
                (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
               (reflecting-map-prod-quotient-map (R (inr star))
                (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
               X
               ∘
               inv-precomp-set-quotient-prod-set-quotient (R (inr star))
               (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X)
              f)
             (a0 , a))
            (pr1 (id f) (a0 , a))
  lemmao (a0 , a) =   htpy-eq (ap pr1 (issec-inv-precomp-set-quotient-prod-set-quotient
          (R (inr star))
          (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X f  ))
          (a0 , a)
  paf :
    ( (a0 , a)  : A (inr star) × multivariable-input n (tail-functional-vec n A)) →
      inv-precomp-set-quotient-prod-set-quotient (R (inr star))
      (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X f
      (quotient-map (R (inr star)) a0 ,
       map-equiv
       (equiv-set-quotient-vector n (tail-functional-vec n A)
        (λ x → R (inl x)))
       (quotient-vector-map n (tail-functional-vec n A) (λ x → R (inl x))
        (tail-multivariable-input n A (a0 , a))))
      ＝
        (inv-precomp-set-quotient-prod-set-quotient (R (inr star))
        (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X f)
        (quotient-map (R (inr star)) a0 ,
         quotient-map (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) a)
  paf (a0 , a) =
    ap (inv-precomp-set-quotient-prod-set-quotient (R (inr star))
        (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X f)
       (eq-pair-Σ refl (map-equiv-equiv-set-quotient-vector-quotient-map n _ _ a))
  goal :
    ( (a0 , a)  : A (inr star) × multivariable-input n (tail-functional-vec n A)) →
    inv-precomp-set-quotient-prod-set-quotient
      (R (inr star))
      (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X f
      (quotient-map (R (inr star)) (a0) ,
       map-equiv (equiv-set-quotient-vector n (tail-functional-vec n A) (λ x → R (inl x)))
       (pr2 (quotient-vector-map (succ-ℕ n) A R (a0 , a)))) ＝ pr1 f (a0 , a)
  goal (a0 , a) = paf (a0 , a) ∙ lemmao (a0 , a)

isretr-inv-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  ( X : Set l) →
  retr (precomp-Set-Quotient (all-sim-Eq-Rel n A R) (set-quotient-vector-Set n A R) (reflecting-map-quotient-vector-map n A R) X)
pr1 (isretr-inv-precomp-vector-set-quotient n A R X) = inv-precomp-vector-set-quotient n A R X 
pr2 (isretr-inv-precomp-vector-set-quotient zero-ℕ A R X) f =
  eq-htpy (λ { (map-raise star) → refl})
pr2 (isretr-inv-precomp-vector-set-quotient (succ-ℕ n) A R X) f =
  goal'
  where
   refl-map :
    reflecting-map-Eq-Rel
      (prod-Eq-Rel (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      (type-Set X)
   refl-map =
        precomp-Set-Quotient
        (prod-Eq-Rel (R (inr star))
         (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
        (set-quotient-vector-Set (succ-ℕ n) A R)
        (reflecting-map-quotient-vector-map (succ-ℕ n) A R) X f
   una :
      type-hom-Set
      (set-quotient-vector-Set (succ-ℕ n) A R )
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
   una (qa0' , qa') = (qa0' , map-equiv (equiv-set-quotient-vector n _ _) qa')
   inv-una :
      type-hom-Set
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      (set-quotient-vector-Set (succ-ℕ n) A R )
   inv-una (qa0' , qa') = (qa0' , map-inv-equiv (equiv-set-quotient-vector n _ _) qa')
   need :
      type-hom-Set
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      X
   need = f ∘ inv-una

   part1 : (need ∘ una) ＝ f
   part1 = eq-htpy λ a → ap f (eq-pair-Σ refl (isretr-map-inv-equiv (equiv-set-quotient-vector n _ _) (pr2 a)))


   part20 :
     pr1 refl-map ＝ (need ∘ (una ∘ (quotient-vector-map _ A R)))
   part20 = ap (λ - → - ∘ quotient-vector-map _ A R) (inv part1)

   part21 :
    reflects-Eq-Rel (all-sim-Eq-Rel _ A R)
         (need ∘ (una ∘ (quotient-vector-map _ A R)))
   part21 = tr (reflects-Eq-Rel (all-sim-Eq-Rel _ A R)) part20 (pr2 refl-map)

   part275' :
        (λ (a0 , a) →
        pair (quotient-map (R (inr star)) a0)
         (quotient-map (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) a))
      ＝  (una ∘ (quotient-vector-map _ A R))
   part275' = eq-htpy λ (a0 , a) →
     eq-pair-Σ refl (inv (map-equiv-equiv-set-quotient-vector-quotient-map _ _ _ a) )

   part278 :
        precomp-Set-Quotient
        (prod-Eq-Rel (R (inr star))
         (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       (reflecting-map-prod-quotient-map (R (inr star)) (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       X need
      ＝ refl-map
   part278 = eq-pair-Σ ((ap (λ - → need ∘ -) part275') ∙ inv (part20))
     (eq-is-prop (is-prop-reflects-Eq-Rel (prod-Eq-Rel (R (inr star))
        (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))) _ _  ))

   part278' :
        (inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X
        (precomp-Set-Quotient
        (prod-Eq-Rel (R (inr star))
         (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       (reflecting-map-prod-quotient-map (R (inr star)) (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       X need))
      ＝ (inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X refl-map)
   part278' = ap (inv-precomp-set-quotient-prod-set-quotient _ _ _) part278

   part279 :
        (inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X
        (precomp-Set-Quotient
        (prod-Eq-Rel (R (inr star))
         (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
      (prod-set-quotient-Set (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       (reflecting-map-prod-quotient-map (R (inr star))
       (all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))))
       X need))
      ＝ need        
   part279 = 
     isretr-inv-precomp-set-quotient-prod-set-quotient
         ( R (inr star)) ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x))) X
          need
   part290 :
      (inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X refl-map) ＝ need
   part290 = inv part278' ∙ part279

   goal' :
     ((inv-precomp-set-quotient-prod-set-quotient
      ( R (inr star))
      ( all-sim-Eq-Rel n (tail-functional-vec n A) (λ x → R (inl x)))
       X refl-map) ∘ una)  ＝
      f
   goal' = ap (λ - → - ∘ una) part290 ∙ part1 
```
