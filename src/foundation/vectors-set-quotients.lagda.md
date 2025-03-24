# Vectors of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.vectors-set-quotients
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-products-set-quotients funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.function-extensionality funext
open import foundation.multivariable-operations funext univalence truncations
open import foundation.products-equivalence-relations funext univalence truncations
open import foundation.raising-universe-levels-unit-type
open import foundation.reflecting-maps-equivalence-relations funext univalence truncations
open import foundation.set-quotients funext univalence truncations
open import foundation.sets funext univalence
open import foundation.unit-type
open import foundation.universal-property-set-quotients funext univalence truncations
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalence-relations funext univalence truncations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.raising-universe-levels
open import foundation-core.retractions
open import foundation-core.sections

open import linear-algebra.vectors funext univalence truncations

open import univalent-combinatorics.standard-finite-types funext univalence truncations
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`. Then, the set quotient of a vector with these types is the vector
of the set quotients of each `Ai`.

## Definition

### The induced relation on the vector of types

```agda
all-sim-equivalence-relation :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( equivalence-relation l2 (multivariable-input n A))
all-sim-equivalence-relation {l1} {l2} zero-ℕ A R =
  raise-indiscrete-equivalence-relation l2 (raise-unit l1)
all-sim-equivalence-relation (succ-ℕ n) A R =
  product-equivalence-relation (R (inr star))
    ( all-sim-equivalence-relation n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)))
```

### The set quotient of a vector of types

```agda
set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  UU (l1 ⊔ l2)
set-quotient-vector n A R =
  multivariable-input n (λ i → ( set-quotient (R i)))

is-set-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  is-set (set-quotient-vector n A R)
is-set-set-quotient-vector zero-ℕ A R = is-set-raise-unit
is-set-set-quotient-vector (succ-ℕ n) A R =
  is-set-product
  ( is-set-set-quotient (R (inr star)))
  ( is-set-set-quotient-vector n
    ( tail-functional-vec n A)
    ( λ x → R (inl x)))

set-quotient-vector-Set :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  Set (l1 ⊔ l2)
pr1 (set-quotient-vector-Set n A R) =
  set-quotient-vector n A R
pr2 (set-quotient-vector-Set n A R) =
  is-set-set-quotient-vector n A R

quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
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
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  reflects-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( quotient-vector-map n A R)
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
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  reflecting-map-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( set-quotient-vector n A R)
pr1 (reflecting-map-quotient-vector-map n A R) =
  quotient-vector-map n A R
pr2 (reflecting-map-quotient-vector-map n A R) =
  reflects-quotient-vector-map n A R

equiv-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  set-quotient-vector n A R ≃ set-quotient (all-sim-equivalence-relation n A R)
pr1 (equiv-set-quotient-vector zero-ℕ A R) _ = quotient-map _ raise-star
pr1 (pr1 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = raise-star
pr2 (pr1 (pr2 (equiv-set-quotient-vector {l1} {l2} zero-ℕ A R))) =
  induction-set-quotient
    ( raise-indiscrete-equivalence-relation l2 (raise-unit l1))
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
          (all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
      by lemma
    ≃ set-quotient (all-sim-equivalence-relation (succ-ℕ n) A R)
      by (equiv-quotient-product-product-set-quotient _ _)
  where
  lemma :
    ( set-quotient (R (inr star)) ×
      ( set-quotient-vector n
        ( tail-functional-vec n A)
        (λ x → R (inl x)))) ≃
      ( set-quotient (R (inr star)) ×
        ( set-quotient
          ( all-sim-equivalence-relation n
            ( tail-functional-vec n A)
            ( λ x → R (inl x)))))
  pr1 (pr1 lemma (qa0 , qa)) = qa0
  pr2 (pr1 lemma (qa0 , qa)) = map-equiv (equiv-set-quotient-vector n _ _) qa
  pr1 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) = qa0
  pr2 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) =
    map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  pr2 (pr1 (pr2 lemma)) (qa0 , qa) =
    eq-pair refl (is-section-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
  pr1 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) = qa0
  pr2 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) =
    map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  pr2 (pr2 (pr2 lemma)) (qa0 , qa) =
    eq-pair
      ( refl)
      ( is-retraction-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)

map-equiv-equiv-set-quotient-vector-quotient-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( map-equiv (equiv-set-quotient-vector n A R) ∘
    ( quotient-vector-map n A R)) ~
  ( quotient-map (all-sim-equivalence-relation n A R))
map-equiv-equiv-set-quotient-vector-quotient-map zero-ℕ A R (map-raise star) =
  refl
map-equiv-equiv-set-quotient-vector-quotient-map (succ-ℕ n) A R (a0 , a) =
  ap
    ( λ qa →
      map-equiv
        ( equiv-quotient-product-product-set-quotient _ _)
        ( quotient-map (R (inr star)) a0 , qa))
    ( map-equiv-equiv-set-quotient-vector-quotient-map n
        ( tail-functional-vec n A)
        ( λ x → R (inl x)) a) ∙
  ( triangle-uniqueness-product-set-quotient
    ( R (inr star))
    ( all-sim-equivalence-relation n (λ z → tail-functional-vec n A z)
    ( λ i → R (inl i)))
    ( a0 , a))

inv-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  (X : Set l) →
  reflecting-map-equivalence-relation
    ( all-sim-equivalence-relation n A R)
    ( type-Set X) →
  ((set-quotient-vector n A R) → type-Set X)
inv-precomp-vector-set-quotient zero-ℕ A R X f (map-raise star) =
  pr1 f raise-star
inv-precomp-vector-set-quotient (succ-ℕ n) A R X f (qa0 , qa) =
  inv-precomp-set-quotient-product-set-quotient
    ( R (inr star))
    ( all-sim-equivalence-relation n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)))
    ( X)
    ( f)
    ( qa0 , map-equiv (equiv-set-quotient-vector n _ _) qa)

abstract
  is-section-inv-precomp-vector-set-quotient :
    { l l1 l2 : Level}
    ( n : ℕ)
    ( A : functional-vec (UU l1) n)
    ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
    ( X : Set l) →
    ( precomp-Set-Quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( X)) ∘
    ( inv-precomp-vector-set-quotient n A R X) ~
    ( id)
  is-section-inv-precomp-vector-set-quotient {l} {l1} {l2} 0 A R X f =
    eq-pair-Σ
      ( eq-htpy (λ where (map-raise star) → refl))
      ( eq-is-prop
        ( is-prop-reflects-equivalence-relation
          ( raise-indiscrete-equivalence-relation l2 (raise-unit l1))
          ( X)
          ( map-reflecting-map-equivalence-relation _ f)))
  is-section-inv-precomp-vector-set-quotient (succ-ℕ n) A R X f =
    eq-pair-Σ
      ( eq-htpy
        ( λ (a0 , a) →
          ( ap
            ( inv-precomp-set-quotient-product-set-quotient
              ( R (inr star))
              ( all-sim-equivalence-relation n
                ( tail-functional-vec n A)
                ( λ x → R (inl x))) X f)
            ( eq-pair-eq-fiber
              ( map-equiv-equiv-set-quotient-vector-quotient-map n _ _ a)) ∙
          ( htpy-eq
            ( ap
              ( map-reflecting-map-equivalence-relation _)
              ( is-section-inv-precomp-set-quotient-product-set-quotient
                ( R (inr star))
                ( all-sim-equivalence-relation n
                  ( tail-functional-vec n A)
                  ( λ x → R (inl x))) X f))
            ( a0 , a)))))
      ( eq-is-prop
        ( is-prop-reflects-equivalence-relation
          ( all-sim-equivalence-relation (succ-ℕ n) A R)
          ( X)
          ( map-reflecting-map-equivalence-relation _ f)))

section-precomp-vector-set-quotient :
  { l l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  ( X : Set l) →
  ( section
    ( precomp-Set-Quotient
      ( all-sim-equivalence-relation n A R)
      ( set-quotient-vector-Set n A R)
      ( reflecting-map-quotient-vector-map n A R)
      ( X)))
pr1 (section-precomp-vector-set-quotient n A R X) =
  inv-precomp-vector-set-quotient n A R X
pr2 (section-precomp-vector-set-quotient n A R X) =
  is-section-inv-precomp-vector-set-quotient n A R X

abstract
  is-retraction-inv-precomp-vector-set-quotient :
    { l l1 l2 : Level}
    ( n : ℕ)
    ( A : functional-vec (UU l1) n)
    ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
    ( X : Set l) →
    ( retraction
      ( precomp-Set-Quotient
        ( all-sim-equivalence-relation n A R)
        ( set-quotient-vector-Set n A R)
        ( reflecting-map-quotient-vector-map n A R)
        ( X)))
  pr1 (is-retraction-inv-precomp-vector-set-quotient n A R X) =
    inv-precomp-vector-set-quotient n A R X
  pr2 (is-retraction-inv-precomp-vector-set-quotient zero-ℕ A R X) f =
    eq-htpy (λ where (map-raise star) → refl)
  pr2 (is-retraction-inv-precomp-vector-set-quotient (succ-ℕ n) A R X) f =
    ap (_∘ set-quotient-vector-product-set-quotient)
      is-inv-map-inv-equiv-f ∙ lemma-f
    where
    precomp-f :
      reflecting-map-equivalence-relation
        ( product-equivalence-relation (R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
        ( type-Set X)
    precomp-f =
      precomp-Set-Quotient
        ( product-equivalence-relation (R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
        ( set-quotient-vector-Set (succ-ℕ n) A R)
        ( reflecting-map-quotient-vector-map (succ-ℕ n) A R) X f

    set-quotient-vector-product-set-quotient :
      ( set-quotient-vector (succ-ℕ n) A R) →
      ( product-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
    set-quotient-vector-product-set-quotient (qa0' , qa') =
      (qa0' , map-equiv (equiv-set-quotient-vector n _ _) qa')

    map-inv-equiv-f :
      ( product-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))) →
      ( type-Set X)
    map-inv-equiv-f (qa0 , qa) =
      f (qa0 , map-inv-equiv (equiv-set-quotient-vector n _ _) qa)

    lemma-f : (map-inv-equiv-f ∘ set-quotient-vector-product-set-quotient) ＝ f
    lemma-f =
      eq-htpy
        ( λ (qa0 , qa) →
          ( ap f
            ( eq-pair-eq-fiber
              ( is-retraction-map-inv-equiv
                ( equiv-set-quotient-vector n _ _)
                ( qa)))))

    is-retraction-inv-precomp-f :
      ( inv-precomp-set-quotient-product-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))
        ( X)
        ( precomp-Set-Quotient
          ( product-equivalence-relation (R (inr star))
          ( all-sim-equivalence-relation n
            ( tail-functional-vec n A)
            ( λ x → R (inl x))))
          ( product-set-quotient-Set
            ( R (inr star))
            ( all-sim-equivalence-relation n
              ( tail-functional-vec n A)
              ( λ x → R (inl x))))
            ( reflecting-map-product-quotient-map (R (inr star))
            ( all-sim-equivalence-relation n
              ( tail-functional-vec n A)
              ( λ x → R (inl x))))
            ( X)
            ( map-inv-equiv-f))) ＝
      map-inv-equiv-f
    is-retraction-inv-precomp-f =
      is-retraction-inv-precomp-set-quotient-product-set-quotient
        ( R (inr star))
        ( all-sim-equivalence-relation n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))
        ( X)
        ( map-inv-equiv-f)

    is-inv-map-inv-equiv-f :
      ( inv-precomp-set-quotient-product-set-quotient
      ( R (inr star))
      ( all-sim-equivalence-relation n
        ( tail-functional-vec n A)
        ( λ x → R (inl x)))
        ( X)
        ( precomp-f)) ＝
        map-inv-equiv-f
    is-inv-map-inv-equiv-f =
      ap
        ( inv-precomp-set-quotient-product-set-quotient
          ( R (inr star))
          ( all-sim-equivalence-relation n (tail-functional-vec n A)
          ( λ x → R (inl x)))
          ( X))
        ( eq-pair-Σ
          ( ap ( _∘ quotient-vector-map _ A R) (inv lemma-f) ∙
            ( ap
              ( map-inv-equiv-f ∘_)
              ( eq-htpy
                ( λ (a0 , a) →
                  ( eq-pair-eq-fiber
                    ( map-equiv-equiv-set-quotient-vector-quotient-map
                      _ _ _ a))))))
          ( eq-is-prop
            ( is-prop-reflects-equivalence-relation
              ( product-equivalence-relation
                ( R (inr star))
                ( all-sim-equivalence-relation n _ _))
              ( X) _))) ∙
        is-retraction-inv-precomp-f

is-set-quotient-vector-set-quotient :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → equivalence-relation l2 (A i)) →
  is-set-quotient
    ( all-sim-equivalence-relation n A R)
    ( set-quotient-vector-Set n A R)
    ( reflecting-map-quotient-vector-map n A R)
pr1 (is-set-quotient-vector-set-quotient n A R X) =
  section-precomp-vector-set-quotient n A R X
pr2 (is-set-quotient-vector-set-quotient n A R X) =
  is-retraction-inv-precomp-vector-set-quotient n A R X
```
