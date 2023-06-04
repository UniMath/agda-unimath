# Finite covers of the circle

```agda
module synthetic-homotopy-theory.finite-cover-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.iterating-functions
open import foundation.negation
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.powers-of-loops
open import synthetic-homotopy-theory.universal-property-circle

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

We instantiate the proofs for the case of n = 2, which gives us the (twisted)
double cover of the circle (sometimes called the "baby" or "junior" Hopf
fibration).

## Definitions

### Finite degree maps

A "degree-`k` map" is a map from the circle to itself, which maps the basepoint
to the basepoint, and maps the loop to `k` iterations of the loop (where
negative iterations are taken to be going in the inverse direction).

```agda
module _
  { l1 : Level} {X : UU l1} (l : free-loop X)
  ( dup-circle : {k : Level} → dependent-universal-property-circle k l)
  where

  private
    up-circle : {k : Level} → universal-property-circle k l
    up-circle =
      universal-property-dependent-universal-property-circle l dup-circle
    X-Pointed-Type : Pointed-Type l1
    X-Pointed-Type = ( X , base-free-loop l )

  finite-degree-map : ℤ → (X → X)
  finite-degree-map k =
    function-recursion-principle-circle
      ( l)
      ( up-circle)
      ( base-free-loop l , power-int-Ω k X-Pointed-Type (loop-free-loop l))

  double-degree-map : X → X
  double-degree-map = finite-degree-map (int-ℕ 2)
```

### Double cover of the circle

```agda
  bool-descent-data-circle : descent-data-circle lzero
  bool-descent-data-circle = (bool , equiv-neg-bool)

  double-cover-circle :
    family-for-descent-data-circle l bool-descent-data-circle
  double-cover-circle =
    center
      ( unique-family-property-universal-property-circle
        ( l)
        ( up-circle)
        ( bool-descent-data-circle))

  double-cover-circle' : family-with-descent-data-circle l lzero
  double-cover-circle' =
    family-with-descent-data-circle-descent-data l bool-descent-data-circle up-circle
```

### Finite cover of the circle

```agda
  Fin-descent-data-circle : (n : ℕ) → descent-data-circle lzero
  Fin-descent-data-circle n = (Fin n , equiv-succ-Fin n)

  finite-cover-circle :
    (n : ℕ) → family-for-descent-data-circle l (Fin-descent-data-circle n)
  finite-cover-circle n =
    center
      ( unique-family-property-universal-property-circle
        ( l)
        ( up-circle)
        ( Fin-descent-data-circle n))

  finite-cover-circle' :
    (n : ℕ) → family-with-descent-data-circle l lzero
  finite-cover-circle' n =
    family-with-descent-data-circle-descent-data l (Fin-descent-data-circle n) up-circle
```

## Properties

### The double cover of the circle is the finite cover of the circle with two loops

```agda
  eq-type-double-cover-finite-cover-circle :
    equiv-fam (pr1 double-cover-circle) (pr1 (finite-cover-circle 2))
  eq-type-double-cover-finite-cover-circle =
    map-inv-equiv
      ( foo l
        ( double-cover-circle')
        ( finite-cover-circle' 2)
        ( dup-circle))
      ( (inv-equiv equiv-bool-Fin-two-ℕ) ,
        (λ { true → refl ; false → refl }))
```

### Evaluation of the finite degree maps

```agda
  ev-finite-degree-map :
    (k : ℤ) →
    ev-free-loop l X (finite-degree-map k) ＝
    ( base-free-loop l , power-int-Ω k X-Pointed-Type (loop-free-loop l))
  ev-finite-degree-map k =
    compute-recursion-principle-circle
      ( l)
      ( up-circle)
      ( base-free-loop l , power-int-Ω k X-Pointed-Type (loop-free-loop l))
```

### There are no sections of the finite covers with two and more twists

```agda
  no-sections-finite-cover-circle-succ-succ :
    (n : ℕ) →
    ¬ ((t : X) → pr1 (finite-cover-circle (succ-ℕ (succ-ℕ n))) t)
  no-sections-finite-cover-circle-succ-succ n =
    map-inv-equiv
      ( sufficient-condition (succ-ℕ (succ-ℕ n)))
      ( λ x →
        has-no-fixed-points-succ-Fin x (is-not-one-succ-succ-ℕ n))
    where
    sufficient-condition :
      (n : ℕ) →
      ¬ ((t : X) → pr1 (finite-cover-circle n) t) ≃
      ((x : Fin n) → ¬ (succ-Fin n x ＝ x))
    sufficient-condition n = equivalence-reasoning
      ¬ ((t : X) → pr1 (finite-cover-circle n) t)
        ≃ ¬ (fixpoint-descent-data-circle (Fin-descent-data-circle n))
          by
            equiv-neg
              ( equiv-ev-fixpoint-descent-data-circle
                ( l)
                ( finite-cover-circle' n)
                ( dup-circle))
        ≃ ((x : Fin n) → ¬ (succ-Fin n x ＝ x))
          by equiv-ev-pair

  no-sections-double-cover-circle : ¬ ((t : X) → pr1 double-cover-circle t)
  no-sections-double-cover-circle =
    {!no-sections-finite-cover-circle-succ-succ 0!}
```

### Commuting triangle

```agda
  double-equiv-circle : X ≃ (Σ X (pr1 double-cover-circle))
  double-equiv-circle = {!!}

  double-cover-map-base : Σ X (pr1 double-cover-circle)
  pr1 double-cover-map-base = base-free-loop l
  pr2 double-cover-map-base = map-equiv (pr1 (pr2 double-cover-circle)) true

  double-cover-map-loop-Σ : Eq-Σ double-cover-map-base double-cover-map-base
  double-cover-map-loop-Σ =
    ( ( (loop-free-loop l) ∙ (loop-free-loop l)) ,
      ( equational-reasoning
        tr
          ( pr1 double-cover-circle)
          ( (loop-free-loop l) ∙ (loop-free-loop l))
          ( pr2 double-cover-map-base)
          ＝ iterate
              ( 2)
              ( tr (pr1 double-cover-circle) (loop-free-loop l))
              ( pr2 double-cover-map-base)
            by
              tr-power-nat-Ω
                ( 2)
                ( X-Pointed-Type)
                ( pr1 double-cover-circle)
                ( loop-free-loop l)
                ( pr2 double-cover-map-base)
          ＝ map-equiv (pr1 (pr2 double-cover-circle)) (iterate 2 neg-bool true)
            by
              inv
              ( iterate-square-ℕ
                ( 2)
                ( neg-bool)
                ( tr (pr1 double-cover-circle) (loop-free-loop l))
                ( map-equiv (pr1 (pr2 double-cover-circle)))
                ( pr2 (pr2 double-cover-circle))
                ( true))
          ＝ pr2 double-cover-map-base by refl))

  double-cover-map-loop : double-cover-map-base ＝ double-cover-map-base
  double-cover-map-loop = eq-pair-Σ' double-cover-map-loop-Σ

  double-map-circle : X → (Σ X (pr1 double-cover-circle))
  double-map-circle =
    function-recursion-principle-circle l up-circle (double-cover-map-base , double-cover-map-loop)

  finite-cover-map-base : (n : ℕ) → Σ X (pr1 (finite-cover-circle (succ-ℕ n)))
  pr1 (finite-cover-map-base n) = base-free-loop l
  pr2 (finite-cover-map-base n) =
    map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n)))) (zero-Fin n)

  finite-cover-map-loop-Σ :
    (n : ℕ) →
    Eq-Σ (finite-cover-map-base n) (finite-cover-map-base n)
  pr1 (finite-cover-map-loop-Σ n) =
    power-nat-Ω (succ-ℕ n) X-Pointed-Type (loop-free-loop l)
  pr2 (finite-cover-map-loop-Σ n) = equational-reasoning
    tr (pr1 (finite-cover-circle (succ-ℕ n)))
      (pr1 (finite-cover-map-loop-Σ n)) (pr2 (finite-cover-map-base n))
      ＝ iterate
          ( succ-ℕ n)
          ( tr (pr1 (finite-cover-circle (succ-ℕ n))) (loop-free-loop l))
          ( pr2 (finite-cover-map-base n))
        by
          tr-power-nat-Ω
            ( succ-ℕ n)
            ( X-Pointed-Type)
            ( pr1 (finite-cover-circle (succ-ℕ n)))
            ( loop-free-loop l)
            ( pr2 (finite-cover-map-base n))
      ＝ map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n)))) (iterate (succ-ℕ n) (succ-Fin (succ-ℕ n)) (zero-Fin n))
        by inv (iterate-square-ℕ (succ-ℕ n) (succ-Fin (succ-ℕ n)) (tr (pr1 (finite-cover-circle (succ-ℕ n))) (loop-free-loop l)) (map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n))))) (pr2 (pr2 (finite-cover-circle (succ-ℕ n)))) (zero-Fin n))
      ＝ map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n)))) (mod-succ-ℕ n (succ-ℕ n))
        by ap (map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n))))) (inv (aaa n (succ-ℕ n)))
      ＝ map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n)))) (zero-Fin n)
        by ap (map-equiv (pr1 (pr2 (finite-cover-circle (succ-ℕ n))))) (bbb n)
      ＝ pr2 (finite-cover-map-base n)
        by refl
    where
    aaa :
      (k n : ℕ) → (mod-succ-ℕ k n) ＝ (iterate n (succ-Fin (succ-ℕ k)) (zero-Fin k))
    aaa k zero-ℕ = refl
    aaa k (succ-ℕ n) = ap (succ-Fin (succ-ℕ k)) (aaa k n)
    bbb : (k : ℕ) → (mod-succ-ℕ k (succ-ℕ k)) ＝ (zero-Fin k)
    bbb k = eq-mod-succ-cong-ℕ k (succ-ℕ k) 0 (cong-zero-ℕ (succ-ℕ k))

  finite-cover-map-loop :
    (n : ℕ) → (finite-cover-map-base n) ＝ (finite-cover-map-base n)
  finite-cover-map-loop n = eq-pair-Σ' (finite-cover-map-loop-Σ n)

  finite-cover-map-free-loop :
    (n : ℕ) → free-loop (Σ X (pr1 (finite-cover-circle (succ-ℕ n))))
  finite-cover-map-free-loop n =
    ( finite-cover-map-base n , finite-cover-map-loop n)

  finite-cover-map-circle :
    (n : ℕ) → (X → (Σ X (pr1 (finite-cover-circle (succ-ℕ n)))))
  finite-cover-map-circle n =
    function-recursion-principle-circle l up-circle (finite-cover-map-free-loop n)

  ev-comp-double-map-circle :
    ev-free-loop l X (pr1 ∘ double-map-circle) ＝ (base-free-loop l , (loop-free-loop l) ∙ (loop-free-loop l))
  ev-comp-double-map-circle =
    eq-Eq-free-loop (ev-free-loop l X ((λ r → pr1 r) ∘ double-map-circle)) (base-free-loop l , (loop-free-loop l ∙ loop-free-loop l))
      ( ap pr1 cbr ,
        ( equational-reasoning
          ap (pr1 ∘ double-map-circle) (loop-free-loop l) ∙ ap pr1 cbr
            ＝ ap pr1 (ap double-map-circle (loop-free-loop l)) ∙ ap pr1 cbr
              by ap (_∙ ap pr1 cbr) (ap-comp pr1 double-map-circle (loop-free-loop l))
            ＝ ap pr1 (cbr ∙ (double-cover-map-loop ∙ inv cbr)) ∙ ap pr1 cbr
              by ap (λ p → ap pr1 p ∙ ap pr1 cbr) cbl
            ＝ (ap pr1 cbr ∙ (ap pr1 (double-cover-map-loop ∙ inv cbr))) ∙ ap pr1 cbr
              by ap (_∙ ap pr1 cbr) (ap-concat pr1 cbr (double-cover-map-loop ∙ inv cbr))
            ＝ (ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ (ap pr1 (inv cbr)))) ∙ ap pr1 cbr
              by ap (λ p → (ap pr1 cbr ∙ p) ∙ ap pr1 cbr) (ap-concat pr1 double-cover-map-loop (inv cbr))
            ＝ ap pr1 cbr ∙ ((ap pr1 double-cover-map-loop ∙ (ap pr1 (inv cbr))) ∙ ap pr1 cbr)
              by assoc (ap pr1 cbr) (ap pr1 double-cover-map-loop ∙ (ap pr1 (inv cbr))) (ap pr1 cbr)
            ＝ ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ (ap pr1 (inv cbr) ∙ (ap pr1 cbr)))
              by ap (ap pr1 cbr ∙_) (assoc (ap pr1 double-cover-map-loop) (ap pr1 (inv cbr)) (ap pr1 cbr))
            ＝ ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ (ap pr1 (inv cbr ∙ cbr)))
              by ap (λ p → ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ p)) (inv (ap-concat pr1 (inv cbr) cbr))
            ＝ ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ refl)
              by ap (λ p → ap pr1 cbr ∙ (ap pr1 double-cover-map-loop ∙ p)) (ap (ap pr1) (left-inv cbr))
            ＝ ap pr1 cbr ∙ (ap pr1 double-cover-map-loop)
              by ap (ap pr1 cbr ∙_) right-unit
            ＝ ap pr1 cbr ∙ ((loop-free-loop l) ∙ (loop-free-loop l))
              by ap (ap pr1 cbr ∙_) [i]))
    where
    cbr : double-map-circle (base-free-loop l) ＝ double-cover-map-base
    cbr =
      (compute-base-recursion-principle-circle l up-circle (double-cover-map-base , double-cover-map-loop))
    cbl :
      ap double-map-circle (loop-free-loop l) ＝ (cbr ∙ (double-cover-map-loop ∙ inv cbr))
    cbl =
      (compute-loop-recursion-principle-circle l up-circle (double-cover-map-base , double-cover-map-loop))
    [i] : ap pr1 double-cover-map-loop ＝ (loop-free-loop l ∙ loop-free-loop l)
    [i] =
      inv (ap-pair-eq-Σ (Σ X (pr1 double-cover-circle)) id double-cover-map-base double-cover-map-base double-cover-map-loop) ∙ (ap (λ p → pr1 (pair-eq-Σ p)) (ap-id double-cover-map-loop) ∙ ap pr1 (isretr-pair-eq-Σ (pr1 l , pr2 double-cover-map-base) (pr1 l , pr2 double-cover-map-base) double-cover-map-loop-Σ))

  ev-comp-finite-cover-map-circle :
    (n : ℕ) →
    ev-free-loop l X (pr1 ∘ (finite-cover-map-circle n)) ＝ (base-free-loop l , power-nat-Ω (succ-ℕ n) X-Pointed-Type (loop-free-loop l))
  ev-comp-finite-cover-map-circle n =
    eq-Eq-free-loop
      ( ev-free-loop l X (pr1 ∘ finite-cover-map-circle n))
      ( base-free-loop l , power-nat-Ω (succ-ℕ n) X-Pointed-Type (loop-free-loop l))
      ( ap pr1 cbr ,
        ( equational-reasoning
          ap (pr1 ∘ (finite-cover-map-circle n)) (loop-free-loop l) ∙ ap pr1 cbr
            ＝ ap pr1 (ap (finite-cover-map-circle n) (loop-free-loop l)) ∙ ap pr1 cbr
              by ap (_∙ ap pr1 cbr) (ap-comp pr1 (finite-cover-map-circle n) (loop-free-loop l))
            ＝ ap pr1 (cbr ∙ ((finite-cover-map-loop n) ∙ (inv cbr))) ∙ ap pr1 cbr
              by ap (λ p → ap pr1 p ∙ ap pr1 cbr) cbl
            ＝ (ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n ∙ (inv cbr)))) ∙ ap pr1 cbr
              by ap (_∙ ap pr1 cbr) (ap-concat pr1 cbr (finite-cover-map-loop n ∙ (inv cbr)))
            ＝ (ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ (ap pr1 (inv cbr)))) ∙ ap pr1 cbr
              by ap (λ p → (ap pr1 cbr ∙ p) ∙ ap pr1 cbr) (ap-concat pr1 (finite-cover-map-loop n) (inv cbr))
            ＝ ap pr1 cbr ∙ ((ap pr1 (finite-cover-map-loop n) ∙ (ap pr1 (inv cbr))) ∙ ap pr1 cbr)
              by assoc (ap pr1 cbr) (ap pr1 (finite-cover-map-loop n) ∙ (ap pr1 (inv cbr))) (ap pr1 cbr)
            ＝ ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ ((ap pr1 (inv cbr)) ∙ ap pr1 cbr))
              by ap (ap pr1 cbr ∙_) (assoc (ap pr1 (finite-cover-map-loop n)) (ap pr1 (inv cbr)) (ap pr1 cbr))
            ＝ ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ ((ap pr1 (inv cbr ∙ cbr))))
              by ap (λ p → ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ p)) (inv (ap-concat pr1 (inv cbr) cbr))
            ＝ ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ refl)
              by ap (λ p → ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n) ∙ (ap pr1 p))) (left-inv cbr)
            ＝ ap pr1 cbr ∙ (ap pr1 (finite-cover-map-loop n))
              by ap (ap pr1 cbr ∙_) right-unit
            ＝ ap pr1 cbr ∙ power-nat-Ω (succ-ℕ n) X-Pointed-Type (pr2 l)
              by ap (ap pr1 cbr ∙_) [i]))
    where
    cbr : finite-cover-map-circle n (base-free-loop l) ＝ finite-cover-map-base n
    cbr =
      compute-base-recursion-principle-circle l up-circle (finite-cover-map-free-loop n)
    cbl :
      ap (finite-cover-map-circle n) (loop-free-loop l) ＝ (cbr ∙ ((finite-cover-map-loop n) ∙ inv cbr))
    cbl =
      compute-loop-recursion-principle-circle l up-circle (finite-cover-map-free-loop n)
    [i] :
      ap pr1 (finite-cover-map-loop n) ＝ power-nat-Ω (succ-ℕ n) X-Pointed-Type (loop-free-loop l)
    [i] =
      inv (ap-pair-eq-Σ (Σ X (pr1 (finite-cover-circle (succ-ℕ n)))) id (finite-cover-map-base n) (finite-cover-map-base n) (finite-cover-map-loop n)) ∙ (ap (λ p → pr1 (pair-eq-Σ p)) (ap-id (finite-cover-map-loop n)) ∙ ap pr1 (isretr-pair-eq-Σ (finite-cover-map-base n) (finite-cover-map-base n) (finite-cover-map-loop-Σ n)))

  ev-compare-double-maps :
    ev-free-loop l X (pr1 ∘ double-map-circle) ＝ ev-free-loop l X double-degree-map
  ev-compare-double-maps =
    ev-comp-double-map-circle ∙ (inv (compute-recursion-principle-circle l up-circle (base-free-loop l , loop-free-loop l ∙ loop-free-loop l)))

  ev-compare-finite-maps :
    (n : ℕ) →
    ev-free-loop l X (pr1 ∘ finite-cover-map-circle n) ＝ ev-free-loop l X (finite-degree-map (in-pos n))
  ev-compare-finite-maps n =
    ev-comp-finite-cover-map-circle n ∙
    ( ap
      ( λ p → (base-free-loop l , p))
      ( inv
        ( compute-power-int-Ω-int-ℕ
          ( succ-ℕ n)
          ( X-Pointed-Type)
          ( loop-free-loop l))) ∙
      inv (ev-finite-degree-map (in-pos n)))

  triangle-double-map-circle : (pr1 ∘ double-map-circle) ~ double-degree-map
  triangle-double-map-circle =
    htpy-eq
      ( map-inv-equiv
        ( equiv-ap-emb
          ( emb-equiv (eq-universal-property-circle l1 l X up-circle)))
        ( ev-compare-double-maps))

  triangle-finite-cover-map-circle :
    (n : ℕ) →
    (pr1 ∘ finite-cover-map-circle n) ~ finite-degree-map (in-pos n)
  triangle-finite-cover-map-circle n =
    htpy-eq
      ( map-inv-equiv
        (equiv-ap-emb
          ( emb-equiv (eq-universal-property-circle l1 l X up-circle)))
          ( ev-compare-finite-maps n))
```
