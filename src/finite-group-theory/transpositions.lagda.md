# Transpositions

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module finite-group-theory.transpositions where

open import elementary-number-theory.natural-numbers using (ℕ; succ-ℕ; zero-ℕ)
open import elementary-number-theory.well-ordering-principle-standard-finite-types using (exists-not-not-forall-count)

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-injective-inl; is-prop-coprod; neq-inr-inl; coprod-Prop)
open import foundation.decidable-equality using ( has-decidable-equality; is-set-has-decidable-equality)
open import foundation.decidable-types using
  (is-decidable; is-decidable-coprod; is-decidable-empty; is-prop-is-decidable; is-decidable-raise)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop; prop-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (empty; ex-falso; is-prop-empty)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ; pair-eq-Σ)
open import foundation.equivalences using
  ( _≃_; _∘e_; eq-htpy-equiv; htpy-equiv; id-equiv; inv-equiv; is-emb-is-equiv; is-equiv;
    is-equiv-has-inverse; left-inverse-law-equiv; right-inverse-law-equiv; map-equiv; map-inv-equiv)
open import foundation.equivalences-maybe using
  ( extend-equiv-Maybe; comp-extend-equiv-Maybe; computation-inv-extend-equiv-Maybe)
open import foundation.functions using (_∘_; id; precomp)
open import foundation.function-extensionality using (htpy-eq; eq-htpy)
open import foundation.functoriality-coproduct-types using (id-map-coprod; map-coprod)
open import foundation.homotopies using (_~_; refl-htpy; inv-htpy; comp-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.involutions using (is-involution; is-equiv-is-involution)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.negation using (¬)
open import foundation.propositions using (eq-is-prop; is-prop-is-prop; is-prop-all-elements-equal)
open import foundation.propositional-extensionality using (eq-iff)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop; is-prop-type-trunc-Prop; unit-trunc-Prop; type-trunc-Prop)
open import foundation.raising-universe-levels using (map-raise; map-inv-raise; raise; equiv-raise)
open import foundation.sets using (is-set-type-Set; Id-Prop)
open import foundation.type-arithmetic-empty-type using
  ( inv-right-unit-law-coprod-is-empty; map-right-absorption-prod)
open import foundation.unit-type using (star; unit)
open import foundation.universe-levels using (Level; UU; lzero; _⊔_)


open import univalent-combinatorics.2-element-types using
  ( compute-swap-2-Element-Type; is-involution-aut-2-element-type;
    has-no-fixpoints-swap-2-Element-Type; swap-2-Element-Type;
    is-not-identity-swap-2-Element-Type; map-swap-2-Element-Type)
open import univalent-combinatorics.counting using
  ( count; equiv-count; inv-equiv-count; map-equiv-count; map-inv-equiv-count; number-of-elements-count;
    has-decidable-equality-count; is-set-count)
open import univalent-combinatorics.equality-standard-finite-types using
  ( has-decidable-equality-Fin; Fin-Set)
open import univalent-combinatorics.finite-types using (has-cardinality; has-cardinality-Prop)
open import univalent-combinatorics.lists using
  (cons; list; fold-list; map-list; nil)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

Transpositions are permutations of two elements

## Definitions

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → decidable-Prop l2)
  (H : has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x))))
  where

  map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x))) → X
  map-transposition' x (inl p) =
    pr1 (map-swap-2-Element-Type (pair _ H) (pair x p))
  map-transposition' x (inr np) = x

  map-transposition : X → X
  map-transposition x =
    map-transposition' x (is-decidable-type-decidable-Prop (P x))

  conserves-P-map-transposition : (x : X) → type-decidable-Prop (P x) →
    type-decidable-Prop (P (map-transposition x))
  conserves-P-map-transposition x p =
    tr (λ R → type-decidable-Prop (P (map-transposition' x R)))
      { x = inl p} {y = is-decidable-type-decidable-Prop (P x)}
      ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (P x))))
      ( pr2 (map-swap-2-Element-Type (pair (Σ X (λ y → type-decidable-Prop (P y))) H) (pair x p)))

  is-involution-map-transposition' :
    (x : X) (d : is-decidable (type-decidable-Prop (P x)))
    (d' : is-decidable (type-decidable-Prop (P (map-transposition' x d)))) →
    Id (map-transposition' (map-transposition' x d) d') x
  is-involution-map-transposition' x (inl p) (inl p') =
    ( ap
      ( λ y → map-transposition' (map-transposition' x (inl p)) (inl y))
      ( eq-is-prop
        ( is-prop-type-decidable-Prop (P (map-transposition' x (inl p)))))) ∙
    ( ap pr1 (is-involution-aut-2-element-type (pair _ H) (swap-2-Element-Type (pair _ H)) (pair x p)))
  is-involution-map-transposition' x (inl p) (inr np') =
    ex-falso (np' (pr2 (map-swap-2-Element-Type (pair _ H) (pair x p))))
  is-involution-map-transposition' x (inr np) (inl p') = ex-falso (np p')
  is-involution-map-transposition' x (inr np) (inr np') = refl

  is-involution-map-transposition : is-involution map-transposition
  is-involution-map-transposition x =
    is-involution-map-transposition' x
      ( is-decidable-type-decidable-Prop (P x))
      ( is-decidable-type-decidable-Prop
        ( P (map-transposition' x (is-decidable-type-decidable-Prop (P x)))))

  is-equiv-map-transposition : is-equiv map-transposition
  is-equiv-map-transposition =
    is-equiv-is-involution is-involution-map-transposition

  transposition : X ≃ X
  pr1 transposition = map-transposition
  pr2 transposition = is-equiv-map-transposition

module _
  {l1 l2 : Level} (X : UU l1)
  where

  permutation-list-transpositions :
    ( list
      ( Σ
        ( X → decidable-Prop l2)
        ( λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))) →
    ( X ≃ X)
  permutation-list-transpositions =
    fold-list id-equiv λ (pair P H) e → (transposition X P H) ∘e e
```

## Properties

### `transposition` is not the identity equivalence

```agda
module _
  {l1 l2 : Level} (X : UU l1) (P : X → decidable-Prop l2)
  (H : has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x))))
  where

  is-not-identity-map-transposition : Id (map-transposition X P H) id → empty
  is-not-identity-map-transposition f =
    is-not-identity-swap-2-Element-Type
      ( pair _ H)
      ( eq-htpy-equiv
        ( λ { (pair x p) →
              eq-pair-Σ
                ( ( ap
                    ( map-transposition' X P H x)
                    ( eq-is-prop
                      ( is-prop-is-decidable
                        ( is-prop-type-decidable-Prop (P x)))
                        { y =
                          is-decidable-type-decidable-Prop (P x)})) ∙
                  ( htpy-eq f x))
                ( eq-is-prop (is-prop-type-decidable-Prop (P x)))}))
```

### For any type `X` with decidable equality and `x y : X` such that `x` and `y` are distinct, there exists a transposition that maps `x` to `y`, `y` to `x` and everything else to itself.

```agda
module _
  {l : Level} {X : UU l} (H : has-decidable-equality X)
  where

  transposition-two-elements : (x y : X) → ¬ (Id x y) →
    Σ ( X → decidable-Prop l)
      ( λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x))))
  pr1 (pr1 (transposition-two-elements x y p) z) = coprod (Id x z) (Id y z)
  pr1 (pr2 (pr1 (transposition-two-elements x y p) z)) =
    is-prop-coprod
      ( λ q r → p (q ∙ inv r))
      ( is-set-type-Set (pair X (is-set-has-decidable-equality H)) x z)
      ( is-set-type-Set (pair X (is-set-has-decidable-equality H)) y z)
  pr2 (pr2 (pr1 (transposition-two-elements x y p) z)) = is-decidable-coprod (H x z) (H y z)
  pr2 (transposition-two-elements x y p) =
    unit-trunc-Prop
      ( pair f (is-equiv-has-inverse inv-f retr-f sec-f))
    where
    f : Fin 2 → Σ X (λ z → type-decidable-Prop (pr1 (transposition-two-elements x y p) z))
    pr1 (f (inl (inr star))) = x
    pr2 (f (inl (inr star))) = inl refl
    pr1 (f (inr star)) = y
    pr2 (f (inr star)) = inr refl
    inv-f : Σ X (λ z → type-decidable-Prop (pr1 (transposition-two-elements x y p) z)) → Fin 2
    inv-f (pair z (inl refl)) = inl (inr star)
    inv-f (pair z (inr refl)) = inr star
    retr-f : (f ∘ inv-f) ~ id
    retr-f (pair z (inl refl)) = refl
    retr-f (pair z (inr refl)) = refl
    sec-f : (inv-f ∘ f) ~ id
    sec-f (inl (inr star)) = refl
    sec-f (inr star) = refl

  equiv-transposition-two-elements : (x y : X) → ¬ (Id x y) → (X ≃ X)
  equiv-transposition-two-elements x y p =
    transposition X (pr1 (transposition-two-elements x y p)) (pr2 (transposition-two-elements x y p))

  left-computation-transposition-two-elements : (x y : X) (p : ¬ (Id x y)) →
    Id (map-equiv (equiv-transposition-two-elements x y p) x) y
  left-computation-transposition-two-elements x y p
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) x) 
  ... | inl pp =
    ap
      pr1
      ( compute-swap-2-Element-Type
        ( pair _ (pr2 (transposition-two-elements x y p)))
        ( pair x pp)
        ( pair y (inr refl))
        ( λ q → p (ap pr1 q)))
  ... | inr np = ex-falso (np (inl refl))

  right-computation-transposition-two-elements : (x y : X) (p : ¬ (Id x y)) →
    Id (map-equiv (equiv-transposition-two-elements x y p) y) x
  right-computation-transposition-two-elements x y p
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) y) 
  ... | inl pp =
    ap
      pr1
      ( compute-swap-2-Element-Type
        ( pair _ (pr2 (transposition-two-elements x y p)))
        ( pair y pp)
        ( pair x (inl refl))
        ( λ q → p (ap pr1 (inv q))))
  ... | inr np = ex-falso (np (inr refl))

  not-computation-transposition-two-elements : (x y z : X) (p : ¬ (Id x y)) →
    ¬ (Id x z) → ¬ (Id y z) →
    Id (map-equiv (equiv-transposition-two-elements x y p) z) z
  not-computation-transposition-two-elements x y z p q r 
    with is-decidable-type-decidable-Prop (pr1 (transposition-two-elements x y p) z) 
  ... | inl (inl h) = ex-falso (q h)
  ... | inl (inr h) = ex-falso (r h)
  ... | inr np = refl

module _
  {l : Level} {X : UU l} (eX : count X)
  (t : Σ ( X → decidable-Prop l) ( λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))
  where

  element-is-not-identity-map-transposition :
    Σ X (λ x → ¬ (Id (map-transposition X (pr1 t) (pr2 t) x) x))
  element-is-not-identity-map-transposition =
    exists-not-not-forall-count (λ z → Id (map-transposition X (pr1 t) (pr2 t) z) z)
    ( λ x → has-decidable-equality-count eX (map-transposition X (pr1 t) (pr2 t) x) x) eX
    ( λ H → is-not-identity-map-transposition X (pr1 t) (pr2 t) (eq-htpy H))
  
  two-elements-transposition :
    Σ X (λ x → Σ X (λ y → Σ (¬ (Id x y)) (λ np → Id (transposition-two-elements (has-decidable-equality-count eX) x y np) t)))
  pr1 two-elements-transposition = pr1 element-is-not-identity-map-transposition
  pr1 (pr2 two-elements-transposition) = map-transposition X (pr1 t) (pr2 t) (pr1 element-is-not-identity-map-transposition)
  pr1 (pr2 (pr2 two-elements-transposition)) = λ p → pr2 element-is-not-identity-map-transposition (inv p)
  pr2 (pr2 (pr2 two-elements-transposition)) =
    eq-pair-Σ
      ( eq-htpy
        ( λ x → eq-pair-Σ
          ( ap pr1
            { x = prop-decidable-Prop
              (pr1
                (transposition-two-elements (has-decidable-equality-count eX) (pr1 two-elements-transposition)
                  (pr1 (pr2 two-elements-transposition)) (pr1 (pr2 (pr2 two-elements-transposition)))) x)}
            { y = prop-decidable-Prop (pr1 t x)}
            ( eq-iff
              (type-t-coprod-id x)
              (coprod-id-type-t x)))
          ( eq-pair-Σ
            ( eq-is-prop (is-prop-is-prop (pr1 (pr1 t x))))
            ( eq-is-prop (is-prop-is-decidable (pr1 (pr2 (pr1 t x))))))))
      ( eq-is-prop (pr2 (has-cardinality-Prop 2 (Σ X (λ x → type-decidable-Prop (pr1 t x))))))
    where
    type-decidable-prop-pr1-two-elements-transposition :
      type-decidable-Prop (pr1 t (pr1 two-elements-transposition))
    type-decidable-prop-pr1-two-elements-transposition =
      cases-type-decidable-prop-pr1-two-elements-transposition
        (is-decidable-type-decidable-Prop (pr1 t (pr1 two-elements-transposition)))
      where
      cases-type-decidable-prop-pr1-two-elements-transposition :
        is-decidable (type-decidable-Prop (pr1 t (pr1 two-elements-transposition))) →
        type-decidable-Prop (pr1 t (pr1 two-elements-transposition))
      cases-type-decidable-prop-pr1-two-elements-transposition (inl Q) = Q
      cases-type-decidable-prop-pr1-two-elements-transposition (inr NQ) =
        ex-falso (pr2 element-is-not-identity-map-transposition
          ( ap (λ R → map-transposition' X (pr1 t) (pr2 t) (pr1 (two-elements-transposition)) R)
            { x = is-decidable-type-decidable-Prop (pr1 t (pr1 two-elements-transposition))} {y = inr NQ}
            ( eq-is-prop (is-prop-is-decidable (is-prop-type-decidable-Prop (pr1 t (pr1 two-elements-transposition)))))))
    type-decidable-prop-pr1-pr2-two-elements-transposition :
      type-decidable-Prop (pr1 t (pr1 (pr2 two-elements-transposition)))
    type-decidable-prop-pr1-pr2-two-elements-transposition = 
      conserves-P-map-transposition X (pr1 t) (pr2 t) (pr1 two-elements-transposition)
        ( type-decidable-prop-pr1-two-elements-transposition)
    type-t-coprod-id : (x : X) →
      coprod (Id (pr1 two-elements-transposition) x) (Id (pr1 (pr2 two-elements-transposition)) x) → type-decidable-Prop (pr1 t x)
    type-t-coprod-id x (inl Q) =
      tr (λ y → type-decidable-Prop (pr1 t y)) Q
        ( type-decidable-prop-pr1-two-elements-transposition)
    type-t-coprod-id x (inr Q) =
      tr (λ y → type-decidable-Prop (pr1 t y)) Q type-decidable-prop-pr1-pr2-two-elements-transposition
    cases-coprod-id-type-t : (x : X) → ( p : type-decidable-Prop (pr1 t x)) →
      (h : Fin 2 ≃ Σ X (λ y → type-decidable-Prop (pr1 t y))) → ( k1 k2 k3 : Fin 2 ) →
      Id (map-inv-equiv h (pair x p)) k1 →
      Id (map-inv-equiv h (pair (pr1 two-elements-transposition) type-decidable-prop-pr1-two-elements-transposition)) k2 →
      Id (map-inv-equiv h (pair (pr1 (pr2 two-elements-transposition)) type-decidable-prop-pr1-pr2-two-elements-transposition)) k3 →
      coprod (Id (pr1 two-elements-transposition) x) (Id (pr1 (pr2 two-elements-transposition)) x)
    cases-coprod-id-type-t x p h (inl (inr star)) (inl (inr star)) k3 K1 K2 K3 =
      inl (ap pr1 (is-injective-map-equiv (inv-equiv h) (K2 ∙ inv K1)))
    cases-coprod-id-type-t x p h (inl (inr star)) (inr star) (inl (inr star)) K1 K2 K3 =
      inr (ap pr1 (is-injective-map-equiv (inv-equiv h) (K3 ∙ inv K1)))
    cases-coprod-id-type-t x p h (inl (inr star)) (inr star) (inr star) K1 K2 K3 =
      ex-falso (pr1 (pr2 (pr2 two-elements-transposition)) (ap pr1 (is-injective-map-equiv (inv-equiv h)
        (K2 ∙ inv K3))))
    cases-coprod-id-type-t x p h (inr star) (inl (inr star)) (inl (inr star)) K1 K2 K3 =
      ex-falso (pr1 (pr2 (pr2 two-elements-transposition)) (ap pr1 (is-injective-map-equiv (inv-equiv h)
        (K2 ∙ inv K3))))
    cases-coprod-id-type-t x p h (inr star) (inl (inr star)) (inr star) K1 K2 K3 =
      inr (ap pr1 (is-injective-map-equiv (inv-equiv h) (K3 ∙ inv K1)))
    cases-coprod-id-type-t x p h (inr star) (inr star) k3 K1 K2 K3 =
      inl (ap pr1 (is-injective-map-equiv (inv-equiv h) (K2 ∙ inv K1)))
    coprod-id-type-t : (x : X) → type-decidable-Prop (pr1 t x) →
      coprod (Id (pr1 two-elements-transposition) x) (Id (pr1 (pr2 two-elements-transposition)) x)
    coprod-id-type-t x p =
      apply-universal-property-trunc-Prop (pr2 t)
        ( coprod-Prop
          ( Id-Prop (pair X (is-set-count eX)) (pr1 two-elements-transposition) x)
          ( Id-Prop (pair X (is-set-count eX)) (pr1 (pr2 two-elements-transposition)) x)
          ( λ q r → pr1 (pr2 (pr2 two-elements-transposition)) (q ∙ inv r)))
        ( λ h → cases-coprod-id-type-t x p h (map-inv-equiv h (pair x p))
          (map-inv-equiv h (pair (pr1 two-elements-transposition) type-decidable-prop-pr1-two-elements-transposition))
          (map-inv-equiv h (pair (pr1 (pr2 two-elements-transposition)) type-decidable-prop-pr1-pr2-two-elements-transposition))
          refl refl refl)
```

### Transpositions can be transported along equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} (X : UU l1) (Y : UU l2) (e : X ≃ Y)
  where

  transposition-conjugation-equiv :
    ( Σ
      ( X → decidable-Prop l3)
      ( λ P →
        has-cardinality
          ( 2)
          ( Σ X (λ x → type-decidable-Prop (P x))))) → 
      ( Σ
        ( Y → decidable-Prop (l3 ⊔ l4))
        ( λ P →
          has-cardinality 2
            ( Σ Y (λ x → type-decidable-Prop (P x)))))
  pr1 (pr1 (transposition-conjugation-equiv (pair P H)) x) = raise l4 (type-decidable-Prop (P (map-inv-equiv e x)))
  pr1 (pr2 (pr1 (transposition-conjugation-equiv (pair P H)) x)) =
    is-prop-all-elements-equal
      (λ p1 p2 →
        is-injective-map-equiv
          ( inv-equiv (equiv-raise l4 (type-decidable-Prop (P (map-inv-equiv e x)))))
          ( eq-is-prop (is-prop-type-decidable-Prop (P (map-inv-equiv e x)))))
  pr2 (pr2 (pr1 (transposition-conjugation-equiv (pair P H)) x)) =
    is-decidable-raise l4 (type-decidable-Prop (P (map-inv-equiv e x))) (is-decidable-type-decidable-Prop (P (map-inv-equiv e x)))
  pr2 (transposition-conjugation-equiv (pair P H)) =
    apply-universal-property-trunc-Prop
      ( H)
      ( has-cardinality-Prop 2 (Σ Y (λ x → raise l4 (type-decidable-Prop (P (map-inv-equiv e x))))))
       λ h →
        unit-trunc-Prop
          ( pair
            ( λ x →
              pair
                ( map-equiv e (pr1 (map-equiv h x)))
                ( tr
                  ( λ g → raise l4 (type-decidable-Prop (P (map-equiv g (pr1 (map-equiv h x))))))
                  ( inv (left-inverse-law-equiv e))
                  ( map-raise (pr2 (map-equiv h x)))))
            ( is-equiv-has-inverse
              ( λ (pair x p) → map-inv-equiv h ( pair (map-inv-equiv e x) (map-inv-raise p)))
              ( λ (pair x p) →
                eq-pair-Σ
                  ( (ap (λ g → map-equiv e (pr1 (map-equiv g (pair (map-inv-equiv e x) (map-inv-raise p)))))
                    (right-inverse-law-equiv h)) ∙
                    ( ap (λ g → map-equiv g x) (right-inverse-law-equiv e)))
                  ( eq-is-prop (pr1 (pr2 (pr1 (transposition-conjugation-equiv (pair P H)) x)))))
              ( λ b →
                ( ap
                  ( λ w → map-inv-equiv h (pair (map-equiv (pr1 w) (pr1 (map-equiv h b))) (pr2 w)))
                  {y = pair id-equiv (pr2 (map-equiv h b))}
                  ( eq-pair-Σ
                    ( left-inverse-law-equiv e)
                    (eq-is-prop (is-prop-type-decidable-Prop (P (pr1 (map-equiv h b)))))) ∙
                  ( ap (λ g → map-equiv g b) (left-inverse-law-equiv h))))))

  correct-transposition-conjugation-equiv : 
    (t : Σ
      ( X → decidable-Prop l3)
      ( λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x))))) → 
    htpy-equiv
      ( transposition
        ( Y)
        ( pr1 (transposition-conjugation-equiv t))
        ( pr2 (transposition-conjugation-equiv t)))
      ( (e ∘e (transposition X (pr1 t) (pr2 t))) ∘e (inv-equiv e)) 
  correct-transposition-conjugation-equiv t x =
    cases-correct-transposition-conjugation-equiv (is-decidable-type-decidable-Prop (pr1 t (map-inv-equiv e x)))
    where
    cases-correct-transposition-conjugation-equiv :
      (Q : is-decidable (type-decidable-Prop (pr1 t (map-inv-equiv e x)))) →
      Id
        ( map-transposition'
          ( Y)
          ( pr1 (transposition-conjugation-equiv t))
          ( pr2 (transposition-conjugation-equiv t))
          ( x)
          ( is-decidable-raise l4 (type-decidable-Prop (pr1 t (map-inv-equiv e x))) Q))
        ( map-equiv e
          ( map-transposition' X (pr1 t) (pr2 t) (map-inv-equiv e x) Q))
    cases-correct-transposition-conjugation-equiv (inl p) =
      ap
        ( pr1)
        ( compute-swap-2-Element-Type
          ( pair
            ( Σ Y (λ y → pr1 (pr1 (transposition-conjugation-equiv t) y)))
            ( pr2 (transposition-conjugation-equiv t)))
          ( pair x (map-raise p))
          ( pair
            ( map-equiv e (pr1 second-pair-X))
            ( map-raise
              ( tr
                ( λ g → type-decidable-Prop (pr1 t (map-equiv g (pr1 second-pair-X))))
                ( inv (left-inverse-law-equiv e))
                ( pr2 second-pair-X))))
           λ q →
            has-no-fixpoints-swap-2-Element-Type
              ( pair (Σ X (λ y → type-decidable-Prop (pr1 t y))) (pr2 t))
              ( pair (map-inv-equiv e x) p)
              ( eq-pair-Σ
                ( is-injective-map-equiv e (inv (pr1 (pair-eq-Σ q)) ∙ ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv e))))
                ( eq-is-prop (is-prop-type-decidable-Prop (pr1 t (map-inv-equiv e x))))))
      where
      second-pair-X : Σ X (λ y → type-decidable-Prop (pr1 t y))
      second-pair-X =
        map-swap-2-Element-Type
          (pair (Σ X (λ y → type-decidable-Prop (pr1 t y))) (pr2 t))
          (pair (map-inv-equiv e x) p)
    cases-correct-transposition-conjugation-equiv (inr np) = ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv e))
          
  correct-transposition-conjugation-equiv-list :
    (li : list
      ( Σ
        ( X → decidable-Prop l3)
        ( λ P →
          has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))))) →
    htpy-equiv
      ( permutation-list-transpositions Y (map-list transposition-conjugation-equiv li))
      ( (e ∘e (permutation-list-transpositions X li)) ∘e (inv-equiv e))
  correct-transposition-conjugation-equiv-list nil x = ap (λ g → map-equiv g x) (inv (right-inverse-law-equiv e))
  correct-transposition-conjugation-equiv-list (cons t li) x =
    ( correct-transposition-conjugation-equiv
      ( t)
      (map-equiv (permutation-list-transpositions Y (map-list transposition-conjugation-equiv li)) x)) ∙
      ( ( ap
        ( map-equiv ((e ∘e transposition X (pr1 t) (pr2 t)) ∘e inv-equiv e))
        ( correct-transposition-conjugation-equiv-list li x)) ∙
        ( ap
          ( λ g →
            map-equiv
              ((((e ∘e transposition X (pr1 t) (pr2 t)) ∘e g) ∘e permutation-list-transpositions X li) ∘e inv-equiv e)
              ( x))
          ( left-inverse-law-equiv e)))
```

### For all `n : ℕ`, for each transposition of `Fin n`, there exists a matching transposition in `Fin (succ-ℕ n)`.

```agda
Fin-succ-Fin-transposition : (n : ℕ) → 
  ( Σ
    ( Fin n → decidable-Prop lzero)
    ( λ P → has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x))))) → 
    ( Σ
      ( Fin (succ-ℕ n) → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2
          ( Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (P x)))))
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inl x) = P x
pr1 (Fin-succ-Fin-transposition n (pair P H)) (inr x) =
  pair empty (pair is-prop-empty is-decidable-empty)
pr2 (Fin-succ-Fin-transposition n (pair P H)) =
  apply-universal-property-trunc-Prop
    ( H)
    ( has-cardinality-Prop 2 (Σ (Fin (succ-ℕ n)) (λ x → type-decidable-Prop (pr1 (Fin-succ-Fin-transposition n (pair P H)) x))))
    ( λ h →
      unit-trunc-Prop
        ( (pair f (is-equiv-has-inverse inv-f retr-f sec-f)) ∘e
          ( inv-right-unit-law-coprod-is-empty
            ( Σ (Fin n)
              ( λ x → type-decidable-Prop (P x)))
            ( Σ unit (λ x → empty)) map-right-absorption-prod ∘e h)))
  where
  f : coprod (Σ (Fin n) (λ x → type-decidable-Prop (P x)))
    (Σ unit (λ x → empty)) →
    Σ (Fin (succ-ℕ n))
    (λ x →
       type-decidable-Prop
       (pr1 (Fin-succ-Fin-transposition n (pair P H)) x))
  f (inl (pair x p)) = pair (inl x) p
  inv-f : Σ (Fin (succ-ℕ n))
    (λ x →
       type-decidable-Prop
       (pr1 (Fin-succ-Fin-transposition n (pair P H)) x)) →
    coprod (Σ (Fin n) (λ x → type-decidable-Prop (P x)))
      (Σ unit (λ x → empty)) 
  inv-f (pair (inl x) p) = inl (pair x p)
  retr-f : (f ∘ inv-f) ~ id
  retr-f (pair (inl x) p) = refl
  sec-f : (inv-f ∘ f) ~ id
  sec-f (inl (pair x p)) = refl

correct-Fin-succ-Fin-transposition : (n : ℕ) → 
  (t : Σ
    ( Fin n → decidable-Prop lzero)
    ( λ P → has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x))))) → 
  htpy-equiv
    ( transposition
      ( Fin (succ-ℕ n))
      ( pr1 (Fin-succ-Fin-transposition n t))
      ( pr2 (Fin-succ-Fin-transposition n t)))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( transposition (Fin n) (pr1 t) (pr2 t)))) 
correct-Fin-succ-Fin-transposition n t (inl x) with is-decidable-type-decidable-Prop (pr1 t x)
correct-Fin-succ-Fin-transposition n t (inl x) | inl p =
    ap
      ( pr1)
      ( compute-swap-2-Element-Type
        ( pair
          (Σ (Fin (succ-ℕ n))
            (λ y → type-decidable-Prop (pr1 (Fin-succ-Fin-transposition n t) y)))
          (pr2 (Fin-succ-Fin-transposition n t)))
        ( pair (inl x) p)
        ( pair
          ( inl (pr1 (map-swap-2-Element-Type (pair (Σ (Fin n) (λ y → type-decidable-Prop (pr1 t y))) (pr2 t)) (pair x p))))
          ( pr2 (map-swap-2-Element-Type (pair (Σ (Fin n) (λ y → type-decidable-Prop (pr1 t y))) (pr2 t)) (pair x p))))
        ( λ eq →
          has-no-fixpoints-swap-2-Element-Type
            ( pair (Σ (Fin n) (λ y → type-decidable-Prop (pr1 t y))) (pr2 t))
            ( pair x p)
            ( eq-pair-Σ
              ( is-injective-inl (inv (pr1 (pair-eq-Σ eq))))
              ( eq-is-prop (is-prop-type-decidable-Prop (pr1 t x))))))
correct-Fin-succ-Fin-transposition n t (inl x) | inr np = refl
correct-Fin-succ-Fin-transposition n t (inr star) = refl

correct-Fin-succ-Fin-transposition-list : (n : ℕ) →
  (l : list
    ( Σ
      ( Fin n → decidable-Prop lzero)
      ( λ P →
        has-cardinality 2 (Σ (Fin n) (λ x → type-decidable-Prop (P x)))))) →
  htpy-equiv
    ( permutation-list-transpositions (Fin (succ-ℕ n)) (map-list (Fin-succ-Fin-transposition n) l))
    ( pr1
      ( map-equiv
        ( extend-equiv-Maybe (Fin-Set n))
        ( permutation-list-transpositions (Fin n) l))) 
correct-Fin-succ-Fin-transposition-list n nil = inv-htpy (id-map-coprod (Fin n) unit)
correct-Fin-succ-Fin-transposition-list n (cons t l) x =
  correct-Fin-succ-Fin-transposition
    ( n)
    ( t)
    ( map-equiv (permutation-list-transpositions (Fin (succ-ℕ n)) (map-list (Fin-succ-Fin-transposition n) l)) x) ∙
      ( (ap
        ( map-equiv (pr1 (map-equiv (extend-equiv-Maybe (Fin-Set n)) (transposition (Fin n) (pr1 t) (pr2 t)))))
        ( correct-Fin-succ-Fin-transposition-list n l x)) ∙
        ( inv
          ( comp-extend-equiv-Maybe
            ( Fin-Set n)
            ( transposition (Fin n) (pr1 t) (pr2 t))
            ( permutation-list-transpositions (Fin n) l)
            ( x))))
```
