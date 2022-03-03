# 2-element types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-types where

open import elementary-number-theory.equality-natural-numbers using
  ( Eq-eq-ℕ)

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-equiv; is-prop-is-contr)
open import foundation.coproduct-types using (coprod; inl; inr; neq-inr-inl; neq-inl-inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.double-negation using (dn-Prop'; intro-dn)
open import foundation.empty-types using (ex-falso; empty-Prop)
open import foundation.equivalences using
  ( _≃_; map-equiv; id-equiv; htpy-equiv; eq-htpy-equiv; is-equiv;
    is-equiv-has-inverse; is-equiv-Prop; is-equiv-left-factor';
    equiv-postcomp-equiv; is-equiv-comp; is-equiv-map-equiv;
    is-equiv-comp-equiv; _∘e_; equiv-precomp-equiv; map-inv-equiv; inv-equiv;
    left-inverse-law-equiv; left-unit-law-equiv; right-inverse-law-equiv;
    is-emb-is-equiv; htpy-eq-equiv; right-unit-law-equiv; equiv-precomp;
    isretr-map-inv-equiv; issec-map-inv-equiv)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.mere-equivalences using
  ( is-set-mere-equiv; mere-equiv; mere-equiv-Prop; symmetric-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.raising-universe-levels using (map-raise)
open import foundation.subuniverses using (is-contr-total-equiv-subuniverse)
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coprod-is-empty)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero)

open import foundation-core.sets using (Id-Prop)

open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin-eq; is-set-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; Fin-UU-Fin-Level; UU-Fin; type-UU-Fin;
    Fin-UU-Fin; has-cardinality)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; equiv-succ-Fin; one-Fin; raise-Fin; equiv-raise-Fin;
    is-not-contractible-Fin; succ-Fin)
```

## Idea

2-element types are types that are merely equivalent to the standard 2-element type `Fin 2`.

## Properties

### Characterization of the identity type of the type of 2-element types

#### Evaluating an equivalence and an automorphism at `0 : Fin 2`

```agda
ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → (Fin 2 ≃ X) → X
ev-zero-equiv-Fin-two-ℕ e = map-equiv e zero-Fin

ev-zero-aut-Fin-two-ℕ : (Fin 2 ≃ Fin 2) → Fin 2
ev-zero-aut-Fin-two-ℕ = ev-zero-equiv-Fin-two-ℕ
```

#### Evaluating an automorphism at `0 : Fin 2` is an equivalence

```agda
inv-ev-zero-aut-Fin-two-ℕ :
  Fin 2 → (Fin 2 ≃ Fin 2)
inv-ev-zero-aut-Fin-two-ℕ (inl (inr star)) = id-equiv
inv-ev-zero-aut-Fin-two-ℕ (inr star) = equiv-succ-Fin

abstract
  issec-inv-ev-zero-aut-Fin-two-ℕ :
    (ev-zero-aut-Fin-two-ℕ ∘ inv-ev-zero-aut-Fin-two-ℕ) ~ id
  issec-inv-ev-zero-aut-Fin-two-ℕ (inl (inr star)) = refl
  issec-inv-ev-zero-aut-Fin-two-ℕ (inr star) = refl

  isretr-inv-ev-zero-aut-Fin-two-ℕ' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    Id (map-equiv e zero-Fin) x →
    Id (map-equiv e one-Fin) y → htpy-equiv (inv-ev-zero-aut-Fin-two-ℕ x) e
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inr star) = inv q
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inr star) = inv q
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inr star) (inr star) p q (inl (inr star)) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  isretr-inv-ev-zero-aut-Fin-two-ℕ' e
    (inr star) (inr star) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))

  isretr-inv-ev-zero-aut-Fin-two-ℕ :
    (inv-ev-zero-aut-Fin-two-ℕ ∘ ev-zero-aut-Fin-two-ℕ) ~ id
  isretr-inv-ev-zero-aut-Fin-two-ℕ e =
    eq-htpy-equiv
      ( isretr-inv-ev-zero-aut-Fin-two-ℕ' e
        ( map-equiv e zero-Fin)
        ( map-equiv e one-Fin)
        ( refl)
        ( refl))

abstract
  is-equiv-ev-zero-aut-Fin-two-ℕ : is-equiv ev-zero-aut-Fin-two-ℕ
  is-equiv-ev-zero-aut-Fin-two-ℕ =
    is-equiv-has-inverse
      inv-ev-zero-aut-Fin-two-ℕ
      issec-inv-ev-zero-aut-Fin-two-ℕ
      isretr-inv-ev-zero-aut-Fin-two-ℕ
```

#### If `X` is a 2-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
abstract
  is-equiv-ev-zero-equiv-Fin-two-ℕ :
    {l1 : Level} {X : UU l1} → mere-equiv (Fin 2) X →
    is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {X})
  is-equiv-ev-zero-equiv-Fin-two-ℕ {l1} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-equiv-Prop (ev-zero-equiv-Fin-two-ℕ))
      ( λ α →
        is-equiv-left-factor'
          ( ev-zero-equiv-Fin-two-ℕ)
          ( map-equiv (equiv-postcomp-equiv α (Fin 2)))
          ( is-equiv-comp
            ( ( ev-zero-equiv-Fin-two-ℕ) ∘
              ( map-equiv (equiv-postcomp-equiv α (Fin 2))))
            ( map-equiv α)
            ( ev-zero-equiv-Fin-two-ℕ)
            ( refl-htpy)
            ( is-equiv-ev-zero-aut-Fin-two-ℕ)
            ( is-equiv-map-equiv α))
          ( is-equiv-comp-equiv α (Fin 2)))

equiv-ev-zero-equiv-Fin-two-ℕ :
  {l1 : Level} {X : UU l1} → mere-equiv (Fin 2) X → (Fin 2 ≃ X) ≃ X
pr1 (equiv-ev-zero-equiv-Fin-two-ℕ e) = ev-zero-equiv-Fin-two-ℕ
pr2 (equiv-ev-zero-equiv-Fin-two-ℕ e) = is-equiv-ev-zero-equiv-Fin-two-ℕ e
```

#### The type of pointed 2-element types of any universe level is contractible

```agda
abstract
  is-contr-total-UU-Fin-Level-two-ℕ :
    {l : Level} → is-contr (Σ (UU-Fin-Level l 2) type-UU-Fin-Level)
  is-contr-total-UU-Fin-Level-two-ℕ {l} =
    is-contr-equiv'
      ( Σ ( UU-Fin-Level l 2)
          ( λ X → raise-Fin l 2 ≃ type-UU-Fin-Level X))
      ( equiv-tot
        ( λ X →
          ( equiv-ev-zero-equiv-Fin-two-ℕ (pr2 X)) ∘e
          ( equiv-precomp-equiv (equiv-raise-Fin l 2) (pr1 X))))
      ( is-contr-total-equiv-subuniverse
        ( mere-equiv-Prop (Fin 2))
        ( Fin-UU-Fin-Level l 2))
```

#### The type of pointed 2-element types of universe level `lzero` is contractible

```agda
abstract
  is-contr-total-UU-Fin-two-ℕ :
    is-contr (Σ (UU-Fin 2) (λ X → type-UU-Fin X))
  is-contr-total-UU-Fin-two-ℕ = is-contr-total-UU-Fin-Level-two-ℕ
```

#### Completing the characterization of the identity type of the type of 2-element types of arbitrary universe level

```agda
point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  Id (Fin-UU-Fin-Level l 2) X → type-UU-Fin-Level X
point-eq-UU-Fin-Level-two-ℕ refl = map-raise zero-Fin

abstract
  is-equiv-point-eq-UU-Fin-Level-two-ℕ :
    {l : Level} (X : UU-Fin-Level l 2) →
    is-equiv (point-eq-UU-Fin-Level-two-ℕ {l} {X})
  is-equiv-point-eq-UU-Fin-Level-two-ℕ {l} =
    fundamental-theorem-id
      ( Fin-UU-Fin-Level l 2)
      ( map-raise zero-Fin)
      ( is-contr-total-UU-Fin-Level-two-ℕ)
      ( λ X → point-eq-UU-Fin-Level-two-ℕ {l} {X})

equiv-point-eq-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  Id (Fin-UU-Fin-Level l 2) X ≃ type-UU-Fin-Level X
pr1 (equiv-point-eq-UU-Fin-Level-two-ℕ {l} {X}) =
  point-eq-UU-Fin-Level-two-ℕ
pr2 (equiv-point-eq-UU-Fin-Level-two-ℕ {l} {X}) =
  is-equiv-point-eq-UU-Fin-Level-two-ℕ X

eq-point-UU-Fin-Level-two-ℕ :
  {l : Level} {X : UU-Fin-Level l 2} →
  type-UU-Fin-Level X → Id (Fin-UU-Fin-Level l 2) X
eq-point-UU-Fin-Level-two-ℕ =
  map-inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ
```

#### Completing the characterization of the identity type of the type of 2-element types of universe level `lzero`

```agda
point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → Id (Fin-UU-Fin 2) X → type-UU-Fin X
point-eq-UU-Fin-two-ℕ refl = zero-Fin

abstract
  is-equiv-point-eq-UU-Fin-two-ℕ :
    (X : UU-Fin 2) → is-equiv (point-eq-UU-Fin-two-ℕ {X})
  is-equiv-point-eq-UU-Fin-two-ℕ =
    fundamental-theorem-id
      ( Fin-UU-Fin 2)
      ( zero-Fin)
      ( is-contr-total-UU-Fin-two-ℕ)
      ( λ X → point-eq-UU-Fin-two-ℕ {X})

equiv-point-eq-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → Id (Fin-UU-Fin 2) X ≃ type-UU-Fin X
pr1 (equiv-point-eq-UU-Fin-two-ℕ {X}) = point-eq-UU-Fin-two-ℕ
pr2 (equiv-point-eq-UU-Fin-two-ℕ {X}) = is-equiv-point-eq-UU-Fin-two-ℕ X

eq-point-UU-Fin-two-ℕ :
  {X : UU-Fin 2} → type-UU-Fin X → Id (Fin-UU-Fin 2) X
eq-point-UU-Fin-two-ℕ {X} =
  map-inv-equiv equiv-point-eq-UU-Fin-two-ℕ
```

### The canonical type family on the type of 2-element types has no section

```agda
abstract
  no-section-type-UU-Fin-Level-two-ℕ :
    {l : Level} → ¬ ((X : UU-Fin-Level l 2) → type-UU-Fin-Level X)
  no-section-type-UU-Fin-Level-two-ℕ {l} f =
    is-not-contractible-Fin 2
      ( Eq-eq-ℕ)
      ( is-contr-equiv
        ( Id (Fin-UU-Fin-Level l 2) (Fin-UU-Fin-Level l 2))
        ( ( inv-equiv equiv-point-eq-UU-Fin-Level-two-ℕ) ∘e
          ( equiv-raise-Fin l 2))
        ( is-prop-is-contr
          ( pair
            ( Fin-UU-Fin-Level l 2)
            ( λ X → eq-point-UU-Fin-Level-two-ℕ (f X)))
          ( Fin-UU-Fin-Level l 2)
          ( Fin-UU-Fin-Level l 2)))

abstract
  no-section-type-UU-Fin-two-ℕ :
    ¬ ((X : UU-Fin 2) → type-UU-Fin X)
  no-section-type-UU-Fin-two-ℕ f =
    no-section-type-UU-Fin-Level-two-ℕ f
```

### There is no decidability procedure that proves that an arbitrary 2-element type is decidable

```agda
abstract
  is-not-decidable-type-UU-Fin-Level-two-ℕ :
    {l : Level} →
    ¬ ((X : UU-Fin-Level l 2) → is-decidable (type-UU-Fin-Level X))
  is-not-decidable-type-UU-Fin-Level-two-ℕ {l} d =
    no-section-type-UU-Fin-Level-two-ℕ
      ( λ X →
        map-right-unit-law-coprod-is-empty
          ( pr1 X)
          ( ¬ (pr1 X))
          ( apply-universal-property-trunc-Prop
            ( pr2 X)
            ( dn-Prop' (pr1 X))
            ( λ e → intro-dn {l} (map-equiv e zero-Fin)))
          ( d X))
```

### Any automorphism on `Fin 2` is an involution

```agda
is-involution-aut-Fin-two-ℕ : (e : Fin 2 ≃ Fin 2) → htpy-equiv (e ∘e e) id-equiv
is-involution-aut-Fin-two-ℕ e x =
  cases-is-involution-aut-Fin-two-ℕ x (map-equiv e x) (map-equiv (e ∘e e) x) refl refl
  where
  cases-is-involution-aut-Fin-two-ℕ : (x y z : Fin 2) (p : Id (map-equiv e x) y)
    (q : Id (map-equiv e y) z) → Id (map-equiv (e ∘e e) x) x
  cases-is-involution-aut-Fin-two-ℕ (inl (inr star)) (inl (inr star)) z p q = ap (map-equiv e) p ∙ p
  cases-is-involution-aut-Fin-two-ℕ (inl (inr star)) (inr star) (inl (inr star)) p q = ap (map-equiv e) p ∙ q
  cases-is-involution-aut-Fin-two-ℕ (inl (inr star)) (inr star) (inr star) p q =
    ex-falso
      ( neq-inr-inl
        ( map-inv-equiv
          ( pair
            ( ap (map-equiv e))
            ( is-emb-is-equiv (pr2 e) (inr star) zero-Fin))
          ( q ∙ inv p)))
  cases-is-involution-aut-Fin-two-ℕ (inr star) (inl (inr star)) (inl (inr star)) p q =
    ex-falso
      ( neq-inr-inl
        ( map-inv-equiv
          ( pair
            ( ap (map-equiv e))
            ( is-emb-is-equiv (pr2 e) (inr star) zero-Fin))
          ( p ∙ inv q)))
  cases-is-involution-aut-Fin-two-ℕ (inr star) (inl (inr star)) (inr star) p q = ap (map-equiv e) p ∙ q
  cases-is-involution-aut-Fin-two-ℕ (inr star) (inr star) z p q = ap (map-equiv e) p ∙ p
```

### Any automorphism on a 2-element set is an involution

```agda
module _
  {l : Level} {X : UU l} (H : has-cardinality X 2)
  where
  
  is-involution-aut-2-element-type : (e : X ≃ X) → htpy-equiv (e ∘e e) id-equiv
  is-involution-aut-2-element-type e x =
    apply-universal-property-trunc-Prop
      ( H)
      ( Id-Prop
        ( pair X (is-set-mere-equiv (symmetric-mere-equiv H) (is-set-Fin 2)))
        ( map-equiv (e ∘e e) x)
        ( x))
      ( λ h →
        ( inv ((ap (λ y → map-equiv y (map-equiv (e ∘e e) x)) (right-inverse-law-equiv h)))) ∙
        ( (inv (ap (λ y → map-equiv (((h ∘e inv-equiv h) ∘e (e ∘e e)) ∘e y) x) (right-inverse-law-equiv h))) ∙
          ( (inv (ap (λ y → map-equiv (((h ∘e inv-equiv h) ∘e (e ∘e (y ∘e e))) ∘e (h ∘e inv-equiv h)) x) (right-inverse-law-equiv h))) ∙
            ( (ap (map-equiv h) (is-involution-aut-Fin-two-ℕ (((inv-equiv h) ∘e e) ∘e h) (map-equiv (inv-equiv h) x))) ∙
              (ap (λ y → map-equiv y x) (right-inverse-law-equiv h))))))
```

### The elements of an arbitrary 2-element type can be swapped (inv )

#### The successor function on `Fin 2` is an involution

#### The swapping equivalence

```agda
module _
  {l : Level} {X : UU l} (H : has-cardinality X 2)
  where

  swap-two-elements : X ≃ X
  swap-two-elements =
    ( equiv-ev-zero-equiv-Fin-two-ℕ H) ∘e
    ( ( equiv-precomp-equiv equiv-succ-Fin X) ∘e
      ( inv-equiv (equiv-ev-zero-equiv-Fin-two-ℕ H)))

  computation-swap-two-elements' : (x y : X) → ¬ (Id x y) → (z : Fin 2) →
    Id (pr1 (pr1 (pr2 (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x))) y) z → Id (map-equiv swap-two-elements x) y
  computation-swap-two-elements' x y p (inl (inr star)) q =
    ex-falso
      (p
      ( (inv (pr2 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x)) ∙
        ( (ap (map-equiv (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x)) (inv q)) ∙
          (pr2 (pr1 (pr2 (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x))) y))))
  computation-swap-two-elements' x y p (inr star) q =
    ( ap (map-equiv (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x)) (inv q)) ∙
    pr2 (pr1 (pr2 (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x))) y

  computation-swap-two-elements : (x y : X) → ¬ (Id x y) →
    Id (map-equiv swap-two-elements x) y
  computation-swap-two-elements x y p =
    computation-swap-two-elements' x y p
      (pr1 (pr1 (pr2 (pr1 (pr1 (is-equiv-ev-zero-equiv-Fin-two-ℕ H)) x))) y) refl

module _
  {l : Level} {X : UU l} (H : has-cardinality X 2)
  where

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin' :
    ¬ (Id (equiv-precomp-equiv (equiv-succ-Fin {2}) X) id-equiv)
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin' p' =
    apply-universal-property-trunc-Prop
      ( H)
      ( empty-Prop)
      ( λ f →
        neq-inr-inl
          ( map-inv-equiv
            ( pair
              ( ap (map-equiv f))
              ( is-emb-is-equiv
                ( pr2 f)
                ( inr star)
                ( zero-Fin)))
            ( htpy-eq-equiv (htpy-eq-equiv p' f) zero-Fin)))

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin :
    ¬ (Id (equiv-precomp-equiv (equiv-succ-Fin {2}) X) id-equiv)
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin p' =
    apply-universal-property-trunc-Prop
      ( H)
      ( empty-Prop)
      ( λ f →
        neq-inr-inl
          ( map-inv-equiv
            ( pair
              ( ap (map-equiv f))
              ( is-emb-is-equiv
                ( pr2 f)
                ( inr star)
                ( zero-Fin)))
            ( htpy-eq-equiv (htpy-eq-equiv p' f) zero-Fin)))
```

### The swapping equivalence is not the identity equivalence

```agda
module _
  {l : Level} {X : UU l} (H : has-cardinality X 2)
  where

  is-not-identity-swap-two-elements : ¬ (Id (swap-two-elements H) id-equiv)
  is-not-identity-swap-two-elements p =
    is-not-identity-equiv-precomp-equiv-equiv-succ-Fin H
      ( ( ( inv (left-unit-law-equiv equiv1)) ∙
          ( ap (λ x → x ∘e equiv1) (inv (left-inverse-law-equiv equiv2)))) ∙
        ( ( inv
            ( right-unit-law-equiv ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1))) ∙
          ( ( ap
              ( λ x → ((inv-equiv equiv2 ∘e equiv2) ∘e equiv1) ∘e x)
              ( inv (left-inverse-law-equiv equiv2))) ∙
          ( ( ( eq-htpy-equiv refl-htpy) ∙
              ( ap (λ x → inv-equiv equiv2 ∘e (x ∘e equiv2)) p)) ∙
            ( ( ap
                ( λ x → inv-equiv equiv2 ∘e x)
                ( left-unit-law-equiv equiv2)) ∙
              ( left-inverse-law-equiv equiv2))))))
    where
    equiv1 : (Fin 2 ≃ X) ≃ (Fin 2 ≃ X)
    equiv1 = equiv-precomp-equiv (equiv-succ-Fin {2}) X
    equiv2 : (Fin 2 ≃ X) ≃ X
    equiv2 = equiv-ev-zero-equiv-Fin-two-ℕ H
```

### The swapping equivalence has no fixpoints

```agda
  has-no-fixpoints-swap-two-elements : (x : X) →
    ¬ (Id (map-equiv (swap-two-elements H) x) x)
  has-no-fixpoints-swap-two-elements x P =
    apply-universal-property-trunc-Prop
      ( H)
      ( empty-Prop)
      ( λ h →
        is-not-identity-swap-two-elements
          (eq-htpy-equiv
            (λ y →
              f
                ( inv-equiv h)
                ( y)
                ( map-inv-equiv h x)
                ( map-inv-equiv h y)
                ( map-inv-equiv h (map-equiv (swap-two-elements H) y))
                ( refl)
                ( refl)
                ( refl))))
    where
    f : (h : X ≃ Fin 2) → (y : X) → (k1 k2 k3 : Fin 2) →
      Id (map-equiv h x) k1 → Id (map-equiv h y) k2 →
      Id (map-equiv h (map-equiv (swap-two-elements H) y)) k3 →
      Id (map-equiv (swap-two-elements H) y) y
    f h y (inl (inr star)) (inl (inr star)) k3 p q r =
      tr
        ( λ z → Id (map-equiv (swap-two-elements H) z) z)
        ( map-inv-equiv
          (pair
            (ap (map-equiv h))
            (is-emb-is-equiv (pr2 h) x y))
          (p ∙ inv q))
        ( P)
    f h y (inl (inr star)) (inr star) (inl (inr star)) p q r =
      ex-falso
        ( neq-inl-inr
          ( inv p ∙ (ap (map-equiv h) (inv P) ∙
            ( ap
              ( map-equiv (h ∘e (swap-two-elements H)))
              ( map-inv-equiv
                ( pair (ap (map-equiv h)) (is-emb-is-equiv (pr2 h) x (map-equiv (swap-two-elements H) y)))
                (p ∙ inv r)) ∙
              (ap (map-equiv h) (is-involution-aut-2-element-type H (swap-two-elements H) y) ∙ q)))))
    f h y (inl (inr star)) (inr star) (inr star) p q r =
      ( map-inv-equiv
        (pair
          (ap (map-equiv h))
          (is-emb-is-equiv (pr2 h) (map-equiv (swap-two-elements H) y) y))
        (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inl (inr star)) p q r =
      ( map-inv-equiv
        (pair
          (ap (map-equiv h))
          (is-emb-is-equiv (pr2 h) (map-equiv (swap-two-elements H) y) y))
        (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inr star) p q r =
      ex-falso
        ( neq-inr-inl
          ( inv p ∙ (ap (map-equiv h) (inv P) ∙
            ( ap
              ( map-equiv (h ∘e (swap-two-elements H)))
              ( map-inv-equiv
                ( pair (ap (map-equiv h)) (is-emb-is-equiv (pr2 h) x (map-equiv (swap-two-elements H) y)))
                (p ∙ inv r)) ∙
              (ap (map-equiv h) (is-involution-aut-2-element-type H (swap-two-elements H) y) ∙ q)))))
    f h y (inr star) (inr star) k3 p q r =
      tr
        ( λ z → Id (map-equiv (swap-two-elements H) z) z)
        ( map-inv-equiv
          (pair
            (ap (map-equiv h))
            (is-emb-is-equiv (pr2 h) x y))
          (p ∙ inv q))
        ( P)
```
