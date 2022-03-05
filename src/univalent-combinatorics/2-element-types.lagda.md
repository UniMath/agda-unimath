# 2-element types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-types where

open import elementary-number-theory.equality-natural-numbers using
  ( Eq-eq-ℕ)

open import foundation.connected-components-universes using
  ( is-contr-total-equiv-component-UU-Level; equiv-eq-component-UU-Level;
    is-equiv-equiv-eq-component-UU-Level)
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
    isretr-map-inv-equiv; issec-map-inv-equiv; equiv-ap; map-inv-is-equiv)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.function-extensionality using (eq-htpy)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; inv; _∙_; ap; tr)
open import foundation.injective-maps using (is-injective-map-equiv)
open import foundation.involutions using (is-involution-aut)
open import foundation.mere-equivalences using
  ( is-set-mere-equiv; mere-equiv; mere-equiv-Prop; symmetric-mere-equiv)
open import foundation.negation using (¬)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( is-prop; UU-Prop; type-Prop; is-prop-type-Prop)
open import foundation.raising-universe-levels using (map-raise)
open import foundation.sets using (is-set; UU-Set)
open import foundation.subuniverses using (is-contr-total-equiv-subuniverse)
open import foundation.type-arithmetic-empty-type using
  ( map-right-unit-law-coprod-is-empty)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)

open import foundation-core.sets using (Id-Prop)

open import univalent-combinatorics.equality-finite-types using
  ( set-UU-Fin-Level; is-set-has-cardinality)
open import univalent-combinatorics.equality-standard-finite-types using
  ( Eq-Fin-eq; is-set-Fin)
open import univalent-combinatorics.finite-types using
  ( UU-Fin-Level; type-UU-Fin-Level; Fin-UU-Fin-Level; UU-Fin; type-UU-Fin;
    Fin-UU-Fin; has-cardinality; has-cardinality-Prop; equiv-UU-Fin-Level)
open import univalent-combinatorics.standard-finite-types using
  ( Fin; zero-Fin; equiv-succ-Fin; one-Fin; raise-Fin; equiv-raise-Fin;
    is-not-contractible-Fin; succ-Fin)
```

## Idea

2-element types are types that are merely equivalent to the standard 2-element type `Fin 2`.

## Definition

### The condition that a type has two elements

```agda
has-two-elements-Prop : {l : Level} → UU l → UU-Prop l
has-two-elements-Prop X = has-cardinality-Prop X 2

has-two-elements : {l : Level} → UU l → UU l
has-two-elements X = type-Prop (has-two-elements-Prop X)

is-prop-has-two-elements : {l : Level} {X : UU l} → is-prop (has-two-elements X)
is-prop-has-two-elements {l} {X} = is-prop-type-Prop (has-two-elements-Prop X)
```

### The type of all 2-element types of universe level `l`

```agda
2-Element-Type : (l : Level) → UU (lsuc l)
2-Element-Type l = UU-Fin-Level l 2

type-2-Element-Type : {l : Level} → 2-Element-Type l → UU l
type-2-Element-Type = pr1

mere-equiv-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) →
  mere-equiv (Fin 2) (type-2-Element-Type X)
mere-equiv-2-Element-Type = pr2
```

## Properties

### Any 2-element type is a set

```agda
is-set-has-two-elements :
  {l : Level} {X : UU l} → has-two-elements X → is-set X
is-set-has-two-elements H = is-set-has-cardinality H

is-set-type-2-Element-Type :
  {l : Level} (X : 2-Element-Type l) → is-set (type-2-Element-Type X)
is-set-type-2-Element-Type X =
  is-set-has-cardinality (mere-equiv-2-Element-Type X)

set-2-Element-Type :
  {l : Level} → 2-Element-Type l → UU-Set l
pr1 (set-2-Element-Type X) = type-2-Element-Type X
pr2 (set-2-Element-Type X) = is-set-type-2-Element-Type X
```

### Characterizing identifications between general 2-element types

```agda
equiv-2-Element-Type :
  {l1 l2 : Level} → 2-Element-Type l1 → 2-Element-Type l2 → UU (l1 ⊔ l2)
equiv-2-Element-Type X Y = equiv-UU-Fin-Level X Y

id-equiv-2-Element-Type :
  {l1 : Level} (X : 2-Element-Type l1) → equiv-2-Element-Type X X
id-equiv-2-Element-Type X = id-equiv

equiv-eq-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → Id X Y → equiv-2-Element-Type X Y
equiv-eq-2-Element-Type X Y = equiv-eq-component-UU-Level

abstract
  is-contr-total-equiv-2-Element-Type :
    {l1 : Level} (X : 2-Element-Type l1) →
    is-contr (Σ (2-Element-Type l1) (equiv-2-Element-Type X))
  is-contr-total-equiv-2-Element-Type X =
    is-contr-total-equiv-component-UU-Level X

abstract
  is-equiv-equiv-eq-2-Element-Type :
    {l1 : Level} (X Y : 2-Element-Type l1) →
    is-equiv (equiv-eq-2-Element-Type X Y)
  is-equiv-equiv-eq-2-Element-Type = is-equiv-equiv-eq-component-UU-Level

eq-equiv-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → equiv-2-Element-Type X Y → Id X Y
eq-equiv-2-Element-Type X Y =
  map-inv-is-equiv (is-equiv-equiv-eq-2-Element-Type X Y)

extensionality-2-Element-Type :
  {l1 : Level} (X Y : 2-Element-Type l1) → Id X Y ≃ equiv-2-Element-Type X Y
pr1 (extensionality-2-Element-Type X Y) = equiv-eq-2-Element-Type X Y
pr2 (extensionality-2-Element-Type X Y) = is-equiv-equiv-eq-2-Element-Type X Y
```

### Characterization the identifications of `Fin 2` with a 2-element type `X`

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
aut-point-Fin-two-ℕ :
  Fin 2 → (Fin 2 ≃ Fin 2)
aut-point-Fin-two-ℕ (inl (inr star)) = id-equiv
aut-point-Fin-two-ℕ (inr star) = equiv-succ-Fin

abstract
  issec-aut-point-Fin-two-ℕ :
    (ev-zero-aut-Fin-two-ℕ ∘ aut-point-Fin-two-ℕ) ~ id
  issec-aut-point-Fin-two-ℕ (inl (inr star)) = refl
  issec-aut-point-Fin-two-ℕ (inr star) = refl

  isretr-aut-point-Fin-two-ℕ' :
    (e : Fin 2 ≃ Fin 2) (x y : Fin 2) →
    Id (map-equiv e zero-Fin) x →
    Id (map-equiv e one-Fin) y → htpy-equiv (aut-point-Fin-two-ℕ x) e
  isretr-aut-point-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inl (inr star)) = inv p
  isretr-aut-point-Fin-two-ℕ' e
    (inl (inr star)) (inl (inr star)) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  isretr-aut-point-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inl (inr star)) = inv p
  isretr-aut-point-Fin-two-ℕ' e
    (inl (inr star)) (inr star) p q (inr star) = inv q
  isretr-aut-point-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inl (inr star)) = inv p
  isretr-aut-point-Fin-two-ℕ' e
    (inr star) (inl (inr star)) p q (inr star) = inv q
  isretr-aut-point-Fin-two-ℕ' e
    (inr star) (inr star) p q (inl (inr star)) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))
  isretr-aut-point-Fin-two-ℕ' e
    (inr star) (inr star) p q (inr star) =
    ex-falso (Eq-Fin-eq (is-injective-map-equiv e (p ∙ inv q)))

  isretr-aut-point-Fin-two-ℕ :
    (aut-point-Fin-two-ℕ ∘ ev-zero-aut-Fin-two-ℕ) ~ id
  isretr-aut-point-Fin-two-ℕ e =
    eq-htpy-equiv
      ( isretr-aut-point-Fin-two-ℕ' e
        ( map-equiv e zero-Fin)
        ( map-equiv e one-Fin)
        ( refl)
        ( refl))

abstract
  is-equiv-ev-zero-aut-Fin-two-ℕ : is-equiv ev-zero-aut-Fin-two-ℕ
  is-equiv-ev-zero-aut-Fin-two-ℕ =
    is-equiv-has-inverse
      aut-point-Fin-two-ℕ
      issec-aut-point-Fin-two-ℕ
      isretr-aut-point-Fin-two-ℕ
```

#### If `X` is a 2-element type, then evaluating an equivalence `Fin 2 ≃ X` at `0` is an equivalence

```agda
module _
  {l1 : Level} (X : 2-Element-Type l1)
  where
  
  abstract
    is-equiv-ev-zero-equiv-Fin-two-ℕ :
      is-equiv (ev-zero-equiv-Fin-two-ℕ {l1} {type-2-Element-Type X})
    is-equiv-ev-zero-equiv-Fin-two-ℕ =
      apply-universal-property-trunc-Prop
        ( mere-equiv-2-Element-Type X)
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
    (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
  pr1 equiv-ev-zero-equiv-Fin-two-ℕ = ev-zero-equiv-Fin-two-ℕ
  pr2 equiv-ev-zero-equiv-Fin-two-ℕ = is-equiv-ev-zero-equiv-Fin-two-ℕ

  equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 ≃ type-2-Element-Type X
  equiv-point-2-Element-Type =
    map-inv-equiv equiv-ev-zero-equiv-Fin-two-ℕ

  map-equiv-point-2-Element-Type :
    type-2-Element-Type X → Fin 2 → type-2-Element-Type X
  map-equiv-point-2-Element-Type x = map-equiv (equiv-point-2-Element-Type x)

  map-inv-equiv-point-2-Element-Type :
    type-2-Element-Type X → type-2-Element-Type X → Fin 2
  map-inv-equiv-point-2-Element-Type x =
    map-inv-equiv (equiv-point-2-Element-Type x)

  issec-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-equiv-point-2-Element-Type x ∘ map-inv-equiv-point-2-Element-Type x) ~
    id
  issec-map-inv-equiv-point-2-Element-Type x =
    issec-map-inv-equiv (equiv-point-2-Element-Type x)

  isretr-map-inv-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    (map-inv-equiv-point-2-Element-Type x ∘ map-equiv-point-2-Element-Type x) ~
    id
  isretr-map-inv-equiv-point-2-Element-Type x =
    isretr-map-inv-equiv (equiv-point-2-Element-Type x)

  compute-map-equiv-point-2-Element-Type :
    (x : type-2-Element-Type X) →
    Id (map-equiv-point-2-Element-Type x zero-Fin) x
  compute-map-equiv-point-2-Element-Type =
    issec-map-inv-equiv equiv-ev-zero-equiv-Fin-two-ℕ

  is-unique-equiv-point-2-Element-Type :
    (e : Fin 2 ≃ type-2-Element-Type X) →
    htpy-equiv (equiv-point-2-Element-Type (map-equiv e zero-Fin)) e
  is-unique-equiv-point-2-Element-Type e =
    htpy-eq-equiv (isretr-map-inv-equiv equiv-ev-zero-equiv-Fin-two-ℕ e)
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
          ( equiv-ev-zero-equiv-Fin-two-ℕ X) ∘e
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
cases-is-involution-aut-Fin-two-ℕ :
  (e : Fin 2 ≃ Fin 2) (x y z : Fin 2) →
  Id (map-equiv e x) y → Id (map-equiv e y) z →
  Id (map-equiv (e ∘e e) x) x
cases-is-involution-aut-Fin-two-ℕ e (inl (inr star)) (inl (inr star)) z p q =
  ap (map-equiv e) p ∙ p
cases-is-involution-aut-Fin-two-ℕ e
  (inl (inr star)) (inr star) (inl (inr star)) p q =
  ap (map-equiv e) p ∙ q
cases-is-involution-aut-Fin-two-ℕ e (inl (inr star)) (inr star) (inr star) p q =
  ex-falso (neq-inr-inl (is-injective-map-equiv e (q ∙ inv p)))
cases-is-involution-aut-Fin-two-ℕ e
  (inr star) (inl (inr star)) (inl (inr star)) p q =
  ex-falso (neq-inr-inl (is-injective-map-equiv e (p ∙ inv q)))
cases-is-involution-aut-Fin-two-ℕ e (inr star) (inl (inr star)) (inr star) p q =
  ap (map-equiv e) p ∙ q
cases-is-involution-aut-Fin-two-ℕ e (inr star) (inr star) z p q =
  ap (map-equiv e) p ∙ p
  
is-involution-aut-Fin-two-ℕ : (e : Fin 2 ≃ Fin 2) → is-involution-aut e
is-involution-aut-Fin-two-ℕ e x =
  cases-is-involution-aut-Fin-two-ℕ e x
    ( map-equiv e x)
    ( map-equiv (e ∘e e) x)
    ( refl)
    ( refl)
```

### Any automorphism on a 2-element set is an involution

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where
  
  is-involution-aut-2-element-type :
    (e : equiv-2-Element-Type X X) → is-involution-aut e
  is-involution-aut-2-element-type e x =
    apply-universal-property-trunc-Prop
      ( mere-equiv-2-Element-Type X)
      ( Id-Prop (set-UU-Fin-Level X) (map-equiv (e ∘e e) x) x)
      ( λ h →
        ( ap (map-equiv (e ∘e e)) (inv (issec-map-inv-equiv h x))) ∙
        ( ( ap (map-equiv e) (inv (issec-map-inv-equiv h _))) ∙
          ( inv (issec-map-inv-equiv h _) ∙
            ( ( ap
                ( map-equiv h)
                ( is-involution-aut-Fin-two-ℕ (inv-equiv h ∘e (e ∘e h)) _)) ∙
              ( issec-map-inv-equiv h x)))))
```

### The elements of an arbitrary 2-element type can be swapped (inv )

#### The successor function on `Fin 2` is an involution

#### The swapping equivalence

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  swap-2-Element-Type : equiv-2-Element-Type X X
  swap-2-Element-Type =
    ( equiv-ev-zero-equiv-Fin-two-ℕ X) ∘e
    ( ( equiv-precomp-equiv equiv-succ-Fin (type-2-Element-Type X)) ∘e
      ( inv-equiv (equiv-ev-zero-equiv-Fin-two-ℕ X)))

  map-swap-2-Element-Type : type-2-Element-Type X → type-2-Element-Type X
  map-swap-2-Element-Type = map-equiv swap-2-Element-Type

  compute-swap-2-Element-Type' :
    (x y : type-2-Element-Type X) → ¬ (Id x y) → (z : Fin 2) →
    Id ( map-inv-equiv-point-2-Element-Type X x y) z →
    Id ( map-swap-2-Element-Type x) y
  compute-swap-2-Element-Type' x y f (inl (inr star)) q =
    ex-falso
      ( f
        ( (inv (compute-map-equiv-point-2-Element-Type X x)) ∙
          ( ( ap (map-equiv-point-2-Element-Type X x) (inv q)) ∙
            ( issec-map-inv-equiv-point-2-Element-Type X x y))))
  compute-swap-2-Element-Type' x y p (inr star) q =
    ( ap (map-equiv-point-2-Element-Type X x) (inv q)) ∙
    ( issec-map-inv-equiv-point-2-Element-Type X x y)

  compute-swap-2-Element-Type :
    (x y : type-2-Element-Type X) → ¬ (Id x y) →
    Id (map-swap-2-Element-Type x) y
  compute-swap-2-Element-Type x y p =
    compute-swap-2-Element-Type' x y p
      ( map-inv-equiv-point-2-Element-Type X x y)
      ( refl)

module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin' :
    ¬ ( Id ( equiv-precomp-equiv (equiv-succ-Fin {2}) (type-2-Element-Type X))
           ( id-equiv))
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin' p' =
    apply-universal-property-trunc-Prop
      ( mere-equiv-2-Element-Type X)
      ( empty-Prop)
      ( λ f →
        neq-inr-inl
          ( is-injective-map-equiv f
            ( htpy-eq-equiv (htpy-eq-equiv p' f) zero-Fin)))

  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin :
    ¬ ( Id (equiv-precomp-equiv (equiv-succ-Fin {2}) (type-2-Element-Type X))
           ( id-equiv))
  is-not-identity-equiv-precomp-equiv-equiv-succ-Fin p' =
    apply-universal-property-trunc-Prop
      ( mere-equiv-2-Element-Type X)
      ( empty-Prop)
      ( λ f →
        neq-inr-inl
          ( is-injective-map-equiv f
            ( htpy-eq-equiv (htpy-eq-equiv p' f) zero-Fin)))
```

### The swapping equivalence is not the identity equivalence

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  is-not-identity-swap-2-Element-Type : ¬ (Id (swap-2-Element-Type X) id-equiv)
  is-not-identity-swap-2-Element-Type p =
    is-not-identity-equiv-precomp-equiv-equiv-succ-Fin X
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
    equiv1 : (Fin 2 ≃ type-2-Element-Type X) ≃ (Fin 2 ≃ type-2-Element-Type X)
    equiv1 = equiv-precomp-equiv (equiv-succ-Fin {2}) (type-2-Element-Type X)
    equiv2 : (Fin 2 ≃ type-2-Element-Type X) ≃ type-2-Element-Type X
    equiv2 = equiv-ev-zero-equiv-Fin-two-ℕ X
```

### The swapping equivalence has no fixpoints

```agda
module _
  {l : Level} (X : 2-Element-Type l)
  where

  has-no-fixpoints-swap-2-Element-Type : (x : type-2-Element-Type X) →
    ¬ (Id (map-equiv (swap-2-Element-Type X) x) x)
  has-no-fixpoints-swap-2-Element-Type x P =
    apply-universal-property-trunc-Prop
      ( mere-equiv-2-Element-Type X)
      ( empty-Prop)
      ( λ h →
        is-not-identity-swap-2-Element-Type X
          (eq-htpy-equiv
            (λ y →
              f
                ( inv-equiv h)
                ( y)
                ( map-inv-equiv h x)
                ( map-inv-equiv h y)
                ( map-inv-equiv h (map-equiv (swap-2-Element-Type X) y))
                ( refl)
                ( refl)
                ( refl))))
    where
    f : (h : type-2-Element-Type X ≃ Fin 2) → (y : type-2-Element-Type X) →
        ( k1 k2 k3 : Fin 2) →
        Id (map-equiv h x) k1 → Id (map-equiv h y) k2 →
        Id (map-equiv h (map-equiv (swap-2-Element-Type X) y)) k3 →
        Id (map-equiv (swap-2-Element-Type X) y) y
    f h y (inl (inr star)) (inl (inr star)) k3 p q r =
      tr
        ( λ z → Id (map-equiv (swap-2-Element-Type X) z) z)
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
              ( map-equiv (h ∘e (swap-2-Element-Type X)))
              ( map-inv-equiv
                ( pair
                  ( ap (map-equiv h))
                  ( is-emb-is-equiv
                    ( pr2 h)
                    ( x)
                    ( map-equiv (swap-2-Element-Type X) y)))
                ( p ∙ inv r)) ∙
              ( ( ap
                  ( map-equiv h)
                  ( is-involution-aut-2-element-type X
                    ( swap-2-Element-Type X) y)) ∙
                ( q))))))
    f h y (inl (inr star)) (inr star) (inr star) p q r =
      ( map-inv-equiv
        (pair
          (ap (map-equiv h))
          (is-emb-is-equiv (pr2 h) (map-equiv (swap-2-Element-Type X) y) y))
        (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inl (inr star)) p q r =
      ( map-inv-equiv
        (pair
          (ap (map-equiv h))
          (is-emb-is-equiv (pr2 h) (map-equiv (swap-2-Element-Type X) y) y))
        (r ∙ inv q))
    f h y (inr star) (inl (inr star)) (inr star) p q r =
      ex-falso
        ( neq-inr-inl
          ( inv p ∙ (ap (map-equiv h) (inv P) ∙
            ( ap
              ( map-equiv (h ∘e (swap-2-Element-Type X)))
              ( map-inv-equiv
                ( pair
                  ( ap (map-equiv h))
                  ( is-emb-is-equiv
                    ( pr2 h)
                    ( x)
                    ( map-equiv (swap-2-Element-Type X) y)))
                ( p ∙ inv r)) ∙
              ( ( ap
                  ( map-equiv h)
                  ( is-involution-aut-2-element-type X
                    ( swap-2-Element-Type X)
                    ( y))) ∙
                ( q))))))
    f h y (inr star) (inr star) k3 p q r =
      tr
        ( λ z → Id (map-equiv (swap-2-Element-Type X) z) z)
        ( map-inv-equiv
          (pair
            (ap (map-equiv h))
            (is-emb-is-equiv (pr2 h) x y))
          (p ∙ inv q))
        ( P)
```
