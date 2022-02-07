# Type arithmetic for dependent pair types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.type-arithmetic-dependent-pair-types where

open import foundation-core.contractible-maps using
  ( is-equiv-is-contr-map; is-contr-map-is-equiv)
open import foundation-core.contractible-types using
  ( is-contr; is-contr-equiv; center; is-contr-equiv')
open import foundation-core.dependent-pair-types using
  ( Σ; pair; pr1; pr2; ind-Σ; triple; triple')
open import foundation-core.equivalences using
  ( is-equiv; _≃_; is-equiv-has-inverse;
    is-equiv-right-factor; is-equiv-id; is-equiv-left-factor)
open import foundation-core.fibers-of-maps using (equiv-fib-pr1; fib)
open import foundation-core.functions using (_∘_; id)
open import foundation-core.homotopies using (_~_)
open import foundation-core.identity-types using (Id; refl; ap)
open import foundation-core.singleton-induction using
  ( ind-singleton-is-contr; comp-singleton-is-contr)
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

We prove laws for the manipulation dependent pair types with respect to itself. The arithmetical laws involving cartesian product types, coproduct types, the unit type, and the empty type are proven in

```md
type-arithmetic-cartesian-products
type-arithmetic-coproducts
type-arithmetic-unit-type
type-arithmetic-empty-type
```

However, we do prove arithmetical laws with respect to contractible types.

## Properties

### The left unit law for Σ using a contractible base type

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A)
  where

  map-inv-left-unit-law-Σ-is-contr : B a → Σ A B
  pr1 (map-inv-left-unit-law-Σ-is-contr b) = a
  pr2 (map-inv-left-unit-law-Σ-is-contr b) = b

  map-left-unit-law-Σ-is-contr : Σ A B → B a
  map-left-unit-law-Σ-is-contr =
    ind-Σ
      ( ind-singleton-is-contr a C
        ( λ x → B x → B a)
        ( id))

  issec-map-inv-left-unit-law-Σ-is-contr :
    ( map-left-unit-law-Σ-is-contr ∘ map-inv-left-unit-law-Σ-is-contr) ~ id
  issec-map-inv-left-unit-law-Σ-is-contr b =
    ap ( λ (f : B a → B a) → f b)
       ( comp-singleton-is-contr a C (λ x → B x → B a) id)
  
  isretr-map-inv-left-unit-law-Σ-is-contr :
    ( map-inv-left-unit-law-Σ-is-contr ∘ map-left-unit-law-Σ-is-contr) ~ id
  isretr-map-inv-left-unit-law-Σ-is-contr = 
    ind-Σ
      ( ind-singleton-is-contr a C
        ( λ x →
          ( y : B x) →
            Id ( ( map-inv-left-unit-law-Σ-is-contr ∘
                   map-left-unit-law-Σ-is-contr)
                 ( pair x y))
               ( pair x y))
        ( λ y → ap
          ( map-inv-left-unit-law-Σ-is-contr)
          ( ap ( λ f → f y)
               ( comp-singleton-is-contr a C (λ x → B x → B a) id))))

  abstract
    is-equiv-map-left-unit-law-Σ-is-contr :
      is-equiv map-left-unit-law-Σ-is-contr
    is-equiv-map-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr

  left-unit-law-Σ-is-contr : Σ A B ≃ B a
  pr1 left-unit-law-Σ-is-contr = map-left-unit-law-Σ-is-contr
  pr2 left-unit-law-Σ-is-contr = is-equiv-map-left-unit-law-Σ-is-contr

  abstract
    is-equiv-map-inv-left-unit-law-Σ-is-contr :
      is-equiv map-inv-left-unit-law-Σ-is-contr
    is-equiv-map-inv-left-unit-law-Σ-is-contr =
      is-equiv-has-inverse
        map-left-unit-law-Σ-is-contr
        isretr-map-inv-left-unit-law-Σ-is-contr
        issec-map-inv-left-unit-law-Σ-is-contr
  
  inv-left-unit-law-Σ-is-contr : B a ≃ Σ A B
  pr1 inv-left-unit-law-Σ-is-contr = map-inv-left-unit-law-Σ-is-contr
  pr2 inv-left-unit-law-Σ-is-contr = is-equiv-map-inv-left-unit-law-Σ-is-contr
```

### Right unit law for dependent pair types

```
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  abstract
    is-equiv-pr1-is-contr : ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
    is-equiv-pr1-is-contr is-contr-B =
      is-equiv-is-contr-map
        ( λ x → is-contr-equiv
          ( B x)
          ( equiv-fib-pr1 B x)
          ( is-contr-B x))

  equiv-pr1 : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  pr1 (equiv-pr1 is-contr-B) = pr1
  pr2 (equiv-pr1 is-contr-B) = is-equiv-pr1-is-contr is-contr-B

  right-unit-law-Σ-is-contr : ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
  right-unit-law-Σ-is-contr = equiv-pr1

  abstract
    is-contr-is-equiv-pr1 : is-equiv (pr1 {B = B}) → ((a : A) → is-contr (B a))
    is-contr-is-equiv-pr1 is-equiv-pr1-B a =
      is-contr-equiv'
        ( fib pr1 a)
        ( equiv-fib-pr1 B a)
        ( is-contr-map-is-equiv is-equiv-pr1-B a)
```

### Associativity of dependent pair types

There are two ways to express associativity for dependent pair types. We formalize both ways.

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : Σ A B → UU l3)
  where

  map-assoc-Σ : Σ (Σ A B) C → Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
  map-assoc-Σ (pair (pair x y) z) = triple x y z

  map-inv-assoc-Σ : Σ A (λ x → Σ (B x) (λ y → C (pair x y))) → Σ (Σ A B) C
  map-inv-assoc-Σ (pair x (pair y z)) = triple' x y z
  -- map-inv-assoc-Σ t = triple' (pr1 t) (pr1 (pr2 t)) (pr2 (pr2 t))

  isretr-map-inv-assoc-Σ : (map-inv-assoc-Σ ∘ map-assoc-Σ) ~ id
  isretr-map-inv-assoc-Σ (pair (pair x y) z) = refl
  
  issec-map-inv-assoc-Σ : (map-assoc-Σ ∘ map-inv-assoc-Σ) ~ id
  issec-map-inv-assoc-Σ (pair x (pair y z)) = refl

  abstract
    is-equiv-map-assoc-Σ : is-equiv map-assoc-Σ
    is-equiv-map-assoc-Σ =
      is-equiv-has-inverse
        map-inv-assoc-Σ
        issec-map-inv-assoc-Σ
        isretr-map-inv-assoc-Σ

  assoc-Σ : Σ (Σ A B) C ≃ Σ A (λ x → Σ (B x) (λ y → C (pair x y)))
  pr1 assoc-Σ = map-assoc-Σ
  pr2 assoc-Σ = is-equiv-map-assoc-Σ

  inv-assoc-Σ : Σ A (λ x → Σ (B x) (λ y → C (pair x y))) ≃ Σ (Σ A B) C
  pr1 inv-assoc-Σ = map-inv-assoc-Σ
  pr2 inv-assoc-Σ =
    is-equiv-has-inverse
      map-assoc-Σ
      isretr-map-inv-assoc-Σ
      issec-map-inv-assoc-Σ
```

### Associativity, second formulation

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : (x : A) → B x → UU l3)
  where
  
  map-assoc-Σ' : Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) → Σ A (λ x → Σ (B x) (C x))
  map-assoc-Σ' (pair (pair x y) z) = triple x y z

  map-inv-assoc-Σ' :
    Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  map-inv-assoc-Σ' (pair x (pair y z)) = triple' x y z

  issec-map-inv-assoc-Σ' : (map-assoc-Σ' ∘ map-inv-assoc-Σ') ~ id
  issec-map-inv-assoc-Σ' (pair x (pair y z)) = refl

  isretr-map-inv-assoc-Σ' : ( map-inv-assoc-Σ' ∘ map-assoc-Σ') ~ id
  isretr-map-inv-assoc-Σ' (pair (pair x y) z) = refl

  is-equiv-map-assoc-Σ' : is-equiv map-assoc-Σ'
  is-equiv-map-assoc-Σ' =
    is-equiv-has-inverse
      map-inv-assoc-Σ'
      issec-map-inv-assoc-Σ'
      isretr-map-inv-assoc-Σ'

  assoc-Σ' : Σ (Σ A B) (λ w → C (pr1 w) (pr2 w)) ≃ Σ A (λ x → Σ (B x) (C x))
  pr1 assoc-Σ' = map-assoc-Σ'
  pr2 assoc-Σ' = is-equiv-map-assoc-Σ'

  inv-assoc-Σ' : Σ A (λ x → Σ (B x) (C x)) ≃ Σ (Σ A B) (λ w → C (pr1 w) (pr2 w))
  pr1 inv-assoc-Σ' = map-inv-assoc-Σ'
  pr2 inv-assoc-Σ' =
    is-equiv-has-inverse
      map-assoc-Σ'
      isretr-map-inv-assoc-Σ'
      issec-map-inv-assoc-Σ'
```

### The interchange law

```
module _
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where
    
  map-interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 (pr1 (map-interchange-Σ-Σ (pair (pair a b) (pair c d)))) = a
  pr2 (pr1 (map-interchange-Σ-Σ (pair (pair a b) (pair c d)))) = c
  pr1 (pr2 (map-interchange-Σ-Σ (pair (pair a b) (pair c d)))) = b
  pr2 (pr2 (map-interchange-Σ-Σ (pair (pair a b) (pair c d)))) = d

  map-inv-interchange-Σ-Σ :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 (pr1 (map-inv-interchange-Σ-Σ (pair (pair a c) (pair b d)))) = a
  pr2 (pr1 (map-inv-interchange-Σ-Σ (pair (pair a c) (pair b d)))) = b
  pr1 (pr2 (map-inv-interchange-Σ-Σ (pair (pair a c) (pair b d)))) = c
  pr2 (pr2 (map-inv-interchange-Σ-Σ (pair (pair a c) (pair b d)))) = d
  
  issec-map-inv-interchange-Σ-Σ :
    ( map-interchange-Σ-Σ ∘ map-inv-interchange-Σ-Σ) ~ id
  issec-map-inv-interchange-Σ-Σ (pair (pair a c) (pair b d)) = refl

  isretr-map-inv-interchange-Σ-Σ :
    ( map-inv-interchange-Σ-Σ ∘ map-interchange-Σ-Σ) ~ id
  isretr-map-inv-interchange-Σ-Σ (pair (pair a b) (pair c d)) = refl

  abstract
    is-equiv-map-interchange-Σ-Σ : is-equiv map-interchange-Σ-Σ
    is-equiv-map-interchange-Σ-Σ =
      is-equiv-has-inverse
        map-inv-interchange-Σ-Σ
        issec-map-inv-interchange-Σ-Σ
        isretr-map-inv-interchange-Σ-Σ

  interchange-Σ-Σ :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) ≃
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 interchange-Σ-Σ = map-interchange-Σ-Σ
  pr2 interchange-Σ-Σ = is-equiv-map-interchange-Σ-Σ
```
