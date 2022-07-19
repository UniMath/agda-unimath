---
title: Truncations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.truncations where

open import foundation-core.truncation-levels using (𝕋; neg-two-𝕋)

open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using
  ( center; is-contr; is-contr-equiv'; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equality-dependent-pair-types using
  ( pair-eq-Σ; eq-pair-Σ)
open import foundation.equivalences using
  ( _≃_; is-equiv; map-inv-equiv; is-equiv-has-inverse;
    inv-equiv; _∘e_; map-equiv; id-equiv)
open import foundation.fibers-of-maps
open import foundation.function-extensionality using (htpy-eq; equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-function-types using
  ( equiv-map-Π; map-equiv-Π)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.homotopies using (_~_; refl-htpy; _·l_)
open import foundation.identity-types using (equiv-inv; _＝_; refl; ap; Id)
open import foundation.propositions using (eq-is-prop')
open import foundation.truncated-types using
  ( is-trunc; Truncated-Type; type-Truncated-Type;
    is-trunc-succ-is-trunc; type-equiv-Truncated-Type;
    Truncated-Type-Truncated-Type; extensionality-Truncated-Type;
    Π-Truncated-Type'; truncated-type-succ-Truncated-Type;
    Id-Truncated-Type; Σ-Truncated-Type; Π-Truncated-Type)

open import foundation-core.truncation-levels
open import foundation-core.universal-property-truncation using
  ( is-truncation; precomp-Trunc; universal-property-truncation;
    universal-property-truncation-is-truncation; map-is-truncation;
    triangle-is-truncation; precomp-Π-Truncated-Type;
    dependent-universal-property-truncation-is-truncation;
    dependent-universal-property-truncation)
open import foundation-core.universe-levels using (Level; UU)
```

## Idea

We postulate the existence of truncations

## Postulates

```agda
postulate
  type-trunc : {l : Level} (k : 𝕋) → UU l → UU l

postulate
  is-trunc-type-trunc :
    {l : Level} {k : 𝕋} {A : UU l} → is-trunc k (type-trunc k A)

trunc : {l : Level} (k : 𝕋) → UU l → Truncated-Type l k
pr1 (trunc k A) = type-trunc k A
pr2 (trunc k A) = is-trunc-type-trunc

postulate
  unit-trunc : {l : Level} {k : 𝕋} {A : UU l} → A → type-trunc k A

postulate
  is-truncation-trunc :
    {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
    is-truncation l2 (trunc k A) unit-trunc

equiv-universal-property-trunc :
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : Truncated-Type l2 k) →
  (type-trunc k A → type-Truncated-Type B) ≃ (A → type-Truncated-Type B)
pr1 (equiv-universal-property-trunc A B) = precomp-Trunc unit-trunc B
pr2 (equiv-universal-property-trunc A B) = is-truncation-trunc B
```

## Properties

### The n-truncations satisfy the universal property

```agda
universal-property-trunc :
  {l1 : Level} (k : 𝕋) (A : UU l1) →
  {l2 : Level} → universal-property-truncation l2 (trunc k A) unit-trunc
universal-property-trunc k A =
  universal-property-truncation-is-truncation
    ( trunc k A)
    ( unit-trunc)
    ( is-truncation-trunc)

module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1}
  where

  apply-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    Σ ( type-trunc k A → type-Truncated-Type B)
      ( λ h → (h ∘ unit-trunc) ~ f)
  apply-universal-property-trunc B f =
    center
      ( universal-property-truncation-is-truncation
        ( trunc k A)
        ( unit-trunc)
        ( is-truncation-trunc)
        ( B)
        ( f))
  
  map-universal-property-trunc :
    (B : Truncated-Type l2 k) → (A → type-Truncated-Type B) →
    type-trunc k A → type-Truncated-Type B
  map-universal-property-trunc B f =
    pr1 (apply-universal-property-trunc B f)

  triangle-universal-property-trunc :
    (B : Truncated-Type l2 k) (f : A → type-Truncated-Type B) →
    (map-universal-property-trunc B f ∘ unit-trunc) ~ f
  triangle-universal-property-trunc B f =
    pr2 (apply-universal-property-trunc B f)
```

### The n-truncations satisfy the dependent universal property

```agda
module _
  {l1 : Level} {k : 𝕋} {A : UU l1}
  where

  dependent-universal-property-trunc :
    {l : Level} →
    dependent-universal-property-truncation l (trunc k A) unit-trunc
  dependent-universal-property-trunc =
    dependent-universal-property-truncation-is-truncation
      ( trunc k A)
      ( unit-trunc)
      ( is-truncation-trunc)

  equiv-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    ((x : type-trunc k A) → type-Truncated-Type (B x)) ≃
    ((a : A) → type-Truncated-Type (B (unit-trunc a)))
  pr1 (equiv-dependent-universal-property-trunc B) =
    precomp-Π-Truncated-Type unit-trunc B
  pr2 (equiv-dependent-universal-property-trunc B) =
    dependent-universal-property-trunc B

  unique-dependent-function-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k)
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    is-contr
      ( Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
          ( λ h → (h ∘ unit-trunc) ~ f))
  unique-dependent-function-trunc B f =
    is-contr-equiv'
      ( fib (precomp-Π-Truncated-Type unit-trunc B) f)
      ( equiv-tot
        ( λ h → equiv-funext))
      ( is-contr-map-is-equiv
        ( dependent-universal-property-trunc B)
        ( f))

  apply-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    Σ ( (x : type-trunc k A) → type-Truncated-Type (B x))
      ( λ h → (h ∘ unit-trunc) ~ f)
  apply-dependent-universal-property-trunc B f =
    center (unique-dependent-function-trunc B f)

  function-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    (x : type-trunc k A) → type-Truncated-Type (B x)
  function-dependent-universal-property-trunc B f =
    pr1 (apply-dependent-universal-property-trunc B f)

  htpy-dependent-universal-property-trunc :
    {l2 : Level} (B : type-trunc k A → Truncated-Type l2 k) →
    (f : (x : A) → type-Truncated-Type (B (unit-trunc x))) →
    ( function-dependent-universal-property-trunc B f ∘ unit-trunc) ~ f
  htpy-dependent-universal-property-trunc B f =
    pr2 (apply-dependent-universal-property-trunc B f)
```

### Families of `k`-truncated-types over `k+1`-truncations of types

```agda
unique-truncated-fam-trunc :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} →
  (B : A → Truncated-Type l2 k) →
  is-contr
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (x : A) → type-equiv-Truncated-Type (B x) (C (unit-trunc x))))
unique-truncated-fam-trunc {l1} {l2} {k} {A} B =
  is-contr-equiv'
    ( Σ ( type-trunc (succ-𝕋 k) A → Truncated-Type l2 k)
        ( λ C → (C ∘ unit-trunc) ~ B))
    ( equiv-tot
      ( λ C →
        equiv-map-Π
          ( λ x →
            ( extensionality-Truncated-Type (B x) (C (unit-trunc x))) ∘e
            ( equiv-inv (C (unit-trunc x)) (B x)))))
    ( universal-property-trunc
      ( succ-𝕋 k)
      ( A)
      ( Truncated-Type-Truncated-Type l2 k)
      ( B))
      
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : A → Truncated-Type l2 k)
  where

  truncated-fam-trunc : type-trunc (succ-𝕋 k) A → Truncated-Type l2 k
  truncated-fam-trunc =
    pr1 (center (unique-truncated-fam-trunc B))

  compute-truncated-fam-trunc :
    (x : A) →
    type-equiv-Truncated-Type (B x) (truncated-fam-trunc (unit-trunc x))
  compute-truncated-fam-trunc =
    pr2 (center (unique-truncated-fam-trunc B))

  elim-truncated-fam-trunc :
    {l3 : Level}
    ( C :
      (x : type-trunc (succ-𝕋 k) A) →
      type-Truncated-Type (truncated-fam-trunc x) → Truncated-Type l3 k) →
    ( f :
      (x : A) (y : type-Truncated-Type (B x)) →
      type-Truncated-Type
        ( C (unit-trunc x) (map-equiv (compute-truncated-fam-trunc x) y))) →
    ( x : type-trunc (succ-𝕋 k) A)
    ( y : type-Truncated-Type (truncated-fam-trunc x)) →
    type-Truncated-Type (C x y)
  elim-truncated-fam-trunc C f =
    function-dependent-universal-property-trunc
      ( λ y →
        truncated-type-succ-Truncated-Type k
          ( Π-Truncated-Type k
            ( truncated-fam-trunc y)
            ( C y)))
      ( λ y →
        map-equiv-Π
          ( λ u → type-Truncated-Type (C (unit-trunc y) u))
          ( compute-truncated-fam-trunc y)
          ( λ u → id-equiv)
          ( f y))
```

### An n-truncated type is equivalent to its n-truncation

```agda
module _
  {l : Level} {k : 𝕋} (A : Truncated-Type l k)
  where

  map-inv-unit-trunc : type-trunc k (type-Truncated-Type A) → type-Truncated-Type A
  map-inv-unit-trunc = map-universal-property-trunc A id

  isretr-map-inv-unit-trunc :
    ( map-inv-unit-trunc ∘ unit-trunc) ~ id
  isretr-map-inv-unit-trunc = triangle-universal-property-trunc A id

  issec-map-inv-unit-trunc :
    ( unit-trunc ∘ map-inv-unit-trunc) ~ id
  issec-map-inv-unit-trunc =
    htpy-eq
      ( pr1
        ( pair-eq-Σ
          ( eq-is-prop'
            ( is-trunc-succ-is-trunc
              ( neg-two-𝕋)
              ( universal-property-trunc
                ( k)
                ( type-Truncated-Type A)
                ( trunc k (type-Truncated-Type A))
                ( unit-trunc)))
            ( pair
              ( unit-trunc ∘ map-inv-unit-trunc)
              ( unit-trunc ·l
                isretr-map-inv-unit-trunc))
            ( pair
              ( id)
              ( refl-htpy)))))

  is-equiv-unit-trunc : is-equiv unit-trunc
  is-equiv-unit-trunc =
    is-equiv-has-inverse
      map-inv-unit-trunc
      issec-map-inv-unit-trunc
      isretr-map-inv-unit-trunc

  equiv-unit-trunc : type-Truncated-Type A ≃ type-trunc k (type-Truncated-Type A)
  pr1 equiv-unit-trunc = unit-trunc
  pr2 equiv-unit-trunc = is-equiv-unit-trunc
```

### Truncation is idempotent

```agda
module _
  {l : Level} (k : 𝕋) (A : UU l)
  where

  idempotent-trunc : type-trunc k (type-trunc k A) ≃ type-trunc k A
  idempotent-trunc = inv-equiv (equiv-unit-trunc (trunc k A))
```

### Characterization of the identity types of truncations

```agda
module _
  {l : Level} (k : 𝕋) {A : UU l} (a : A)
  where

  Eq-trunc-Truncated-Type : type-trunc (succ-𝕋 k) A → Truncated-Type l k
  Eq-trunc-Truncated-Type = truncated-fam-trunc (λ y → trunc k (a ＝ y))

  Eq-trunc : type-trunc (succ-𝕋 k) A → UU l
  Eq-trunc x = type-Truncated-Type (Eq-trunc-Truncated-Type x)

  compute-Eq-trunc : (x : A) → type-trunc k (a ＝ x) ≃ Eq-trunc (unit-trunc x)
  compute-Eq-trunc = compute-truncated-fam-trunc (λ y → trunc k (a ＝ y))

  map-compute-Eq-trunc :
    (x : A) → type-trunc k (a ＝ x) → Eq-trunc (unit-trunc x)
  map-compute-Eq-trunc x = map-equiv (compute-Eq-trunc x)

  refl-Eq-trunc : Eq-trunc (unit-trunc a)
  refl-Eq-trunc = map-compute-Eq-trunc a (unit-trunc refl)

  is-contr-total-Eq-trunc : is-contr (Σ (type-trunc (succ-𝕋 k) A) Eq-trunc)
  pr1 (pr1 is-contr-total-Eq-trunc) = unit-trunc a
  pr2 (pr1 is-contr-total-Eq-trunc) = refl-Eq-trunc
  pr2 is-contr-total-Eq-trunc (pair x e) =
    elim-truncated-fam-trunc
      ( λ y → trunc k (a ＝ y))
      ( λ y p →
        Id-Truncated-Type
          ( Σ-Truncated-Type
            ( trunc (succ-𝕋 k) A)
            ( λ b →
              truncated-type-succ-Truncated-Type k
                ( Eq-trunc-Truncated-Type b)))
          ( pair (unit-trunc a) refl-Eq-trunc)
          ( pair y p))
      ( λ y →
        function-dependent-universal-property-trunc
          ( λ q →
            Id-Truncated-Type
              ( Σ-Truncated-Type
                ( trunc (succ-𝕋 k) A)
                ( λ y →
                  truncated-type-succ-Truncated-Type k
                    ( Eq-trunc-Truncated-Type y)))
              ( pair (unit-trunc a) refl-Eq-trunc)
              ( pair (unit-trunc y) (map-compute-Eq-trunc y q)))
          ( r y))
      ( x)
      ( e)
    where
    r : (y : A) (p : a ＝ y) →
        Id { A = Σ (type-trunc (succ-𝕋 k) A) Eq-trunc}
           ( pair (unit-trunc a) refl-Eq-trunc)
           ( pair (unit-trunc y) (map-compute-Eq-trunc y (unit-trunc p)))
    r y refl = refl
```
