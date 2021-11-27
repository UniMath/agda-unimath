---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundations.13-function-extensionality where

open import foundations.12-truncation-levels public

--------------------------------------------------------------------------------

-- Section 13.1 Equivalent forms of Function Extensionality.

-- Proposition 13.1.1

-- Proposition 13.1.1, condition (i)

htpy-eq :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) → (f ~ g)
htpy-eq refl = refl-htpy

FUNEXT :
  {i j : Level} {A : UU i} {B : A → UU j} →
  (f : (x : A) → B x) → UU (i ⊔ j)
FUNEXT f = is-fiberwise-equiv (λ g → htpy-eq {f = f} {g = g})

-- Proposition 13.1.1, condition (iii)

ev-refl-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
  ((g : (x : A) → B x) (H : f ~ g) → C g H) → C f refl-htpy
ev-refl-htpy f C φ = φ f refl-htpy

IND-HTPY :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) → UU _
IND-HTPY {l1} {l2} {l3} {A} {B} f =
  (C : (g : (x : A) → B x) → (f ~ g) → UU l3) → sec (ev-refl-htpy f C)

-- Proposition 13.1.1, (i) implies (ii)

abstract
  is-contr-total-htpy-FUNEXT :
    {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
    FUNEXT f → is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  is-contr-total-htpy-FUNEXT f funext-f =
    fundamental-theorem-id' f refl-htpy (λ g → htpy-eq {g = g}) funext-f

-- Proposition 13.1.1, (i) implies (iii)

abstract
  IND-HTPY-FUNEXT :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    FUNEXT f → IND-HTPY {l3 = l3} f
  IND-HTPY-FUNEXT {l3 = l3} {A = A} {B = B} f funext-f =
    Ind-identity-system f
      ( refl-htpy)
      ( is-contr-total-htpy-FUNEXT f funext-f)

-- Proposition 13.1.1, (iii) implies (i)

abstract
  FUNEXT-IND-HTPY :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    ({l : Level} → IND-HTPY {l3 = l} f) → FUNEXT f
  FUNEXT-IND-HTPY f ind-htpy-f =
    fundamental-theorem-id-IND-identity-system f
      ( refl-htpy)
      ( ind-htpy-f)
      ( λ g → htpy-eq)

-- Theorem 13.1.4

WEAK-FUNEXT :
  {i j : Level} (A : UU i) (B : A → UU j) → UU (i ⊔ j)
WEAK-FUNEXT A B =
  ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)

abstract
  WEAK-FUNEXT-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f) →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B)
  pr1 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) x = center (is-contr-B x)
  pr2 (WEAK-FUNEXT-FUNEXT funext A B is-contr-B) f =
    map-inv-is-equiv (funext A B c f) (λ x → contraction (is-contr-B x) (f x))
    where
    c : (x : A) → B x
    c x = center (is-contr-B x)

abstract
  FUNEXT-WEAK-FUNEXT :
    {l1 l2 : Level} →
    ((A : UU l1) (B : A → UU l2) → WEAK-FUNEXT A B) →
    ((A : UU l1) (B : A → UU l2) (f : (x : A) → B x) → FUNEXT f)
  FUNEXT-WEAK-FUNEXT weak-funext A B f =
    fundamental-theorem-id f
      ( refl-htpy)
      ( is-contr-retract-of
        ( (x : A) → Σ (B x) (λ b → Id (f x) b))
        ( pair
          ( λ t x → pair (pr1 t x) (pr2 t x))
          ( pair (λ t → pair (λ x → pr1 (t x)) (λ x → pr2 (t x)))
          ( λ t → eq-pair-Σ refl refl)))
        ( weak-funext A
          ( λ x → Σ (B x) (λ b → Id (f x) b))
          ( λ x → is-contr-total-path (f x))))
      ( λ g → htpy-eq {g = g})

-- From now on we will be assuming that function extensionality holds

postulate funext : {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) → FUNEXT f

equiv-funext : {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (Id f g) ≃ (f ~ g)
pr1 (equiv-funext {f = f} {g}) = htpy-eq
pr2 (equiv-funext {f = f} {g}) = funext f g

abstract
  eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    (f ~ g) → Id f g
  eq-htpy = map-inv-is-equiv (funext _ _)
  
  issec-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((htpy-eq {f = f} {g = g}) ∘ (eq-htpy {f = f} {g = g})) ~ id
  issec-eq-htpy = issec-map-inv-is-equiv (funext _ _)
  
  isretr-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
    ((eq-htpy {f = f} {g = g}) ∘ (htpy-eq {f = f} {g = g})) ~ id
  isretr-eq-htpy = isretr-map-inv-is-equiv (funext _ _)

  is-equiv-eq-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f g : (x : A) → B x) → is-equiv (eq-htpy {f = f} {g = g})
  is-equiv-eq-htpy f g = is-equiv-map-inv-is-equiv (funext _ _)

  eq-htpy-refl-htpy :
    {i j : Level} {A : UU i} {B : A → UU j}
    (f : (x : A) → B x) → Id (eq-htpy (refl-htpy {f = f})) refl
  eq-htpy-refl-htpy f = isretr-eq-htpy refl

equiv-eq-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x} →
  (f ~ g) ≃ Id f g
pr1 (equiv-eq-htpy {f = f} {g}) = eq-htpy
pr2 (equiv-eq-htpy {f = f} {g}) = is-equiv-eq-htpy f g

{-
The immediate proof of the following theorem would be

  is-contr-total-htpy-FUNEXT f (funext f)

We give a different proof to ensure that the center of contraction is the 
expected thing: 

  pair f refl-htpy

-}

abstract
  is-contr-total-htpy :
    {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) →
    is-contr (Σ ((x : A) → B x) (λ g → f ~ g))
  pr1 (pr1 (is-contr-total-htpy f)) = f
  pr2 (pr1 (is-contr-total-htpy f)) = refl-htpy
  pr2 (is-contr-total-htpy f) t =
    ( inv
      ( contraction
        ( is-contr-total-htpy-FUNEXT f (funext f))
        ( pair f refl-htpy))) ∙
    ( contraction (is-contr-total-htpy-FUNEXT f (funext f)) t)
  
abstract
  Ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) →
    IND-HTPY {l3 = l3} f
  Ind-htpy f = IND-HTPY-FUNEXT f (funext f)
  
  ind-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    C f refl-htpy → {g : (x : A) → B x} (H : f ~ g) → C g H
  ind-htpy f C t {g} = pr1 (Ind-htpy f C) t g
  
  comp-htpy :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
    (f : (x : A) → B x) (C : (g : (x : A) → B x) → (f ~ g) → UU l3) →
    (c : C f refl-htpy) →
    Id (ind-htpy f C c refl-htpy) c
  comp-htpy f C = pr2 (Ind-htpy f C)

abstract
  is-contr-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-contr (B x)) → is-contr ((x : A) → B x)
  is-contr-Π {A = A} {B = B} = WEAK-FUNEXT-FUNEXT (λ X Y → funext) A B

-- Theorem 13.1.5

abstract
  is-trunc-Π :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-trunc k (B x)) → is-trunc k ((x : A) → B x)
  is-trunc-Π neg-two-𝕋 is-trunc-B = is-contr-Π is-trunc-B
  is-trunc-Π (succ-𝕋 k) is-trunc-B f g =
    is-trunc-is-equiv k (f ~ g) htpy-eq
      ( funext f g)
      ( is-trunc-Π k (λ x → is-trunc-B x (f x) (g x)))

abstract
  is-prop-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-prop ((x : A) → B x)
  is-prop-Π = is-trunc-Π neg-one-𝕋

abstract
  is-prop-Π' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-prop ({x : A} → B x)
  is-prop-Π' {l1} {l2} {A} {B} H =
    is-prop-equiv
      ( pair
        ( λ f x → f {x})
        ( is-equiv-has-inverse
          ( λ g {x} → g x)
          ( refl-htpy)
          ( refl-htpy)))
      ( is-prop-Π H)

abstract
  is-set-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-set (B x)) → is-set ((x : A) → (B x))
  is-set-Π = is-trunc-Π zero-𝕋

abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = is-trunc-Π one-𝕋

-- Corollary 13.1.6

abstract
  is-trunc-function-type :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k B → is-trunc k (A → B)
  is-trunc-function-type k {A} {B} is-trunc-B =
    is-trunc-Π k {B = λ (x : A) → B} (λ x → is-trunc-B)

abstract
  is-prop-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop B → is-prop (A → B)
  is-prop-function-type = is-trunc-function-type neg-one-𝕋

abstract
  is-set-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set B → is-set (A → B)
  is-set-function-type = is-trunc-function-type zero-𝕋

abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = is-trunc-function-type one-𝕋

--------------------------------------------------------------------------------

{- We now do some bureaucracy, ensuring that propositions, sets, and 1-types
   are closed under Π and exponents. All of these will be used implicitly in
   the text. -}

-- We define dependent products on propositions --

type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
type-Π-Prop A P = (x : A) → type-Prop (P x)

is-prop-type-Π-Prop :
  {l1 l2 : Level} (A : UU l1) (P : A → UU-Prop l2) → is-prop (type-Π-Prop A P)
is-prop-type-Π-Prop A P = is-prop-Π (λ x → is-prop-type-Prop (P x))

Π-Prop :
  {l1 l2 : Level} (A : UU l1) →
  (A → UU-Prop l2) → UU-Prop (l1 ⊔ l2)
pr1 (Π-Prop A P) = type-Π-Prop A P
pr2 (Π-Prop A P) = is-prop-type-Π-Prop A P

-- A special case for dependent products on propositions is exponents --

type-function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-function-Prop A P = A → type-Prop P

is-prop-type-function-Prop :
  {l1 l2 : Level} (A : UU l1) (P : UU-Prop l2) →
  is-prop (type-function-Prop A P)
is-prop-type-function-Prop A P =
  is-prop-function-type (is-prop-type-Prop P)

function-Prop :
  {l1 l2 : Level} → UU l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (function-Prop A P) = type-function-Prop A P
pr2 (function-Prop A P) = is-prop-type-function-Prop A P

-- We also define the hom-type of propositions --

type-hom-Prop :
  { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) → UU (l1 ⊔ l2)
type-hom-Prop P Q = type-function-Prop (type-Prop P) Q

is-prop-type-hom-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  is-prop (type-hom-Prop P Q)
is-prop-type-hom-Prop P Q = is-prop-type-function-Prop (type-Prop P) Q

hom-Prop :
  { l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
pr1 (hom-Prop P Q) = type-hom-Prop P Q
pr2 (hom-Prop P Q) = is-prop-type-hom-Prop P Q

implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
implication-Prop P Q = hom-Prop P Q

type-implication-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (l1 ⊔ l2)
type-implication-Prop P Q = type-hom-Prop P Q

-- Negation is a special case of function-Prop and hom-Prop

is-prop-neg : {l : Level} {A : UU l} → is-prop (¬ A)
is-prop-neg {A = A} = is-prop-function-type is-prop-empty

neg-Prop' : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (neg-Prop' A) = ¬ A
pr2 (neg-Prop' A) = is-prop-neg

neg-Prop : {l1 : Level} → UU-Prop l1 → UU-Prop l1
neg-Prop P = neg-Prop' (type-Prop P)

is-prop-is-empty : {l : Level} {A : UU l} → is-prop (is-empty A)
is-prop-is-empty = is-prop-neg

is-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-empty-Prop A) = is-empty A
pr2 (is-empty-Prop A) = is-prop-is-empty

-- Double negation is a special case of negation

dn-Prop' :
  {l : Level} (A : UU l) → UU-Prop l
dn-Prop' A = neg-Prop' (¬ A)

dn-Prop :
  {l : Level} (P : UU-Prop l) → UU-Prop l
dn-Prop P = dn-Prop' (type-Prop P)

-- We define dependent products on sets by an arbitrary indexing type

type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set' A B = (x : A) → type-Set (B x)

is-set-type-Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → is-set (type-Π-Set' A B)
is-set-type-Π-Set' A B =
  is-set-Π (λ x → is-set-type-Set (B x))

Π-Set' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set' A B) = type-Π-Set' A B
pr2 (Π-Set' A B) = is-set-type-Π-Set' A B

-- We define dependent products on sets --

type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) → UU (l1 ⊔ l2)
type-Π-Set A B = type-Π-Set' (type-Set A) B

is-set-type-Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : type-Set A → UU-Set l2) →
  is-set (type-Π-Set A B)
is-set-type-Π-Set A B =
  is-set-type-Π-Set' (type-Set A) B

Π-Set :
  {l1 l2 : Level} (A : UU-Set l1) →
  (type-Set A → UU-Set l2) → UU-Set (l1 ⊔ l2)
pr1 (Π-Set A B) = type-Π-Set A B
pr2 (Π-Set A B) = is-set-type-Π-Set A B

-- We define the type of morphisms between sets --

type-hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU (l1 ⊔ l2)
type-hom-Set A B = type-Set A → type-Set B

is-set-type-hom-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) →
  is-set (type-hom-Set A B)
is-set-type-hom-Set A B = is-set-function-type (is-set-type-Set B)

hom-Set :
  {l1 l2 : Level} → UU-Set l1 → UU-Set l2 → UU-Set (l1 ⊔ l2)
pr1 (hom-Set A B) = type-hom-Set A B
pr2 (hom-Set A B) = is-set-type-hom-Set A B

-- We define the dependent product of 1-types indexed by an arbitrary type

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' A B = (x : A) → type-1-Type (B x)

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' A B =
  is-1-type-Π (λ x → is-1-type-type-1-Type (B x))

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type' A B) = type-Π-1-Type' A B
pr2 (Π-1-Type' A B) = is-1-type-type-Π-1-Type' A B

-- We define the dependent product of 1-types

type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type A B = type-Π-1-Type' (type-1-Type A) B

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type A B =
  is-1-type-type-Π-1-Type' (type-1-Type A) B

Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type A B) = type-Π-1-Type A B
pr2 (Π-1-Type A B) = is-1-type-type-Π-1-Type A B

-- We define the type of morphisms between 1-types

type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type A B = type-1-Type A → type-1-Type B

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type A B =
  is-1-type-function-type (is-1-type-type-1-Type B)

hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (hom-1-Type A B) = type-hom-1-Type A B
pr2 (hom-1-Type A B) = is-1-type-type-hom-1-Type A B

{- We define the dependent product of truncated types indexed by an arbitrary
   type. -}

type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type' k A B = (x : A) → type-Truncated-Type (B x)

is-trunc-type-Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type' k A B)
is-trunc-type-Π-Truncated-Type' k A B =
  is-trunc-Π k (λ x → is-trunc-type-Truncated-Type (B x))

Π-Truncated-Type' :
  (k : 𝕋) {l1 l2 : Level} (A : UU l1) (B : A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
pr1 (Π-Truncated-Type' k A B) = type-Π-Truncated-Type' k A B
pr2 (Π-Truncated-Type' k A B) = is-trunc-type-Π-Truncated-Type' k A B

-- We define the dependent product of truncated types

type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU (l1 ⊔ l2)
type-Π-Truncated-Type k A B =
  type-Π-Truncated-Type' k (type-Truncated-Type A) B

is-trunc-type-Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  is-trunc k (type-Π-Truncated-Type k A B)
is-trunc-type-Π-Truncated-Type k A B =
  is-trunc-type-Π-Truncated-Type' k (type-Truncated-Type A) B

Π-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : type-Truncated-Type A → UU-Truncated-Type k l2) →
  UU-Truncated-Type k (l1 ⊔ l2)
Π-Truncated-Type k A B =
  Π-Truncated-Type' k (type-Truncated-Type A) B

-- We define the type of morphisms between truncated types

type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU (l1 ⊔ l2)
type-hom-Truncated-Type k A B =
  type-Truncated-Type A → type-Truncated-Type B

is-trunc-type-hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) →
  is-trunc k (type-hom-Truncated-Type k A B)
is-trunc-type-hom-Truncated-Type k A B =
  is-trunc-function-type k (is-trunc-type-Truncated-Type B)

hom-Truncated-Type :
  (k : 𝕋) {l1 l2 : Level} (A : UU-Truncated-Type k l1)
  (B : UU-Truncated-Type k l2) → UU-Truncated-Type k (l1 ⊔ l2)
pr1 (hom-Truncated-Type k A B) = type-hom-Truncated-Type k A B
pr2 (hom-Truncated-Type k A B) = is-trunc-type-hom-Truncated-Type k A B

--------------------------------------------------------------------------------

-- Section 13.2 Identity systems on Π-types

{- The type theoretic principle of choice is the assertion that Π distributes
   over Σ. In other words, there is an equivalence

   ((x : A) → Σ (B x) (C x)) ≃ Σ ((x : A) → B x) (λ f → (x : A) → C x (f x)).

   In the following we construct this equivalence, and we also characterize the
   relevant identity types. 

   We call the type on the left-hand side Π-total-fam, and we call the type on
   the right-hand side type-choice-∞. -}
   
Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
type-choice-∞ {A = A} {B} C = Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

{- We compute the identity type of type-choice-∞. Note that its identity 
   type is again of the form type-choice-∞. -}

Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-type-choice-∞ {A = A} {B} C t t' =
  type-choice-∞
    ( λ (x : A) (p : Id ((pr1 t) x) ((pr1 t') x)) →
      Id (tr (C x) p ((pr2 t) x)) ((pr2 t') x))

reflexive-Eq-type-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : type-choice-∞ C) → Eq-type-choice-∞ C t t
pr1 (reflexive-Eq-type-choice-∞ C (pair f g)) = refl-htpy
pr2 (reflexive-Eq-type-choice-∞ C (pair f g)) = refl-htpy

Eq-type-choice-∞-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : type-choice-∞ C) → Id t t' → Eq-type-choice-∞ C t t'
Eq-type-choice-∞-eq C t .t refl = reflexive-Eq-type-choice-∞ C t

abstract
  is-contr-total-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t : type-choice-∞ C) →
    is-contr (Σ (type-choice-∞ C) (Eq-type-choice-∞ C t))
  is-contr-total-Eq-type-choice-∞ {A = A} {B} C t =
    is-contr-total-Eq-structure
      ( λ f g H → (x : A) → Id (tr (C x) (H x) ((pr2 t) x)) (g x))
      ( is-contr-total-htpy (pr1 t))
      ( pair (pr1 t) refl-htpy)
      ( is-contr-total-htpy (pr2 t))
  
  is-equiv-Eq-type-choice-∞-eq :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    (t t' : type-choice-∞ C) → is-equiv (Eq-type-choice-∞-eq C t t')
  is-equiv-Eq-type-choice-∞-eq C t =
    fundamental-theorem-id t
      ( reflexive-Eq-type-choice-∞ C t)
      ( is-contr-total-Eq-type-choice-∞ C t)
      ( Eq-type-choice-∞-eq C t)
  
  eq-Eq-type-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
    {t t' : type-choice-∞ C} → Eq-type-choice-∞ C t t' → Id t t'
  eq-Eq-type-choice-∞ C {t} {t'} =
    map-inv-is-equiv (is-equiv-Eq-type-choice-∞-eq C t t')

-- Theorem 13.2.1

choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → type-choice-∞ C
pr1 (choice-∞ φ) x = pr1 (φ x)
pr2 (choice-∞ φ) x = pr2 (φ x)

inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  type-choice-∞ C → Π-total-fam C
pr1 (inv-choice-∞ ψ x) = (pr1 ψ) x
pr2 (inv-choice-∞ ψ x) = (pr2 ψ) x

issec-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( choice-∞ {A = A} {B = B} {C = C}) ∘
    ( inv-choice-∞ {A = A} {B = B} {C = C})) ~ id
issec-inv-choice-∞ {A = A} {C = C} (pair ψ ψ') =
  eq-Eq-type-choice-∞ C (pair refl-htpy refl-htpy)

isretr-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( inv-choice-∞ {A = A} {B = B} {C = C}) ∘
    ( choice-∞ {A = A} {B = B} {C = C})) ~ id
isretr-inv-choice-∞ φ =
  eq-htpy (λ x → eq-pair-Σ refl refl)

abstract
  is-equiv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (choice-∞ {A = A} {B = B} {C = C})
  is-equiv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-choice-∞ :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
pr1 equiv-choice-∞ = choice-∞
pr2 equiv-choice-∞ = is-equiv-choice-∞

distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ type-choice-∞ C
distributive-Π-Σ = equiv-choice-∞

abstract
  is-equiv-inv-choice-∞ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (inv-choice-∞ {A = A} {B = B} {C = C})
  is-equiv-inv-choice-∞ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( choice-∞ {A = A} {B = B} {C = C})
      ( isretr-inv-choice-∞ {A = A} {B = B} {C = C})
      ( issec-inv-choice-∞ {A = A} {B = B} {C = C})

equiv-inv-choice-∞ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
pr1 (equiv-inv-choice-∞ C) = inv-choice-∞
pr2 (equiv-inv-choice-∞ C) = is-equiv-inv-choice-∞

inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  (type-choice-∞ C) ≃ (Π-total-fam C)
inv-distributive-Π-Σ = equiv-inv-choice-∞

-- Corollary 13.2.2

mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = choice-∞ {B = λ x → B}

abstract
  is-equiv-mapping-into-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
  is-equiv-mapping-into-Σ = is-equiv-choice-∞

{- Next we compute the identity type of products of total spaces. Note again
   that the identity type of a product of total spaces is again a product of
   total spaces. -}

Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-Π-total-fam {A = A} C t t' =
  Π-total-fam (λ x (p : Id (pr1 (t x)) (pr1 (t' x))) →
    Id (tr (C x) p (pr2 (t x))) (pr2 (t' x)))

reflexive-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t
pr1 (reflexive-Eq-Π-total-fam C t a) = refl
pr2 (reflexive-Eq-Π-total-fam C t a) = refl

Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Id t t' → Eq-Π-total-fam C t t'
Eq-Π-total-fam-eq C t .t refl = reflexive-Eq-Π-total-fam C t

is-contr-total-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t : (a : A) → Σ (B a) (C a)) →
  is-contr (Σ ((a : A) → Σ (B a) (C a)) (Eq-Π-total-fam C t))
is-contr-total-Eq-Π-total-fam {A = A} {B} C t =
  is-contr-equiv'
    ( (a : A) →
      Σ (Σ (B a) (C a)) (λ t' →
        Σ (Id (pr1 (t a)) (pr1 t')) (λ p →
          Id (tr (C a) p (pr2 (t a))) (pr2 t'))))
    ( equiv-choice-∞)
    ( is-contr-Π
      ( λ a →
        is-contr-total-Eq-structure
        ( λ b c p → Id (tr (C a) p (pr2 (t a))) c)
        ( is-contr-total-path (pr1 (t a)))
        ( pair (pr1 (t a)) refl)
        ( is-contr-total-path (pr2 (t a)))))

is-equiv-Eq-Π-total-fam-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → is-equiv (Eq-Π-total-fam-eq C t t')
is-equiv-Eq-Π-total-fam-eq C t =
  fundamental-theorem-id t
    ( reflexive-Eq-Π-total-fam C t)
    ( is-contr-total-Eq-Π-total-fam C t)
    ( Eq-Π-total-fam-eq C t)

eq-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C t t' → Id t t'
eq-Eq-Π-total-fam C t t' = map-inv-is-equiv (is-equiv-Eq-Π-total-fam-eq C t t')

-- Corollary 13.2.3. Dependent functions are sections of projection maps

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  equiv-Π-sec-pr1 : sec (pr1 {B = B}) ≃ ((x : A) → B x)
  equiv-Π-sec-pr1 =
    ( ( left-unit-law-Σ-is-contr
        ( is-contr-equiv
          ( Π-total-fam (λ x y → Id y x))
          ( inv-equiv equiv-choice-∞)
          ( is-contr-Π (λ x → is-contr-total-path' x)))
        ( pair id refl-htpy)) ∘e
      ( equiv-right-swap-Σ)) ∘e
    ( equiv-Σ
      ( λ s → pr1 s ~ id)
      ( equiv-choice-∞)
      ( λ s → equiv-id))
      
-- Theorem 13.2.4

is-contr-total-Eq-Π :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3) →
  ( is-contr-total-C : (x : A) → is-contr (Σ (B x) (C x))) →
  is-contr (Σ ((x : A) → B x) (λ g → (x : A) → C x (g x)))
is-contr-total-Eq-Π {A = A} {B} C is-contr-total-C =
  is-contr-equiv'
    ( (x : A) → Σ (B x) (C x))
    ( equiv-choice-∞)
    ( is-contr-Π is-contr-total-C)

--------------------------------------------------------------------------------

-- Section 13.3 Universal properties

-- Theorem 13.3.1

abstract
  is-equiv-ev-pair :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
    is-equiv (ev-pair {C = C})
  pr1 (pr1 is-equiv-ev-pair) = ind-Σ
  pr2 (pr1 is-equiv-ev-pair) = refl-htpy
  pr1 (pr2 is-equiv-ev-pair) = ind-Σ
  pr2 (pr2 is-equiv-ev-pair) f = eq-htpy (ind-Σ (λ x y → refl))

equiv-ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : Σ A B) → C x) ≃ ((a : A) (b : B a) → C (pair a b))
pr1 equiv-ev-pair = ev-pair
pr2 equiv-ev-pair = is-equiv-ev-pair

-- Corollary 13.3.2

-- Theorem 13.3.3

ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → Id a x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → Id (ind-Id a _ (f a refl) x' p') (f x' p'))
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → Id a x → UU l2} →
  ((x : A) (p : Id a x) → B x p) ≃ (B a refl)
pr1 (equiv-ev-refl a) = ev-refl a
pr2 (equiv-ev-refl a) = is-equiv-ev-refl a

--------------------------------------------------------------------------------

-- Section 13.4 Composing with equivalences.

precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

-- Theorem 13.4.1

tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-coherently-invertible :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-coherently-invertible f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-coherently-invertible f
    ( pair g (pair issec-g (pair isretr-g coh))) C = 
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))

abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-coherently-invertible f
      ( is-coherently-invertible-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

abstract
  ind-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
    ((x : A) → C (f x)) → ((y : B) → C y)
  ind-is-equiv C f is-equiv-f =
    map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
  comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
    (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
    Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
  comp-is-equiv C f is-equiv-f h =
    issec-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
  htpy-comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
    (h : (x : A) → C (f x)) →
    (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
  htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)

abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)

abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
pr1 (equiv-precomp e C) = precomp (map-equiv e) C
pr2 (equiv-precomp e C) =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C

abstract
  is-equiv-is-equiv-precomp-subuniverse :
    { l1 l2 : Level}
    ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
    ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B) →
    ( (l : Level) (C : Σ (UU l) (P l)) →
      is-equiv (precomp f (pr1 C))) →
    is-equiv f
  is-equiv-is-equiv-precomp-subuniverse α P A B f is-equiv-precomp-f =
    let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
    is-equiv-has-inverse
      ( pr1 retr-f)
      ( htpy-eq
        ( ap ( pr1)
             ( eq-is-contr'
               ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
                 ( pair
                   ( f ∘ (pr1 retr-f))
                   ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
                 ( pair id refl))))
      ( htpy-eq (pr2 retr-f))

abstract
  is-equiv-is-equiv-precomp :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
  is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse
      ( const Level Level lzero)
      ( λ l X → unit)
      ( pair A star)
      ( pair B star)
      ( f)
      ( λ l C → is-equiv-precomp-f l (pr1 C))

is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : UU-Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : UU-Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : UU-Truncated-Type k l1) (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : UU-Truncated-Type k l) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})

--------------------------------------------------------------------------------

-- Section 13.5 The strong induction principle of ℕ

-- We prove that the induction principle for ℕ implies strong induction.

-- We first prove some lemmas about inequality.

is-prop-leq-ℕ :
  (m n : ℕ) → is-prop (leq-ℕ m n)
is-prop-leq-ℕ zero-ℕ zero-ℕ = is-prop-unit
is-prop-leq-ℕ zero-ℕ (succ-ℕ n) = is-prop-unit
is-prop-leq-ℕ (succ-ℕ m) zero-ℕ = is-prop-empty
is-prop-leq-ℕ (succ-ℕ m) (succ-ℕ n) = is-prop-leq-ℕ m n

leq-ℕ-Prop : ℕ → ℕ → UU-Prop lzero
pr1 (leq-ℕ-Prop m n) = leq-ℕ m n
pr2 (leq-ℕ-Prop m n) = is-prop-leq-ℕ m n

neg-succ-leq-ℕ :
  (n : ℕ) → ¬ (leq-ℕ (succ-ℕ n) n)
neg-succ-leq-ℕ zero-ℕ = id
neg-succ-leq-ℕ (succ-ℕ n) = neg-succ-leq-ℕ n

leq-eq-left-ℕ :
  {m m' : ℕ} → Id m m' → (n : ℕ) → leq-ℕ m n → leq-ℕ m' n
leq-eq-left-ℕ refl n = id

leq-eq-right-ℕ :
  (m : ℕ) {n n' : ℕ} → Id n n' → leq-ℕ m n → leq-ℕ m n'
leq-eq-right-ℕ m refl = id

cases-leq-succ-ℕ :
  {m n : ℕ} → leq-ℕ m (succ-ℕ n) → coprod (leq-ℕ m n) (Id m (succ-ℕ n))
cases-leq-succ-ℕ {zero-ℕ} {n} star = inl star
cases-leq-succ-ℕ {succ-ℕ m} {zero-ℕ} p =
  inr (ap succ-ℕ (antisymmetric-leq-ℕ m zero-ℕ p star))
cases-leq-succ-ℕ {succ-ℕ m} {succ-ℕ n} p =
  map-coprod id (ap succ-ℕ) (cases-leq-succ-ℕ p)

□-≤-ℕ : {l : Level} → (ℕ → UU l) → ℕ → UU l
□-≤-ℕ P n = (m : ℕ) → (m ≤-ℕ n) → P m

η-□-≤-ℕ : {l : Level} {P : ℕ → UU l} → ((n : ℕ) → P n) → (n : ℕ) → □-≤-ℕ P n
η-□-≤-ℕ f n m p = f m

ε-□-≤-ℕ :
  {l : Level} {P : ℕ → UU l} → ((n : ℕ) → □-≤-ℕ P n) → ((n : ℕ) → P n)
ε-□-≤-ℕ f n = f n n (refl-leq-ℕ n)

-- Now we begin with the proof of the theorem
 
-- We first take care of the zero case, with appropriate computation rule.

zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → P zero-ℕ → □-≤-ℕ P zero-ℕ
zero-strong-ind-ℕ P p0 zero-ℕ t = p0

eq-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) (t : leq-ℕ zero-ℕ zero-ℕ) →
  Id (zero-strong-ind-ℕ P p0 zero-ℕ t) p0
eq-zero-strong-ind-ℕ P p0 t = refl

-- Next, we take care of the successor case, with appropriate computation rule.

{- In the successor case, we need to define a map

   □-≤-ℕ P k → □-≤-ℕ P (succ-ℕ k).

   The dependent function in the codomain is defined by case analysis, where
   the cases are that either m ≤ k or m = k+1.
   -}
   
cases-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (n : ℕ) → (□-≤-ℕ P n) → P (succ-ℕ n)) (n : ℕ)
  (H : □-≤-ℕ P n) (m : ℕ) (c : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) → P m
cases-succ-strong-ind-ℕ P pS n H m (inl q) = H m q
cases-succ-strong-ind-ℕ P pS n H .(succ-ℕ n) (inr refl) = pS n H

succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → ((k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))
succ-strong-ind-ℕ P pS k H m p =
  cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p)

-- We use a similar case analysis to obtain the computation rule.

cases-htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (c : coprod (leq-ℕ m k) (Id m (succ-ℕ k))) →
  (q : leq-ℕ m k) →
  Id ( cases-succ-strong-ind-ℕ P pS k H m c)
     ( H m q)
cases-htpy-succ-strong-ind-ℕ P pS k H m (inl p) q =
  ap (H m) (eq-is-prop (is-prop-leq-ℕ m k))
cases-htpy-succ-strong-ind-ℕ P pS k H m (inr α) q =
  ex-falso (neg-succ-leq-ℕ k (leq-eq-left-ℕ α k q))

htpy-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (m : ℕ) (p : leq-ℕ m (succ-ℕ k)) (q : leq-ℕ m k) →
  Id ( succ-strong-ind-ℕ P pS k H m p)
     ( H m q)
htpy-succ-strong-ind-ℕ P pS k H m p q =
  cases-htpy-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p) q

cases-eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k)
  (c : coprod (leq-ℕ (succ-ℕ k) k) (Id (succ-ℕ k) (succ-ℕ k))) →
  Id ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k) c))
     ( pS k H)
cases-eq-succ-strong-ind-ℕ P pS k H (inl p) = ex-falso (neg-succ-leq-ℕ k p)
cases-eq-succ-strong-ind-ℕ P pS k H (inr α) =
  ap ( (cases-succ-strong-ind-ℕ P pS k H (succ-ℕ k)) ∘ inr)
     ( eq-is-prop' (is-set-ℕ (succ-ℕ k) (succ-ℕ k)) α refl)

eq-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  (k : ℕ) (H : □-≤-ℕ P k) (p : leq-ℕ (succ-ℕ k) (succ-ℕ k)) →
  Id ( (succ-strong-ind-ℕ P pS k H (succ-ℕ k) p))
     ( pS k H)
eq-succ-strong-ind-ℕ P pS k H p =
  cases-eq-succ-strong-ind-ℕ P pS k H (cases-leq-succ-ℕ p)

{- Now that we have the base case and inductive step covered, we can proceed
   by induction. -}

induction-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) → (□-≤-ℕ P zero-ℕ) →
  ((k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) → (n : ℕ) → □-≤-ℕ P n
induction-strong-ind-ℕ P q0 qS zero-ℕ = q0
induction-strong-ind-ℕ P q0 qS (succ-ℕ n) =
  qS n (induction-strong-ind-ℕ P q0 qS n)

computation-succ-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (q0 : □-≤-ℕ P zero-ℕ) →
  (qS : (k : ℕ) → (□-≤-ℕ P k) → (□-≤-ℕ P (succ-ℕ k))) →
  (n : ℕ) →
  Id ( induction-strong-ind-ℕ P q0 qS (succ-ℕ n))
     ( qS n (induction-strong-ind-ℕ P q0 qS n))
computation-succ-strong-ind-ℕ P q0 qS n = refl

{- We are finally ready to put things together and define strong-ind-ℕ. -}

strong-ind-ℕ :
  {l : Level} → (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) (n : ℕ) → P n
strong-ind-ℕ P p0 pS = 
  ε-□-≤-ℕ
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS))

{- The computation rule for the base case holds by definition. -}

comp-zero-strong-ind-ℕ :
  {l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  (pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Id (strong-ind-ℕ P p0 pS zero-ℕ) p0
comp-zero-strong-ind-ℕ P p0 pS = refl

{- For the computation rule of the inductive step, we use our hard work. -}

cases-leq-succ-reflexive-leq-ℕ :
  {n : ℕ} → Id (cases-leq-succ-ℕ {succ-ℕ n} {n} (refl-leq-ℕ n)) (inr refl)
cases-leq-succ-reflexive-leq-ℕ {zero-ℕ} = refl
cases-leq-succ-reflexive-leq-ℕ {succ-ℕ n} =
  ap (map-coprod id (ap succ-ℕ)) cases-leq-succ-reflexive-leq-ℕ
  
cases-eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( α :
    ( m : ℕ) (p : leq-ℕ m n) →
    Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
         ( λ k z m₁ z₁ →
           cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
         n m p)
     ( strong-ind-ℕ P p0 pS m)) →
  ( m : ℕ) (p : leq-ℕ m (succ-ℕ n)) →
  ( q : coprod (leq-ℕ m n) (Id m (succ-ℕ n))) →
  Id ( succ-strong-ind-ℕ P pS n
       ( induction-strong-ind-ℕ P
         ( zero-strong-ind-ℕ P p0)
         ( succ-strong-ind-ℕ P pS) n) m p)
     ( strong-ind-ℕ P p0 pS m)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α m p (inl x) =
  ( htpy-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    m p x) ∙
  ( α m x)
cases-eq-comp-succ-strong-ind-ℕ P p0 pS n α .(succ-ℕ n) p (inr refl) =
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS) n)
    ( p)) ∙
  ( inv
    ( ap
      ( cases-succ-strong-ind-ℕ P pS n
        ( induction-strong-ind-ℕ P
          ( zero-strong-ind-ℕ P p0)
          ( λ k H m p₁ →
            cases-succ-strong-ind-ℕ P pS k H m (cases-leq-succ-ℕ p₁))
          n)
        ( succ-ℕ n))
       cases-leq-succ-reflexive-leq-ℕ))

eq-comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  ( m : ℕ) (p : leq-ℕ m n) →
  Id ( induction-strong-ind-ℕ P (zero-strong-ind-ℕ P p0)
       ( λ k z m₁ z₁ →
         cases-succ-strong-ind-ℕ P pS k z m₁ (cases-leq-succ-ℕ z₁))
       n m p)
     ( strong-ind-ℕ P p0 pS m)
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ zero-ℕ star = refl
eq-comp-succ-strong-ind-ℕ P p0 pS zero-ℕ (succ-ℕ m) ()
eq-comp-succ-strong-ind-ℕ P p0 pS (succ-ℕ n) m p =
  cases-eq-comp-succ-strong-ind-ℕ P p0 pS n
    ( eq-comp-succ-strong-ind-ℕ P p0 pS n) m p
    ( cases-leq-succ-ℕ p)

comp-succ-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  ( n : ℕ) →
  Id (strong-ind-ℕ P p0 pS (succ-ℕ n)) (pS n (λ m p → strong-ind-ℕ P p0 pS m))
comp-succ-strong-ind-ℕ P p0 pS n = 
  ( eq-succ-strong-ind-ℕ P pS n
    ( induction-strong-ind-ℕ P
      ( zero-strong-ind-ℕ P p0)
      ( succ-strong-ind-ℕ P pS)
      ( n))
    ( refl-leq-ℕ n)) ∙
  ( ap ( pS n)
       ( eq-htpy
         ( λ m → eq-htpy
           ( λ p → eq-comp-succ-strong-ind-ℕ P p0 pS n m p))))

total-strong-ind-ℕ :
  { l : Level} (P : ℕ → UU l) (p0 : P zero-ℕ) →
  ( pS : (k : ℕ) → (□-≤-ℕ P k) → P (succ-ℕ k)) →
  Σ ( (n : ℕ) → P n)
    ( λ h →
      ( Id (h zero-ℕ) p0) ×
      ( (n : ℕ) → Id (h (succ-ℕ n)) (pS n (λ m p → h m))))
pr1 (total-strong-ind-ℕ P p0 pS) = strong-ind-ℕ P p0 pS
pr1 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-zero-strong-ind-ℕ P p0 pS
pr2 (pr2 (total-strong-ind-ℕ P p0 pS)) = comp-succ-strong-ind-ℕ P p0 pS

```
