---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module univalent-foundations.16-finite-types where

open import foundation public
open import elementary-number-theory public

-- Section 16.3 Finite types

-- Definition 16.3.1

is-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

abstract
  is-prop-is-finite :
    {l : Level} (X : UU l) → is-prop (is-finite X)
  is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

abstract
  is-finite-count :
    {l : Level} {X : UU l} → count X → is-finite X
  is-finite-count = unit-trunc-Prop

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

abstract
  is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
  is-finite-type-𝔽 X = pr2 X

has-cardinality-Prop :
  {l : Level} → UU l → ℕ → UU-Prop l
has-cardinality-Prop X k = mere-equiv-Prop (Fin k) X

has-cardinality :
  {l : Level} → UU l → ℕ → UU l
has-cardinality X k = mere-equiv (Fin k) X

UU-Fin-Level : (l : Level) → ℕ → UU (lsuc l)
UU-Fin-Level l k = Σ (UU l) (mere-equiv (Fin k))

type-UU-Fin-Level : {l : Level} {k : ℕ} → UU-Fin-Level l k → UU l
type-UU-Fin-Level X = pr1 X

abstract
  mere-equiv-UU-Fin-Level :
    {l : Level} {k : ℕ} (X : UU-Fin-Level l k) →
    mere-equiv (Fin k) (type-UU-Fin-Level X)
  mere-equiv-UU-Fin-Level X = pr2 X

UU-Fin : ℕ → UU (lsuc lzero)
UU-Fin k = UU-Fin-Level lzero k

type-UU-Fin : {k : ℕ} → UU-Fin k → UU lzero
type-UU-Fin X = pr1 X

-- Remark 16.3.2

abstract
  is-finite-empty : is-finite empty
  is-finite-empty = is-finite-count count-empty

abstract
  is-finite-is-empty :
    {l1 : Level} {X : UU l1} → is-empty X → is-finite X
  is-finite-is-empty H = is-finite-count (count-is-empty H)

empty-𝔽 : 𝔽
pr1 empty-𝔽 = empty
pr2 empty-𝔽 = is-finite-is-empty id

empty-UU-Fin : UU-Fin zero-ℕ
pr1 empty-UU-Fin = empty
pr2 empty-UU-Fin = unit-trunc-Prop id-equiv

abstract
  is-finite-unit : is-finite unit
  is-finite-unit = is-finite-count count-unit

unit-𝔽 : 𝔽
pr1 unit-𝔽 = unit
pr2 unit-𝔽 = is-finite-unit

unit-UU-Fin : UU-Fin 1
pr1 unit-UU-Fin = unit
pr2 unit-UU-Fin = unit-trunc-Prop (left-unit-law-coprod unit)

abstract
  is-finite-is-contr :
    {l1 : Level} {X : UU l1} → is-contr X → is-finite X
  is-finite-is-contr H = is-finite-count (count-is-contr H)

abstract
  is-finite-is-decidable-Prop :
    {l : Level} (P : UU-Prop l) →
    is-decidable (type-Prop P) → is-finite (type-Prop P)
  is-finite-is-decidable-Prop P (inl x) =
    is-finite-is-contr (is-proof-irrelevant-is-prop (is-prop-type-Prop P) x)
  is-finite-is-decidable-Prop P (inr x) =
    is-finite-is-empty x

abstract
  is-finite-Fin : {k : ℕ} → is-finite (Fin k)
  is-finite-Fin {k} = is-finite-count (count-Fin k)

abstract
  is-finite-ℤ-Mod : {k : ℕ} → is-nonzero-ℕ k → is-finite (ℤ-Mod k)
  is-finite-ℤ-Mod {zero-ℕ} H = ex-falso (H refl)
  is-finite-ℤ-Mod {succ-ℕ k} H = is-finite-Fin

Fin-𝔽 : ℕ → 𝔽
pr1 (Fin-𝔽 k) = Fin k
pr2 (Fin-𝔽 k) = is-finite-Fin

ℤ-Mod-𝔽 : (k : ℕ) → is-nonzero-ℕ k → 𝔽
pr1 (ℤ-Mod-𝔽 k H) = ℤ-Mod k
pr2 (ℤ-Mod-𝔽 k H) = is-finite-ℤ-Mod H

Fin-UU-Fin : (k : ℕ) → UU-Fin k
pr1 (Fin-UU-Fin k) = Fin k
pr2 (Fin-UU-Fin k) = unit-trunc-Prop id-equiv

raise-Fin : (l : Level) (k : ℕ) → UU l
raise-Fin l k = raise l (Fin k)

equiv-raise-Fin : (l : Level) (k : ℕ) → Fin k ≃ raise-Fin l k
equiv-raise-Fin l k = equiv-raise l (Fin k)

map-raise-Fin : (l : Level) (k : ℕ) → Fin k → raise-Fin l k
map-raise-Fin l k = map-raise

Fin-UU-Fin-Level : (l : Level) (k : ℕ) → UU-Fin-Level l k
pr1 (Fin-UU-Fin-Level l k) = raise-Fin l k
pr2 (Fin-UU-Fin-Level l k) = unit-trunc-Prop (equiv-raise-Fin l k)

abstract
  is-finite-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite A → is-finite B
  is-finite-equiv e =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv e))

abstract
  is-finite-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-equiv f → is-finite A → is-finite B
  is-finite-is-equiv is-equiv-f =
    map-universal-property-trunc-Prop
      ( is-finite-Prop _)
      ( is-finite-count ∘ (count-equiv (pair _ is-equiv-f)))

abstract
  is-finite-equiv' :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
    is-finite B → is-finite A
  is-finite-equiv' e = is-finite-equiv (inv-equiv e)

abstract
  is-finite-mere-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-finite A → is-finite B
  is-finite-mere-equiv e H =
    apply-universal-property-trunc-Prop e
      ( is-finite-Prop _)
      ( λ e' → is-finite-equiv e' H)

abstract
  is-finite-type-UU-Fin-Level :
    {l : Level} {k : ℕ} (X : UU-Fin-Level l k) → is-finite (type-UU-Fin-Level X)
  is-finite-type-UU-Fin-Level X =
    is-finite-mere-equiv
      ( mere-equiv-UU-Fin-Level X)
      ( is-finite-Fin)

abstract
  is-finite-type-UU-Fin :
    {k : ℕ} (X : UU-Fin k) → is-finite (type-UU-Fin X)
  is-finite-type-UU-Fin X = is-finite-type-UU-Fin-Level X

abstract
  is-set-is-finite :
    {l : Level} {X : UU l} → is-finite X → is-set X
  is-set-is-finite {l} {X} H =
    apply-universal-property-trunc-Prop H
      ( is-set-Prop X)
      ( λ e → is-set-count e)

has-decidable-equality-is-finite :
  {l1 : Level} {X : UU l1} → is-finite X → has-decidable-equality X
has-decidable-equality-is-finite {l1} {X} is-finite-X =
  apply-universal-property-trunc-Prop is-finite-X
    ( has-decidable-equality-Prop X)
    ( λ e →
      has-decidable-equality-equiv' (equiv-count e) has-decidable-equality-Fin)

has-decidable-equality-has-cardinality :
  {l1 : Level} {X : UU l1} {k : ℕ} →
  has-cardinality X k → has-decidable-equality X
has-decidable-equality-has-cardinality {l1} {X} {k} H =
  apply-universal-property-trunc-Prop H
    ( has-decidable-equality-Prop X)
    ( λ e → has-decidable-equality-equiv' e has-decidable-equality-Fin)

abstract
  is-finite-eq :
    {l1 : Level} {X : UU l1} →
    has-decidable-equality X → {x y : X} → is-finite (Id x y)
  is-finite-eq d {x} {y} = is-finite-count (count-eq d x y)

Id-𝔽 : (X : 𝔽) (x y : type-𝔽 X) → 𝔽
pr1 (Id-𝔽 X x y) = Id x y
pr2 (Id-𝔽 X x y) =
  is-finite-eq (has-decidable-equality-is-finite (is-finite-type-𝔽 X))

-- Theorem 16.3.3

abstract
  mere-equiv-UU-Fin :
    {k : ℕ} (X : UU-Fin k) → mere-equiv (Fin k) (type-UU-Fin X)
  mere-equiv-UU-Fin X = pr2 X

has-finite-cardinality :
  {l : Level} → UU l → UU l
has-finite-cardinality X = Σ ℕ (has-cardinality X)

number-of-elements-has-finite-cardinality :
  {l : Level} {X : UU l} → has-finite-cardinality X → ℕ
number-of-elements-has-finite-cardinality = pr1

abstract
  mere-equiv-has-finite-cardinality :
    {l : Level} {X : UU l} (c : has-finite-cardinality X) →
    type-trunc-Prop (Fin (number-of-elements-has-finite-cardinality c) ≃ X)
  mere-equiv-has-finite-cardinality = pr2

abstract
  all-elements-equal-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → all-elements-equal (has-finite-cardinality X)
  all-elements-equal-has-finite-cardinality {l1} {X} (pair k K) (pair l L) =
    eq-subtype
      ( λ k → mere-equiv-Prop (Fin k) X)
      ( apply-universal-property-trunc-Prop K
        ( pair (Id k l) (is-set-ℕ k l))
        ( λ (e : Fin k ≃ X) →
          apply-universal-property-trunc-Prop L
            ( pair (Id k l) (is-set-ℕ k l))
            ( λ (f : Fin l ≃ X) → is-injective-Fin ((inv-equiv f) ∘e e))))

abstract
  is-prop-has-finite-cardinality :
    {l1 : Level} {X : UU l1} → is-prop (has-finite-cardinality X)
  is-prop-has-finite-cardinality =
    is-prop-all-elements-equal all-elements-equal-has-finite-cardinality

has-finite-cardinality-Prop :
  {l1 : Level} (X : UU l1) → UU-Prop l1
pr1 (has-finite-cardinality-Prop X) = has-finite-cardinality X
pr2 (has-finite-cardinality-Prop X) = is-prop-has-finite-cardinality

module _
  {l : Level} {X : UU l}
  where

  abstract
    is-finite-has-finite-cardinality : has-finite-cardinality X → is-finite X
    is-finite-has-finite-cardinality (pair k K) =
      apply-universal-property-trunc-Prop K
        ( is-finite-Prop X)
        ( is-finite-count ∘ (pair k))

  abstract
    is-finite-has-cardinality : {k : ℕ} → has-cardinality X k → is-finite X
    is-finite-has-cardinality {k} H =
      is-finite-has-finite-cardinality (pair k H)

  has-finite-cardinality-count : count X → has-finite-cardinality X
  pr1 (has-finite-cardinality-count e) = number-of-elements-count e
  pr2 (has-finite-cardinality-count e) = unit-trunc-Prop (equiv-count e)

  abstract
    has-finite-cardinality-is-finite : is-finite X → has-finite-cardinality X
    has-finite-cardinality-is-finite =
      map-universal-property-trunc-Prop
        ( has-finite-cardinality-Prop X)
        ( has-finite-cardinality-count)

  number-of-elements-is-finite : is-finite X → ℕ
  number-of-elements-is-finite =
    number-of-elements-has-finite-cardinality ∘ has-finite-cardinality-is-finite

  abstract
    mere-equiv-is-finite :
      (f : is-finite X) → mere-equiv (Fin (number-of-elements-is-finite f)) X
    mere-equiv-is-finite f =
      mere-equiv-has-finite-cardinality (has-finite-cardinality-is-finite f)

  abstract
    compute-number-of-elements-is-finite :
      (e : count X) (f : is-finite X) →
      Id (number-of-elements-count e) (number-of-elements-is-finite f)
    compute-number-of-elements-is-finite e f =
      ind-trunc-Prop
        ( λ g → Id-Prop ℕ-Set ( number-of-elements-count e)
                              ( number-of-elements-is-finite g))
        ( λ g →
          ( is-injective-Fin ((inv-equiv (equiv-count g)) ∘e (equiv-count e))) ∙
          ( ap pr1
            ( eq-is-prop' is-prop-has-finite-cardinality
              ( has-finite-cardinality-count g)
              ( has-finite-cardinality-is-finite (unit-trunc-Prop g)))))
        ( f)

-- Some immediate conclusions of Theorem 16.3.3

has-finite-cardinality-empty : has-finite-cardinality empty
pr1 has-finite-cardinality-empty = zero-ℕ
pr2 has-finite-cardinality-empty = unit-trunc-Prop id-equiv

has-finite-cardinality-is-empty :
  {l1 : Level} {X : UU l1} → is-empty X → has-finite-cardinality X
pr1 (has-finite-cardinality-is-empty f) = zero-ℕ
pr2 (has-finite-cardinality-is-empty f) =
  unit-trunc-Prop (equiv-count (count-is-empty f))

abstract
  is-empty-is-zero-number-of-elements-is-finite :
    {l1 : Level} {X : UU l1} (f : is-finite X) →
    is-zero-ℕ (number-of-elements-is-finite f) → is-empty X
  is-empty-is-zero-number-of-elements-is-finite {l1} {X} f p =
    apply-universal-property-trunc-Prop f
      ( is-empty-Prop X)
      ( λ e →
        is-empty-is-zero-number-of-elements-count e
          ( compute-number-of-elements-is-finite e f ∙ p))

-- Corollary 16.3.4

map-compute-total-UU-Fin : Σ ℕ UU-Fin → 𝔽
pr1 (map-compute-total-UU-Fin (pair k (pair X e))) = X
pr2 (map-compute-total-UU-Fin (pair k (pair X e))) =
  is-finite-has-finite-cardinality (pair k e)

compute-total-UU-Fin : Σ ℕ UU-Fin ≃ 𝔽
compute-total-UU-Fin =
  ( equiv-tot
    ( λ X →
      equiv-prop
        ( is-prop-has-finite-cardinality)
        ( is-prop-is-finite X)
        ( is-finite-has-finite-cardinality)
        ( has-finite-cardinality-is-finite))) ∘e
  ( equiv-left-swap-Σ)

-- Proposition 16.3.5

abstract
  finite-choice-Fin :
    {l1 : Level} {k : ℕ} {Y : Fin k → UU l1} →
    ((x : Fin k) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : Fin k) → Y x)
  finite-choice-Fin {l1} {zero-ℕ} {Y} H = unit-trunc-Prop ind-empty
  finite-choice-Fin {l1} {succ-ℕ k} {Y} H =
    map-inv-equiv-trunc-Prop
      ( equiv-dependent-universal-property-coprod Y)
      ( map-inv-distributive-trunc-prod-Prop
        ( pair
          ( finite-choice-Fin (λ x → H (inl x)))
          ( map-inv-equiv-trunc-Prop
            ( equiv-dependent-universal-property-unit (Y ∘ inr))
            ( H (inr star)))))

abstract
  finite-choice-count :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → count X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice-count {l1} {l2} {X} {Y} (pair k e) H =
    map-inv-equiv-trunc-Prop
      ( equiv-precomp-Π e Y)
      ( finite-choice-Fin (λ x → H (map-equiv e x)))

abstract
  finite-choice :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} → is-finite X →
    ((x : X) → type-trunc-Prop (Y x)) → type-trunc-Prop ((x : X) → Y x)
  finite-choice {l1} {l2} {X} {Y} is-finite-X H =
    apply-universal-property-trunc-Prop is-finite-X
      ( trunc-Prop ((x : X) → Y x))
      ( λ e → finite-choice-count e H)

-- Remarks

-- Ordering relation on any type A that comes equipped with a count

leq-count :
  {l : Level} {X : UU l} → count X → X → X → UU lzero
leq-count e x y =
  leq-Fin (map-inv-equiv-count e x) (map-inv-equiv-count e y)

refl-leq-count :
  {l : Level} {X : UU l} (e : count X) (x : X) → leq-count e x x
refl-leq-count (pair k e) x = refl-leq-Fin (map-inv-equiv e x)

antisymmetric-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y : X} →
  leq-count e x y → leq-count e y x → Id x y
antisymmetric-leq-count (pair k e) H K =
  is-injective-map-inv-equiv e (antisymmetric-leq-Fin H K)

transitive-leq-count :
  {l : Level} {X : UU l} (e : count X) {x y z : X} →
  leq-count e x y → leq-count e y z → leq-count e x z
transitive-leq-count (pair k e) {x} {y} {z} H K =
  transitive-leq-Fin {x = map-inv-equiv e x} {map-inv-equiv e y} H K

preserves-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-Fin x y → leq-count e (map-equiv-count e x) (map-equiv-count e y)
preserves-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

reflects-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X)
  {x y : Fin (number-of-elements-count e)} →
  leq-count e (map-equiv-count e x) (map-equiv-count e y) → leq-Fin x y
reflects-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( inv (isretr-map-inv-equiv (equiv-count e) x))
    ( H)
    ( isretr-map-inv-equiv (equiv-count e) y)

transpose-leq-equiv-count :
  {l : Level} {X : UU l} (e : count X) →
  {x : Fin (number-of-elements-count e)} {y : X} →
  leq-Fin x (map-inv-equiv-count e y) → leq-count e (map-equiv-count e x) y
transpose-leq-equiv-count e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( isretr-map-inv-equiv (equiv-count e) x)
    ( H)
    ( refl)

transpose-leq-equiv-count' :
  {l : Level} {X : UU l} (e : count X) →
  {x : X} {y : Fin (number-of-elements-count e)} →
  leq-Fin (map-inv-equiv-count e x) y → leq-count e x (map-equiv-count e y)
transpose-leq-equiv-count' e {x} {y} H =
  concatenate-eq-leq-eq-Fin
    ( refl)
    ( H)
    ( inv (isretr-map-inv-equiv (equiv-count e) y))

-- Theorem 16.3.6

-- Theorem 16.3.6 (i)

abstract
  is-finite-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (coprod X Y)
  is-finite-coprod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (coprod X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (coprod X Y))
          ( is-finite-count ∘ (count-coprod e)))

coprod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (coprod-𝔽 X Y) = coprod (type-𝔽 X) (type-𝔽 Y)
pr2 (coprod-𝔽 X Y) = is-finite-coprod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite X
  is-finite-left-coprod =
    functor-trunc-Prop count-left-coprod

abstract
  is-finite-right-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} → is-finite (coprod X Y) →
    is-finite Y
  is-finite-right-coprod =
    functor-trunc-Prop count-right-coprod

coprod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (add-ℕ k l)
pr1 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = coprod X Y
pr2 (coprod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (add-ℕ k l)) (coprod X Y))
        ( λ e2 →
          unit-trunc-Prop
            ( equiv-coprod e1 e2 ∘e inv-equiv (coprod-Fin k l))))

coprod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (add-ℕ k l)
coprod-UU-Fin X Y = coprod-UU-Fin-Level X Y

-- Theorem 16.3.6 (ii)

abstract
  is-finite-prod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite X → is-finite Y → is-finite (X × Y)
  is-finite-prod {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (X × Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop is-finite-Y
          ( is-finite-Prop (X × Y))
          ( is-finite-count ∘ (count-prod e)))

prod-𝔽 : 𝔽 → 𝔽 → 𝔽
pr1 (prod-𝔽 X Y) = prod (type-𝔽 X) (type-𝔽 Y)
pr2 (prod-𝔽 X Y) = is-finite-prod (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y)

abstract
  is-finite-left-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → Y → is-finite X
  is-finite-left-factor f y =
    functor-trunc-Prop (λ e → count-left-factor e y) f

abstract
  is-finite-right-factor :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
    is-finite (X × Y) → X → is-finite Y
  is-finite-right-factor f x =
    functor-trunc-Prop (λ e → count-right-factor e x) f

prod-UU-Fin-Level :
  {l1 l2 : Level} {k l : ℕ} → UU-Fin-Level l1 k → UU-Fin-Level l2 l →
  UU-Fin-Level (l1 ⊔ l2) (mul-ℕ k l)
pr1 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) = X × Y
pr2 (prod-UU-Fin-Level {l1} {l2} {k} {l} (pair X H) (pair Y K)) =
  apply-universal-property-trunc-Prop H
    ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
    ( λ e1 →
      apply-universal-property-trunc-Prop K
        ( mere-equiv-Prop (Fin (mul-ℕ k l)) (X × Y))
        ( λ e2 →
          unit-trunc-Prop (equiv-prod e1 e2 ∘e inv-equiv (prod-Fin k l))))

prod-UU-Fin :
  {k l : ℕ} → UU-Fin k → UU-Fin l → UU-Fin (mul-ℕ k l)
prod-UU-Fin = prod-UU-Fin-Level

-- Theorem 16.3.6 (iii)

-- Theorem 16.3.6 (iii) (a) and (b) implies (c)

abstract
  is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → ((x : X) → is-finite (Y x)) → is-finite (Σ X Y)
  is-finite-Σ {X = X} {Y} is-finite-X is-finite-Y =
    apply-universal-property-trunc-Prop is-finite-X
      ( is-finite-Prop (Σ X Y))
      ( λ (e : count X) →
        apply-universal-property-trunc-Prop
          ( finite-choice is-finite-X is-finite-Y)
          ( is-finite-Prop (Σ X Y))
          ( is-finite-count ∘ (count-Σ e)))

Σ-𝔽 : (X : 𝔽) (Y : type-𝔽 X → 𝔽) → 𝔽
pr1 (Σ-𝔽 X Y) = Σ (type-𝔽 X) (λ x → type-𝔽 (Y x))
pr2 (Σ-𝔽 X Y) =
  is-finite-Σ
    ( is-finite-type-𝔽 X)
    ( λ x → is-finite-type-𝔽 (Y x))

-- Theorem 16.3.6 (iii) (a) and (c) implies (b)

abstract
  is-finite-fiber-is-finite-Σ :
    {l1 l2 : Level} {X : UU l1} {Y : X → UU l2} →
    is-finite X → is-finite (Σ X Y) → (x : X) → is-finite (Y x)
  is-finite-fiber-is-finite-Σ {l1} {l2} {X} {Y} f g x =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop (Y x))
      ( λ e → functor-trunc-Prop (λ h → count-fiber-count-Σ e h x) g)

-- Theorem 16.3.6 (iii) (b), (c), B has a section implies (a)

abstract
  is-finite-base-is-finite-Σ-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-section {l1} {l2} {A} {B} b f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop A)
      ( λ e →
        is-finite-count
          ( count-equiv
            ( ( equiv-total-fib-map-section b) ∘e
              ( equiv-tot
                ( λ t →
                  ( equiv-tot (λ x → equiv-eq-pair-Σ (map-section b x) t)) ∘e
                  ( ( assoc-Σ A
                      ( λ (x : A) → Id x (pr1 t))
                      ( λ s → Id (tr B (pr2 s) (b (pr1 s))) (pr2 t))) ∘e
                    ( inv-left-unit-law-Σ-is-contr
                      ( is-contr-total-path' (pr1 t))
                      ( pair (pr1 t) refl))))))
            ( count-Σ e
              ( λ t →
                count-eq
                  ( has-decidable-equality-is-finite (g (pr1 t)))
                  ( b (pr1 t))
                  ( pr2 t)))))

abstract
  is-finite-base-is-finite-Σ-mere-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    type-trunc-Prop ((x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-mere-section {l1} {l2} {A} {B} H f g =
    apply-universal-property-trunc-Prop H
      ( is-finite-Prop A)
      ( λ b → is-finite-base-is-finite-Σ-section b f g)

abstract
  global-choice-count :
    {l : Level} {A : UU l} → count A → global-choice A
  global-choice-count (pair zero-ℕ e) t =
    ex-falso
      ( is-empty-type-trunc-Prop
        ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
        ( t))
  global-choice-count (pair (succ-ℕ k) e) t = map-equiv e zero-Fin

abstract
  global-choice-decidable-subtype-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
    ((x : A) → is-decidable (type-Prop (P x))) →
    global-choice (type-subtype P)
  global-choice-decidable-subtype-count e P d =
    global-choice-equiv
      ( equiv-Σ-equiv-base (type-Prop ∘ P) (equiv-count e))
      ( global-choice-decidable-subtype-Fin
        ( λ x → P (map-equiv-count e x))
        ( λ x → d (map-equiv-count e x)))

is-inhabited-or-empty-count :
  {l1 : Level} {A : UU l1} → count A → is-inhabited-or-empty A
is-inhabited-or-empty-count (pair zero-ℕ e) =
  inr (is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl)
is-inhabited-or-empty-count (pair (succ-ℕ k) e) =
  inl (unit-trunc-Prop (map-equiv e zero-Fin))

is-inhabited-or-empty-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-inhabited-or-empty A
is-inhabited-or-empty-is-finite {l1} {A} f =
  apply-universal-property-trunc-Prop f
    ( is-inhabited-or-empty-Prop A)
    ( is-inhabited-or-empty-count)

is-decidable-type-trunc-Prop-is-finite :
  {l1 : Level} {A : UU l1} → is-finite A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-finite H =
  map-coprod
    ( id)
    ( map-universal-property-trunc-Prop empty-Prop)
    ( is-inhabited-or-empty-is-finite H)

abstract
  global-choice-emb-count :
    {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
    ((x : A) → is-decidable (fib (map-emb f) x)) → global-choice B
  global-choice-emb-count e f d t =
    map-equiv-total-fib
      ( map-emb f)
      ( global-choice-decidable-subtype-count e
        ( fib-emb-Prop f)
        ( d)
        ( functor-trunc-Prop
          ( map-inv-equiv-total-fib (map-emb f))
          ( t)))

count-type-subtype-is-finite-type-subtype :
  {l1 l2 : Level} {A : UU l1} (e : count A) (P : A → UU-Prop l2) →
  is-finite (Σ A (λ x → type-Prop (P x))) → count (Σ A (λ x → type-Prop (P x)))
count-type-subtype-is-finite-type-subtype {l1} {l2} {A} e P f =
  count-decidable-subtype P d e
  where
  d : (x : A) → is-decidable (type-Prop (P x))
  d x =
    apply-universal-property-trunc-Prop f
      ( is-decidable-Prop (P x))
      ( λ g → is-decidable-count-Σ e g x)

count-domain-emb-is-finite-domain-emb :
  {l1 l2 : Level} {A : UU l1} (e : count A) {B : UU l2} (f : B ↪ A) →
  is-finite B → count B
count-domain-emb-is-finite-domain-emb e f H =
  count-equiv
    ( equiv-total-fib (map-emb f))
    ( count-type-subtype-is-finite-type-subtype e
      ( λ x → pair (fib (map-emb f) x) (is-prop-map-emb f x))
      ( is-finite-equiv'
        ( equiv-total-fib (map-emb f))
        ( H)))

abstract
  choice-count-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → count (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → (x : A) → B x
  choice-count-Σ-is-finite-fiber {l1} {l2} {A} {B} K e g H x =
    global-choice-count
      ( count-domain-emb-is-finite-domain-emb e
        ( fiber-inclusion-emb (pair A K) B x)
        ( g x))
      ( H x)

abstract
  choice-is-finite-Σ-is-finite-fiber :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    ((x : A) → type-trunc-Prop (B x)) → type-trunc-Prop ((x : A) → B x)
  choice-is-finite-Σ-is-finite-fiber {l1} {l2} {A} {B} K f g H =
    apply-universal-property-trunc-Prop f
      ( trunc-Prop ((x : A) → B x))
      ( λ e → unit-trunc-Prop (choice-count-Σ-is-finite-fiber K e g H))

abstract
  is-finite-base-is-finite-Σ-merely-inhabited :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → (b : (x : A) → type-trunc-Prop (B x)) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) → is-finite A
  is-finite-base-is-finite-Σ-merely-inhabited {l1} {l2} {A} {B} K b f g =
    is-finite-base-is-finite-Σ-mere-section
      ( choice-is-finite-Σ-is-finite-fiber K f g b)
      ( f)
      ( g)

-- Theorem 16.3.6 Immediate corollaries and bureaucracy

abstract
  is-finite-fib :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) →
    is-finite X → is-finite Y → (y : Y) → is-finite (fib f y)
  is-finite-fib f is-finite-X is-finite-Y y =
    apply-universal-property-trunc-Prop
      ( is-finite-X)
      ( is-finite-Prop (fib f y))
      ( λ H →
        apply-universal-property-trunc-Prop
          ( is-finite-Y)
          ( is-finite-Prop (fib f y))
          ( λ K → unit-trunc-Prop (count-fib f H K y)))

fib-𝔽 : (X Y : 𝔽) (f : type-𝔽 X → type-𝔽 Y) → type-𝔽 Y → 𝔽
pr1 (fib-𝔽 X Y f y) = fib f y
pr2 (fib-𝔽 X Y f y) =
  is-finite-fib f (is-finite-type-𝔽 X) (is-finite-type-𝔽 Y) y

abstract
  is-finite-fib-map-section :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
    is-finite (Σ A B) → ((x : A) → is-finite (B x)) →
    (t : Σ A B) → is-finite (fib (map-section b) t)
  is-finite-fib-map-section {l1} {l2} {A} {B} b f g (pair y z) =
    is-finite-equiv'
      ( ( ( left-unit-law-Σ-is-contr
            ( is-contr-total-path' y)
            ( pair y refl)) ∘e
          ( inv-assoc-Σ A
            ( λ x → Id x y)
            ( λ t → Id (tr B (pr2 t) (b (pr1 t))) z))) ∘e
        ( equiv-tot (λ x → equiv-pair-eq-Σ (pair x (b x)) (pair y z))))
      ( is-finite-eq (has-decidable-equality-is-finite (g y)))

count-type-trunc-Prop :
  {l1 : Level} {A : UU l1} → count A → count (type-trunc-Prop A)
count-type-trunc-Prop (pair zero-ℕ e) =
  count-is-empty
    ( is-empty-type-trunc-Prop
      ( is-empty-is-zero-number-of-elements-count (pair zero-ℕ e) refl))
count-type-trunc-Prop (pair (succ-ℕ k) e) =
  count-is-contr
    ( is-proof-irrelevant-is-prop
      ( is-prop-type-trunc-Prop)
      ( unit-trunc-Prop (map-equiv e zero-Fin)))

abstract
  is-finite-type-trunc-Prop :
    {l1 : Level} {A : UU l1} → is-finite A → is-finite (type-trunc-Prop A)
  is-finite-type-trunc-Prop = functor-trunc-Prop count-type-trunc-Prop

trunc-Prop-𝔽 : 𝔽 → 𝔽
pr1 (trunc-Prop-𝔽 A) = type-trunc-Prop (type-𝔽 A)
pr2 (trunc-Prop-𝔽 A) = is-finite-type-trunc-Prop (is-finite-type-𝔽 A)

complement :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
complement {l1} {l2} {A} B = Σ A (is-empty ∘ B)

abstract
  is-finite-base-is-finite-complement :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-set A →
    is-finite (Σ A B) → (g : (x : A) → is-finite (B x)) →
    is-finite (complement B) → is-finite A
  is-finite-base-is-finite-complement {l1} {l2} {A} {B} K f g h =
    is-finite-equiv
      ( ( right-unit-law-Σ-is-contr
          ( λ x →
            is-proof-irrelevant-is-prop
              ( is-prop-is-inhabited-or-empty (B x))
              ( is-inhabited-or-empty-is-finite (g x)))) ∘e
        ( inv-equiv
          ( left-distributive-Σ-coprod A
            ( λ x → type-trunc-Prop (B x))
            ( λ x → is-empty (B x)))))
      ( is-finite-coprod
        ( is-finite-base-is-finite-Σ-merely-inhabited
          ( is-set-is-subtype (λ x → is-prop-type-trunc-Prop) K)
          ( λ t → pr2 t)
          ( is-finite-equiv
            ( equiv-right-swap-Σ)
            ( is-finite-Σ
              ( f)
              ( λ x → is-finite-type-trunc-Prop (g (pr1 x)))))
          ( λ x → g (pr1 x)))
        ( h))  

--------------------------------------------------------------------------------

Π-ℕ : (k : ℕ) → (Fin k → ℕ) → ℕ
Π-ℕ zero-ℕ x = 1
Π-ℕ (succ-ℕ k) x = mul-ℕ (Π-ℕ k (λ i → x (inl i))) (x (inr star))

count-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → count (B x)) → count ((x : Fin k) → B x)
count-Π-Fin {l1} {zero-ℕ} {B} e =
  count-is-contr (dependent-universal-property-empty' B)
count-Π-Fin {l1} {succ-ℕ k} {B} e =
  count-equiv'
    ( equiv-dependent-universal-property-coprod B)
    ( count-prod
      ( count-Π-Fin (λ x → e (inl x)))
      ( count-equiv'
        ( equiv-dependent-universal-property-unit (B ∘ inr))
        ( e (inr star))))

count-Π :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → count (B x)) → count ((x : A) → B x)
count-Π {l1} {l2} {A} {B} e f =
  count-equiv'
    ( equiv-precomp-Π (equiv-count e) B)
    ( count-Π-Fin (λ x → f (map-equiv-count e x)))

count-function-type :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  count A → count B → count (A → B)
count-function-type e f =
  count-Π e (λ x → f)

abstract
  is-finite-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-finite A → ((x : A) → is-finite (B x)) → is-finite ((x : A) → B x)
  is-finite-Π {l1} {l2} {A} {B} f g =
    apply-universal-property-trunc-Prop f
      ( is-finite-Prop ((x : A) → B x))
      ( λ e →
        apply-universal-property-trunc-Prop
          ( finite-choice f g)
          ( is-finite-Prop ((x : A) → B x))
          ( λ h → unit-trunc-Prop (count-Π e h)))

Π-𝔽 : (A : 𝔽) (B : type-𝔽 A → 𝔽) → 𝔽
pr1 (Π-𝔽 A B) = (x : type-𝔽 A) → type-𝔽 (B x)
pr2 (Π-𝔽 A B) = is-finite-Π (is-finite-type-𝔽 A) (λ x → is-finite-type-𝔽 (B x))

abstract
  is-finite-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A → B)
  is-finite-function-type f g = is-finite-Π f (λ x → g)

_→-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A →-𝔽 B) = type-𝔽 A → type-𝔽 B
pr2 (A →-𝔽 B) =
  is-finite-function-type (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

abstract
  is-finite-≃ :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-finite A → is-finite B → is-finite (A ≃ B)
  is-finite-≃ f g =
    is-finite-Σ
      ( is-finite-function-type f g)
      ( λ h →
        is-finite-prod
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π g
                ( λ y → is-finite-eq (has-decidable-equality-is-finite g))))
          ( is-finite-Σ
            ( is-finite-function-type g f)
            ( λ k →
              is-finite-Π f
                ( λ x → is-finite-eq (has-decidable-equality-is-finite f)))))

_≃-𝔽_ : 𝔽 → 𝔽 → 𝔽
pr1 (A ≃-𝔽 B) = type-𝔽 A ≃ type-𝔽 B
pr2 (A ≃-𝔽 B) = is-finite-≃ (is-finite-type-𝔽 A) (is-finite-type-𝔽 B)

Aut-𝔽 : 𝔽 → 𝔽
Aut-𝔽 A = A ≃-𝔽 A

--------------------------------------------------------------------------------

-- A combinatorial proof that finite sums are associative

abstract
  associative-sum-count-ℕ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (count-A : count A)
    (count-B : (x : A) → count (B x)) (f : (x : A) → B x → ℕ) →
    Id ( sum-count-ℕ count-A (λ x → sum-count-ℕ (count-B x) (f x)))
      ( sum-count-ℕ (count-Σ count-A count-B) (ind-Σ f))
  associative-sum-count-ℕ {l1} {l2} {A} {B} count-A count-B f =
    ( ( ap-sum-count-ℕ count-A
        ( λ x →
          inv
          ( number-of-elements-count-Σ
            ( count-B x)
            ( λ y → count-Fin (f x y))))) ∙
      ( inv
        ( number-of-elements-count-Σ count-A
          ( λ x → count-Σ (count-B x) (λ y → count-Fin (f x y)))))) ∙
    ( ( double-counting-equiv
        ( count-Σ count-A (λ x → count-Σ (count-B x) (λ y → count-Fin (f x y))))
        ( count-Σ (count-Σ count-A count-B) (λ x → count-Fin (ind-Σ f x)))
        ( inv-assoc-Σ A B (λ x → Fin (ind-Σ f x)))) ∙
      ( number-of-elements-count-Σ
        ( count-Σ count-A count-B)
        ( λ x → (count-Fin (ind-Σ f x)))))

--------------------------------------------------------------------------------

-- Unital magmas

Magma-UU : (l : Level) → UU (lsuc l)
Magma-UU l = Σ (UU l) (λ A → A → A → A)

type-Magma : {l : Level} → Magma-UU l → UU l
type-Magma M = pr1 M

μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M → type-Magma M → type-Magma M
μ-Magma M = pr2 M

fold-Fin-μ-Magma :
  {l : Level} (M : Magma-UU l) → type-Magma M →
  {k : ℕ} → (Fin k → type-Magma M) → type-Magma M
fold-Fin-μ-Magma M m {zero-ℕ} f = m
fold-Fin-μ-Magma M m {succ-ℕ k} f =
  μ-Magma M (fold-Fin-μ-Magma M m (f ∘ inl)) (f (inr star))

fold-count-μ-Magma' :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} {k : ℕ} → (Fin k ≃ A) → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma' M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv e)

fold-count-μ-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) → type-Magma M →
  {A : UU l2} → count A → (A → type-Magma M) → type-Magma M
fold-count-μ-Magma M m e f = fold-Fin-μ-Magma M m (f ∘ map-equiv-count e)

is-unital-Magma : {l : Level} (M : Magma-UU l) → UU l
is-unital-Magma M =
  Σ ( type-Magma M)
    ( λ e →
      ( (x : type-Magma M) → Id (μ-Magma M e x) x) ×
      ( (x : type-Magma M) → Id (μ-Magma M x e) x))

Unital-Magma-UU : (l : Level) → UU (lsuc l)
Unital-Magma-UU l = Σ (Magma-UU l) is-unital-Magma

magma-Unital-Magma :
  {l : Level} → Unital-Magma-UU l → Magma-UU l
magma-Unital-Magma M = pr1 M
  
is-unital-magma-Unital-Magma :
  {l : Level} (M : Unital-Magma-UU l) → is-unital-Magma (magma-Unital-Magma M)
is-unital-magma-Unital-Magma M = pr2 M

is-semigroup-Magma : {l : Level} → Magma-UU l → UU l
is-semigroup-Magma M =
  (x y z : type-Magma M) →
  Id (μ-Magma M (μ-Magma M x y) z) (μ-Magma M x (μ-Magma M y z))

is-commutative-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-Magma M =
  (x y : type-Magma M) → Id (μ-Magma M x y) (μ-Magma M y x)

is-commutative-monoid-Magma : {l : Level} → Magma-UU l → UU l
is-commutative-monoid-Magma M =
  ((is-semigroup-Magma M) × (is-unital-Magma M)) × (is-commutative-Magma M)

unit-is-commutative-monoid-Magma :
  {l : Level} (M : Magma-UU l) → is-commutative-monoid-Magma M → type-Magma M
unit-is-commutative-monoid-Magma M H = pr1 (pr2 (pr1 H))

swap-with-Fin : {k : ℕ} (x y : Fin k) → Fin k → Fin k
swap-with-Fin {k} x y z
  with has-decidable-equality-Fin x z | has-decidable-equality-Fin y z
... | inl p | d = y
... | inr f | inl q = x
... | inr f | inr g = z


{-
permutation-fold-Fin-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M) →
  {k : ℕ} (e : Fin k ≃ Fin k) (f : Fin k → type-Magma M) →
  Id ( fold-Fin-μ-Magma M
       ( unit-is-commutative-monoid-Magma M H)
       ( f ∘ map-equiv e))
     ( fold-Fin-μ-Magma M (unit-is-commutative-monoid-Magma M H) f)
permutation-fold-Fin-μ-is-commutative-monoid-Magma M H {k} e f = {!!}

is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma :
  {l1 l2 : Level} (M : Magma-UU l1) (H : is-commutative-monoid-Magma M)
  {A : UU l2} {k : ℕ} →
  is-weakly-constant-map
    ( fold-count-μ-Magma' M (unit-is-commutative-monoid-Magma M H) {A} {k = k})
is-weakly-constant-map-fold-count-μ-is-commutative-monoid-Magma M H {k} e f = {!!}
-}

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise 16.1

is-decidable-fib-retract-has-decidable-equality :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → has-decidable-equality B →
  (i : A → B) → retr i → (b : B) → is-decidable (fib i b)
is-decidable-fib-retract-has-decidable-equality d i (pair r R) b =
  is-decidable-iff
    ( λ (p : Id (i (r b)) b) → pair (r b) p)
    ( λ t → ap (i ∘ r) (inv (pr2 t)) ∙ (ap i (R (pr1 t)) ∙ pr2 t))
    ( d (i (r b)) b)

is-decidable-fib-retract-ℕ :
  {l1 : Level} {A : UU l1} (i : A → ℕ) → retr i → (x : ℕ) →
  is-decidable (fib i x)
is-decidable-fib-retract-ℕ =
  is-decidable-fib-retract-has-decidable-equality has-decidable-equality-ℕ

is-decidable-fib-retract-Fin :
  {l1 : Level} {k : ℕ} {A : UU l1} (i : A → Fin k) → retr i → (x : Fin k) →
  is-decidable (fib i x)
is-decidable-fib-retract-Fin {l1} {k} =
  is-decidable-fib-retract-has-decidable-equality has-decidable-equality-Fin

is-decidable-fib-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) → retr i →
  (y : B) → is-decidable (fib i y)
is-decidable-fib-retract-count e =
  is-decidable-fib-retract-has-decidable-equality
    ( has-decidable-equality-count e)

is-decidable-fib-retract-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite B) (i : A → B) →
  retr i → (y : B) → is-decidable (fib i y)
is-decidable-fib-retract-is-finite H =
  is-decidable-fib-retract-has-decidable-equality
    ( has-decidable-equality-is-finite H)

abstract
  is-injective-retr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → retr f →
    is-injective f
  is-injective-retr f (pair h H) {x} {y} p = (inv (H x)) ∙ (ap h p ∙ H y)

abstract
  is-emb-retract-count :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
    retr i → is-emb i
  is-emb-retract-count e i R =
    is-emb-is-injective (is-set-count e) (is-injective-retr i R)

emb-retract-count :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count B) (i : A → B) →
  retr i → A ↪ B
pr1 (emb-retract-count e i R) = i
pr2 (emb-retract-count e i R) = is-emb-retract-count e i R

count-retract :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → count B → count A
count-retract (pair i R) e =
  count-equiv
    ( equiv-total-fib i)
    ( count-decidable-subtype
      ( fib-emb-Prop (emb-retract-count e i R))
      ( is-decidable-fib-retract-count e i R)
      ( e))

abstract
  is-finite-retract :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} → A retract-of B →
    is-finite B → is-finite A
  is-finite-retract R = functor-trunc-Prop (count-retract R)

-- Exercise 16.2

-- Exercise 16.2 (a)

is-decidable-Π-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : coprod A B → UU l3} →
  is-decidable ((a : A) → C (inl a)) → is-decidable ((b : B) → C (inr b)) →
  is-decidable ((x : coprod A B) → C x)
is-decidable-Π-coprod {C = C} dA dB =
  is-decidable-equiv
    ( equiv-dependent-universal-property-coprod C)
    ( is-decidable-prod dA dB)

is-decidable-Π-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable ((x : A) → B (unit-Maybe x)) → is-decidable (B exception-Maybe) →
  is-decidable ((x : Maybe A) → B x)
is-decidable-Π-Maybe {B = B} du de =
  is-decidable-equiv
    ( equiv-dependent-universal-property-Maybe B)
    ( is-decidable-prod du de)

is-decidable-Π-Fin :
  {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
  ((x : Fin k) → is-decidable (B x)) → is-decidable ((x : Fin k) → B x)
is-decidable-Π-Fin {l1} {zero-ℕ} {B} d = inl ind-empty
is-decidable-Π-Fin {l1} {succ-ℕ k} {B} d =
  is-decidable-Π-Maybe
    ( is-decidable-Π-Fin (λ x → d (inl x)))
    ( d (inr star))

is-decidable-Π-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((x : A) → C x) → is-decidable ((y : B) → D y)
is-decidable-Π-equiv {D = D} e f = is-decidable-equiv' (equiv-Π D e f)

is-decidable-Π-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable ((y : B) → D y) → is-decidable ((x : A) → C x)
is-decidable-Π-equiv' {D = D} e f = is-decidable-equiv (equiv-Π D e f)

is-decidable-Π-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  count A → ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-count e d =
  is-decidable-Π-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Π-Fin (λ x → d (map-equiv-count e x)))

is-decidable-Π-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-finite A →
  ((x : A) → is-decidable (B x)) → is-decidable ((x : A) → B x)
is-decidable-Π-is-finite {l1} {l2} {A} {B} H d =
  is-decidable-iff
    ( map-Π (λ x → elim-trunc-Prop-is-decidable (d x)))
    ( map-Π (λ x → unit-trunc-Prop))
    ( is-decidable-iff
      ( α)
      ( finite-choice H)
      ( apply-universal-property-trunc-Prop H
        ( is-decidable-Prop (trunc-Prop ((x : A) → B x)))
        ( λ e →
          is-decidable-iff
            ( finite-choice H)
            ( α)
            ( is-decidable-Π-count e
              ( λ x →
                is-decidable-iff
                  ( unit-trunc-Prop)
                  ( elim-trunc-Prop-is-decidable (d x))
                  ( d x))))))
  where
  α : type-trunc-Prop ((x : A) → B x) → (x : A) → type-trunc-Prop (B x)
  α = map-universal-property-trunc-Prop
        ( Π-Prop A (λ x → trunc-Prop (B x)))
        ( λ (f : (x : A) → B x) (x : A) → unit-trunc-Prop (f x))

-- Remark: The analogous development for Σ-types stops at is-decidable-Σ-count

is-decidable-Σ-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  is-decidable (Σ A (C ∘ inl)) → is-decidable (Σ B (C ∘ inr)) →
  is-decidable (Σ (coprod A B) C)
is-decidable-Σ-coprod {l1} {l2} {l3} {A} {B} C dA dB =
  is-decidable-equiv
    ( right-distributive-Σ-coprod A B C)
    ( is-decidable-coprod dA dB)

is-decidable-Σ-Maybe :
  {l1 l2 : Level} {A : UU l1} {B : Maybe A → UU l2} →
  is-decidable (Σ A (B ∘ unit-Maybe)) → is-decidable (B exception-Maybe) →
  is-decidable (Σ (Maybe A) B)
is-decidable-Σ-Maybe {l1} {l2} {A} {B} dA de =
  is-decidable-Σ-coprod B dA
    ( is-decidable-equiv
      ( left-unit-law-Σ (B ∘ inr))
      ( de))

is-decidable-Σ-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ A C) → is-decidable (Σ B D)
is-decidable-Σ-equiv {D = D} e f =
  is-decidable-equiv' (equiv-Σ D e f)

is-decidable-Σ-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} {D : B → UU l4}
  (e : A ≃ B) (f : (x : A) → C x ≃ D (map-equiv e x)) →
  is-decidable (Σ B D) → is-decidable (Σ A C)
is-decidable-Σ-equiv' {D = D} e f =
  is-decidable-equiv (equiv-Σ D e f) 

is-decidable-Σ-count :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → count A →
  ((x : A) → is-decidable (B x)) → is-decidable (Σ A B)
is-decidable-Σ-count e d =
  is-decidable-Σ-equiv
    ( equiv-count e)
    ( λ x → id-equiv)
    ( is-decidable-Σ-Fin (λ x → d (map-equiv-count e x)))

-- There is no way to construct a function is-decidable-Σ-is-finite. This would
-- contradict the univalence axiom.

-- Exercise 16.2 (b)

is-decidable-is-injective-is-finite' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable ((x y : A) → Id (f x) (f y) → Id x y)
is-decidable-is-injective-is-finite' f HA HB =
  is-decidable-Π-is-finite HA
    ( λ x →
      is-decidable-Π-is-finite HA
        ( λ y →
          is-decidable-function-type
            ( has-decidable-equality-is-finite HB (f x) (f y))
            ( has-decidable-equality-is-finite HA x y)))

is-decidable-is-injective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-injective f)
is-decidable-is-injective-is-finite f HA HB =
  is-decidable-iff
    ( λ p {x} {y} → p x y)
    ( λ p x y → p)
    ( is-decidable-is-injective-is-finite' f HA HB)

is-decidable-is-emb-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-emb f)
is-decidable-is-emb-is-finite f HA HB =
  is-decidable-iff
    ( is-emb-is-injective (is-set-is-finite HB))
    ( is-injective-is-emb)
    ( is-decidable-is-injective-is-finite f HA HB)

-- Exercise 16.2 (c)

is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fib f HA HB y))

-- Exercise 16.2 (d)

is-decidable-is-equiv-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-equiv f)
is-decidable-is-equiv-is-finite f HA HB =
  is-decidable-iff
    ( λ p → is-equiv-is-emb-is-surjective (pr1 p) (pr2 p))
    ( λ K → pair (is-surjective-is-equiv K) (is-emb-is-equiv K))
    ( is-decidable-prod
      ( is-decidable-is-surjective-is-finite f HA HB)
      ( is-decidable-is-emb-is-finite f HA HB))

-- Exercise 16.4

-- Exercise 16.4 (b)

-- The number falling-factorial-ℕ n m is the number (n)_m from combinatorics

falling-factorial-ℕ : ℕ → ℕ → ℕ
falling-factorial-ℕ zero-ℕ zero-ℕ = 1
falling-factorial-ℕ zero-ℕ (succ-ℕ m) = 0
falling-factorial-ℕ (succ-ℕ n) zero-ℕ = 1
falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  mul-ℕ (succ-ℕ n) (falling-factorial-ℕ n m)

{-
Fin-falling-factorial-ℕ :
  (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ n m = {!!}
-}

{-
Fin-falling-factorial-ℕ : (n m : ℕ) → Fin (falling-factorial-ℕ n m) ≃ (Fin m ↪ Fin n)
Fin-falling-factorial-ℕ zero-ℕ zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb id)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' empty)
        ( id))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap id))))
Fin-falling-factorial-ℕ zero-ℕ (succ-ℕ m) =
  equiv-is-empty id (λ f → map-emb f (inr star))
Fin-falling-factorial-ℕ (succ-ℕ n) zero-ℕ =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-equiv
      ( is-emb ex-falso)
      ( left-unit-law-Σ-is-contr
        ( universal-property-empty' (Fin (succ-ℕ n)))
        ( ex-falso))
      ( dependent-universal-property-empty'
        ( λ x → (y : empty) → is-equiv (ap ex-falso))))
Fin-falling-factorial-ℕ (succ-ℕ n) (succ-ℕ m) =
  ( ( ( right-unit-law-Σ-is-contr
        { B = λ f → is-decidable (fib (map-emb f) (inr star))}
        ( λ f →
          is-proof-irrelevant-is-prop
            ( is-prop-is-decidable
              ( is-prop-map-is-emb (is-emb-map-emb f) (inr star)))
            ( is-decidable-Σ-Fin
              ( λ x →
                has-decidable-equality-Fin (map-emb f x) (inr star))))) ∘e
      ( ( inv-equiv
          ( left-distributive-Σ-coprod
            ( Fin (succ-ℕ m) ↪ Fin (succ-ℕ n))
            ( λ f → fib (map-emb f) (inr star))
            ( λ f → ¬ (fib (map-emb f) (inr star))))) ∘e
        {!!})) ∘e
    ( equiv-coprod (Fin-falling-factorial-ℕ n m) (Fin-falling-factorial-ℕ n (succ-ℕ m)))) ∘e
  ( Fin-add-ℕ (falling-factorial-ℕ n m) (falling-factorial-ℕ n (succ-ℕ m)))
-}

-- Exercise 16.4 (d)

stirling-number-second-kind : ℕ → ℕ → ℕ
stirling-number-second-kind zero-ℕ zero-ℕ = 1
stirling-number-second-kind zero-ℕ (succ-ℕ n) = 0
stirling-number-second-kind (succ-ℕ m) zero-ℕ = 0
stirling-number-second-kind (succ-ℕ m) (succ-ℕ n) =
  add-ℕ
    ( mul-ℕ (succ-ℕ n) (stirling-number-second-kind m (succ-ℕ n)))
    ( stirling-number-second-kind m n)

-- Exercise 16.8

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  (K : is-finite A)
  where

  abstract
    is-finite-codomain :
      is-surjective f → has-decidable-equality B → is-finite B
    is-finite-codomain H d =
      is-finite-base-is-finite-Σ-merely-inhabited
        ( is-set-has-decidable-equality d)
        ( H)
        ( is-finite-equiv' (equiv-total-fib f) K)
        ( λ b → is-finite-Σ K (λ a → is-finite-eq d))

abstract
  is-finite-im :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (K : is-finite A) →
    has-decidable-equality B → is-finite (im f)
  is-finite-im {f = f} K d =
    is-finite-codomain K
      ( is-surjective-map-unit-im f)
      ( λ x y →
        is-decidable-equiv
          ( extensionality-type-subtype (λ u → trunc-Prop (fib f u)) x y)
          ( d (pr1 x) (pr1 y)))

-- Exercise 16.15

is-inl-Fin : {k : ℕ} → Fin (succ-ℕ k) → UU lzero
is-inl-Fin {k} x = Σ (Fin k) (λ y → Id (inl y) x)

is-star-Fin : {k : ℕ} → Fin (succ-ℕ k) → UU lzero
is-star-Fin x = Id (inr star) x

is-star-is-not-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → ¬ (is-inl-Fin x) → is-star-Fin x
is-star-is-not-inl-Fin (inl x) H = ex-falso (H (pair x refl))
is-star-is-not-inl-Fin (inr star) H = refl

skip-Fin :
  {k : ℕ} → Fin (succ-ℕ k) → Fin k → Fin (succ-ℕ k)
skip-Fin {succ-ℕ k} (inl x) (inl y) = inl (skip-Fin x y)
skip-Fin {succ-ℕ k} (inl x) (inr y) = inr star
skip-Fin {succ-ℕ k} (inr x) y = inl y

abstract
  is-injective-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-injective (skip-Fin x)
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inl y} {inl z} p =
    ap ( inl)
       ( is-injective-skip-Fin x
         ( is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p))
  is-injective-skip-Fin {succ-ℕ k} (inl x) {inr star} {inr star} p = refl
  is-injective-skip-Fin {succ-ℕ k} (inr star) {y} {z} p =
    is-injective-is-emb (is-emb-inl (Fin (succ-ℕ k)) unit) p

abstract
  is-emb-skip-Fin :
    {k : ℕ} (x : Fin (succ-ℕ k)) → is-emb (skip-Fin x)
  is-emb-skip-Fin {k} x =
    is-emb-is-injective
      ( is-set-Fin (succ-ℕ k))
      ( is-injective-skip-Fin x)

emb-skip-Fin : {k : ℕ} (x : Fin (succ-ℕ k)) → Fin k ↪ Fin (succ-ℕ k)
pr1 (emb-skip-Fin x) = skip-Fin x
pr2 (emb-skip-Fin x) = is-emb-skip-Fin x

repeat-Fin :
  {k : ℕ} (x : Fin k) → Fin (succ-ℕ k) → Fin k
repeat-Fin {succ-ℕ k} (inl x) (inl y) = inl (repeat-Fin x y)
repeat-Fin {succ-ℕ k} (inl x) (inr star) = inr star
repeat-Fin {succ-ℕ k} (inr star) (inl y) = y
repeat-Fin {succ-ℕ k} (inr star) (inr star) = inr star

abstract
  is-almost-injective-repeat-Fin :
    {k : ℕ} (x : Fin k) {y z : Fin (succ-ℕ k)} →
    ¬ (Id (inl x) y) → ¬ (Id (inl x) z) →
    Id (repeat-Fin x y) (repeat-Fin x z) → Id y z
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inl z} f g p =
    ap ( inl)
       ( is-almost-injective-repeat-Fin x
         ( λ q → f (ap inl q))
         ( λ q → g (ap inl q))
         ( is-injective-inl p))
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inl y} {inr star} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin {succ-ℕ k} (inl x) {inr star} {inl z} f g p =
    ex-falso (Eq-Fin-eq p)
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inl x) {inr star} {inr star} f g p =
    refl
  is-almost-injective-repeat-Fin {succ-ℕ k} (inr star) {inl y} {inl z} f g p =
    ap inl p
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inl y} {inr star} f g p =
    ex-falso (f (ap inl (inv p)))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inl z} f g p =
    ex-falso (g (ap inl p))
  is-almost-injective-repeat-Fin
    {succ-ℕ k} (inr star) {inr star} {inr star} f g p = refl

is-decidable-is-inl-Fin :
  {k : ℕ} (x : Fin (succ-ℕ k)) → is-decidable (is-inl-Fin x)
is-decidable-is-inl-Fin (inl x) = inl (pair x refl)
is-decidable-is-inl-Fin (inr star) = inr α
  where
  α : is-inl-Fin (inr star) → empty
  α (pair y p) = Eq-Fin-eq p 

cases-map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
  is-decidable (is-inl-Fin (map-emb f (inr star))) → (x : Fin k) →
  is-decidable (is-inl-Fin (map-emb f (inl x))) → Fin l
cases-map-reduce-emb-Fin f (inl (pair t p)) x d = repeat-Fin t (map-emb f (inl x))
cases-map-reduce-emb-Fin f (inr g) x (inl (pair y p)) = y
cases-map-reduce-emb-Fin f (inr g) x (inr h) =
  ex-falso (Eq-Fin-eq (is-injective-emb f ((inv p) ∙ q)))
  where
  p : is-star-Fin (map-emb f (inr star))
  p = is-star-is-not-inl-Fin (map-emb f (inr star)) g
  q : is-star-Fin (map-emb f (inl x))
  q = is-star-is-not-inl-Fin (map-emb f (inl x)) h

map-reduce-emb-Fin :
  {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) → Fin k → Fin l
map-reduce-emb-Fin f x =
  cases-map-reduce-emb-Fin f
    ( is-decidable-is-inl-Fin (map-emb f (inr star)))
    ( x)
    ( is-decidable-is-inl-Fin (map-emb f (inl x)))

abstract
  is-injective-cases-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l))
    (d : is-decidable (is-inl-Fin (map-emb f (inr star))))
    (x : Fin k) (e : is-decidable (is-inl-Fin (map-emb f (inl x))))
    (x' : Fin k) (e' : is-decidable  (is-inl-Fin (map-emb f (inl x')))) →
    Id (cases-map-reduce-emb-Fin f d x e) (cases-map-reduce-emb-Fin f d x' e') →
    Id x x'
  is-injective-cases-map-reduce-emb-Fin f (inl (pair t q)) x e x' e' p =
    is-injective-inl
      ( is-injective-is-emb
        ( is-emb-map-emb f)
        ( is-almost-injective-repeat-Fin t
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( λ α → Eq-Fin-eq (is-injective-emb f ((inv q) ∙ α)))
          ( p)))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inl (pair y' q')) p =
    is-injective-inl (is-injective-emb f ((inv q) ∙ (ap inl p ∙ q')))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inl (pair y q)) x' (inr h) p =
    ex-falso
    ( Eq-Fin-eq
      ( is-injective-emb f
        ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
          ( is-star-is-not-inl-Fin (pr1 f (inl x')) h))))
  is-injective-cases-map-reduce-emb-Fin
    f (inr g) x (inr h) x' (inl (pair y' q')) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))
  is-injective-cases-map-reduce-emb-Fin f (inr g) x (inr h) x' (inr k) p =
    ex-falso
      ( Eq-Fin-eq
        ( is-injective-emb f
          ( ( inv (is-star-is-not-inl-Fin (pr1 f (inr star)) g)) ∙
            ( is-star-is-not-inl-Fin (pr1 f (inl x)) h))))

abstract
  is-injective-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-injective (map-reduce-emb-Fin f)
  is-injective-map-reduce-emb-Fin f {x} {y} =
    is-injective-cases-map-reduce-emb-Fin f
      ( is-decidable-is-inl-Fin (map-emb f (inr star)))
      ( x)
      ( is-decidable-is-inl-Fin (map-emb f (inl x)))
      ( y)
      ( is-decidable-is-inl-Fin (map-emb f (inl y)))

abstract
  is-emb-map-reduce-emb-Fin :
    {k l : ℕ} (f : Fin (succ-ℕ k) ↪ Fin (succ-ℕ l)) →
    is-emb (map-reduce-emb-Fin f)
  is-emb-map-reduce-emb-Fin f =
    is-emb-is-injective (is-set-Fin _) (is-injective-map-reduce-emb-Fin f)

reduce-emb-Fin :
  (k l : ℕ) → Fin (succ-ℕ k) ↪ Fin (succ-ℕ l) → Fin k ↪ Fin l
pr1 (reduce-emb-Fin k l f) = map-reduce-emb-Fin f
pr2 (reduce-emb-Fin k l f) = is-emb-map-reduce-emb-Fin f

-- We now come to the main result

abstract
  leq-emb-Fin :
    {k l : ℕ} → Fin k ↪ Fin l → k ≤-ℕ l
  leq-emb-Fin {zero-ℕ} {zero-ℕ} f = refl-leq-ℕ zero-ℕ
  leq-emb-Fin {succ-ℕ k} {zero-ℕ} f = ex-falso (map-emb f (inr star))
  leq-emb-Fin {zero-ℕ} {succ-ℕ l} f = leq-zero-ℕ (succ-ℕ l)
  leq-emb-Fin {succ-ℕ k} {succ-ℕ l} f = leq-emb-Fin (reduce-emb-Fin k l f)

abstract
  leq-is-emb-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-emb f → k ≤-ℕ l
  leq-is-emb-Fin {f = f} H = leq-emb-Fin (pair f H)

abstract
  leq-is-injective-Fin :
    {k l : ℕ} {f : Fin k → Fin l} → is-injective f → k ≤-ℕ l
  leq-is-injective-Fin H = leq-is-emb-Fin (is-emb-is-injective (is-set-Fin _) H)

abstract
  is-not-emb-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-emb f)
  is-not-emb-le-Fin {k} {l} f p =
    map-neg (leq-is-emb-Fin) (contradiction-le-ℕ l k p)

abstract
  is-not-injective-le-Fin :
    {k l : ℕ} (f : Fin k → Fin l) → le-ℕ l k → ¬ (is-injective f)
  is-not-injective-le-Fin {k} {l} f p =
    map-neg (is-emb-is-injective (is-set-Fin l)) (is-not-emb-le-Fin f p)

abstract
  is-not-injective-map-Fin-succ-Fin :
    {k : ℕ} (f : Fin (succ-ℕ k) → Fin k) → ¬ (is-injective f)
  is-not-injective-map-Fin-succ-Fin {k} f =
    is-not-injective-le-Fin f (le-succ-ℕ {k})

abstract
  no-embedding-ℕ-Fin :
    (k : ℕ) → ¬ (ℕ ↪ Fin k)
  no-embedding-ℕ-Fin k e =
    contradiction-leq-ℕ k k
      ( refl-leq-ℕ k)
      ( leq-emb-Fin (comp-emb e (emb-nat-Fin (succ-ℕ k))))

-- We generalise the main results to types equipped with a counting

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (eA : count A) (eB : count B)
  where

  abstract
    leq-emb-count :
      (A ↪ B) → (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-emb-count f =
      leq-emb-Fin
        ( comp-emb
          ( comp-emb (emb-equiv (inv-equiv-count eB)) f)
          ( emb-equiv (equiv-count eA)))

  abstract
    leq-is-emb-count :
      {f : A → B} → is-emb f → 
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-emb-count {f} H = leq-emb-count (pair f H)

  abstract
    leq-is-injective-count :
      {f : A → B} → is-injective f →
      (number-of-elements-count eA) ≤-ℕ (number-of-elements-count eB)
    leq-is-injective-count H =
      leq-is-emb-count (is-emb-is-injective (is-set-count eB) H)

  abstract
    is-not-emb-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      ¬ (is-emb f)
    is-not-emb-le-count f p H =
      is-not-emb-le-Fin (map-emb h) p (is-emb-map-emb h)
      where
      h : Fin (number-of-elements-count eA) ↪ Fin (number-of-elements-count eB)
      h = comp-emb
            ( emb-equiv (inv-equiv-count eB))
            ( comp-emb (pair f H) (emb-equiv (equiv-count eA)))

  abstract
    is-not-injective-le-count :
      (f : A → B) →
      le-ℕ (number-of-elements-count eB) (number-of-elements-count eA) →
      ¬ (is-injective f)
    is-not-injective-le-count f p H =
      is-not-emb-le-count f p (is-emb-is-injective (is-set-count eB) H)

abstract
  no-embedding-ℕ-count :
    {l : Level} {A : UU l} (e : count A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-count e f =
    no-embedding-ℕ-Fin
      ( number-of-elements-count e)
      ( comp-emb (emb-equiv (inv-equiv-count e)) f)

-- We generalise the main results to finite types

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : is-finite A) (K : is-finite B)
  where

  abstract
    leq-emb-is-finite :
      (A ↪ B) →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-emb-is-finite f =
      apply-universal-property-trunc-Prop H P
        ( λ eA →
          apply-universal-property-trunc-Prop K P
            ( λ eB →
              concatenate-eq-leq-eq-ℕ
                ( inv (compute-number-of-elements-is-finite eA H))
                ( leq-emb-count eA eB f)
                ( compute-number-of-elements-is-finite eB K)))
      where
      P : UU-Prop lzero
      P = leq-ℕ-Prop
            ( number-of-elements-is-finite H)
            ( number-of-elements-is-finite K)

  abstract
    leq-is-emb-is-finite :
      {f : A → B} → is-emb f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-emb-is-finite {f} H =
      leq-emb-is-finite (pair f H)

  abstract
    leq-is-injective-is-finite :
      {f : A → B} → is-injective f →
      (number-of-elements-is-finite H) ≤-ℕ (number-of-elements-is-finite K)
    leq-is-injective-is-finite I =
      leq-is-emb-is-finite (is-emb-is-injective (is-set-is-finite K) I)

  abstract
    is-not-emb-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      ¬ (is-emb f)
    is-not-emb-le-is-finite f p E =
      apply-universal-property-trunc-Prop H empty-Prop
        ( λ e →
          apply-universal-property-trunc-Prop K empty-Prop
            ( λ d → is-not-emb-le-count e d f
              ( concatenate-eq-le-eq-ℕ
                ( compute-number-of-elements-is-finite d K)
                ( p)
                ( inv (compute-number-of-elements-is-finite e H)))
              ( E)))

  abstract
    is-not-injective-le-is-finite :
      (f : A → B) →
      le-ℕ (number-of-elements-is-finite K) (number-of-elements-is-finite H) →
      ¬ (is-injective f)
    is-not-injective-le-is-finite f p I =
      is-not-emb-le-is-finite f p (is-emb-is-injective (is-set-is-finite K) I)

abstract
  no-embedding-ℕ-is-finite :
    {l : Level} {A : UU l} (H : is-finite A) → ¬ (ℕ ↪ A)
  no-embedding-ℕ-is-finite H f =
    apply-universal-property-trunc-Prop H empty-Prop
      ( λ e → no-embedding-ℕ-count e f)
```
