---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.14-propositional-truncation where

open import foundation public
open import elementary-number-theory public

-- Definition 14.3.1

case-paths-induction-principle-propositional-truncation :
  { l : Level} {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  ( B : type-Prop P → UU l) → UU (l ⊔ l2)
case-paths-induction-principle-propositional-truncation P α f B =
  (p q : type-Prop P) (x : B p) (y : B q) → Id (tr B (α p q) x) y
  
induction-principle-propositional-truncation :
  (l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
  UU (lsuc l ⊔ l1 ⊔ l2)
induction-principle-propositional-truncation l {l1} {l2} {A} P α f =
  ( B : type-Prop P → UU l) →
  ( g : (x : A) → (B (f x))) →
  ( β : case-paths-induction-principle-propositional-truncation P α f B) →
  Σ ((p : type-Prop P) → B p) (λ h → (x : A) → Id (h (f x)) (g x))

-- Lemma 14.3.2

abstract
  is-prop-case-paths-induction-principle-propositional-truncation :
    { l : Level} {l1 l2 : Level} {A : UU l1}
    ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
    ( B : type-Prop P → UU l) →
    case-paths-induction-principle-propositional-truncation P α f B →
    ( p : type-Prop P) → is-prop (B p)
  is-prop-case-paths-induction-principle-propositional-truncation P α f B β p =
    is-prop-is-proof-irrelevant (λ x → pair (tr B (α p p) x) (β p p x))
  
  case-paths-induction-principle-propositional-truncation-is-prop :
    { l : Level} {l1 l2 : Level} {A : UU l1}
    ( P : UU-Prop l2) (α : (p q : type-Prop P) → Id p q) (f : A → type-Prop P) →
    ( B : type-Prop P → UU l) →
    ( (p : type-Prop P) → is-prop (B p)) →
    case-paths-induction-principle-propositional-truncation P α f B
  case-paths-induction-principle-propositional-truncation-is-prop
    P α f B is-prop-B p q x y =
    eq-is-prop (is-prop-B q)

--------------------------------------------------------------------------------

-- Section 14.4 Mapping propositional truncations into sets

--------------------------------------------------------------------------------

-- Example 14.4.1

global-choice-decidable-subtype-ℕ :
  {l1 : Level} {P : ℕ → UU l1} (H : (x : ℕ) → is-prop (P x))
  (d : (x : ℕ) → is-decidable (P x)) → global-choice (Σ ℕ P)
global-choice-decidable-subtype-ℕ {l1} {P} H d t =
  tot ( λ x → pr1)
      ( apply-universal-property-trunc-Prop t
        ( minimal-element-ℕ-Prop H)
        ( well-ordering-principle-ℕ P d))

abstract
  is-prop-is-lower-bound-Fin :
    {l : Level} {k : ℕ} {P : Fin k → UU l} (x : Fin k) →
    is-prop (is-lower-bound-Fin P x)
  is-prop-is-lower-bound-Fin x =
    is-prop-Π (λ y → is-prop-function-type (is-prop-leq-Fin x y))

  is-lower-bound-fin-Prop :
    {l : Level} {k : ℕ} (P : Fin k → UU l) (x : Fin k) → UU-Prop l
  pr1 (is-lower-bound-fin-Prop P x) = is-lower-bound-Fin P x
  pr2 (is-lower-bound-fin-Prop P x) = is-prop-is-lower-bound-Fin x

abstract
  all-elements-equal-minimal-element-Fin :
    {l : Level} {k : ℕ} (P : Fin k → UU l) →
    ((x : Fin k) → is-prop (P x)) → all-elements-equal (minimal-element-Fin P)
  all-elements-equal-minimal-element-Fin P H
    (pair x (pair p l)) (pair y (pair q m)) =
    eq-subtype
      ( λ t → prod-Prop (pair _ (H t)) (is-lower-bound-fin-Prop P t))
      ( antisymmetric-leq-Fin (l y q) (m x p))

abstract
  is-prop-minimal-element-Fin :
    {l : Level} {k : ℕ} (P : Fin k → UU l) →
    ((x : Fin k) → is-prop (P x)) → is-prop (minimal-element-Fin P)
  is-prop-minimal-element-Fin P H =
    is-prop-all-elements-equal (all-elements-equal-minimal-element-Fin P H)

minimal-element-Fin-Prop :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → ((x : Fin k) → is-prop (P x)) →
  UU-Prop l
pr1 (minimal-element-Fin-Prop P H) = minimal-element-Fin P
pr2 (minimal-element-Fin-Prop P H) = is-prop-minimal-element-Fin P H

global-choice-decidable-subtype-Fin :
  {l : Level} {k : ℕ} (P : Fin k → UU l) → ((x : Fin k) → is-prop (P x)) →
  ((x : Fin k) → is-decidable (P x)) → global-choice (Σ (Fin k) P)
global-choice-decidable-subtype-Fin {l} {zero-ℕ} P H d t =
  ex-falso (apply-universal-property-trunc-Prop t empty-Prop pr1)
global-choice-decidable-subtype-Fin {l} {succ-ℕ k} P H d t =
  map-Σ P
    ( mod-succ-ℕ k)
    ( λ x → id)
    ( global-choice-total-Q
      ( functor-trunc-Prop
        ( map-Σ Q
          ( nat-Fin)
          ( λ x → tr P (inv (issec-nat-Fin x))))
        ( t)))
  where
  Q : ℕ → UU l
  Q n = P (mod-succ-ℕ k n)
  is-prop-Q : (n : ℕ) → is-prop (Q n)
  is-prop-Q n = H (mod-succ-ℕ k n)
  is-decidable-Q : (n : ℕ) → is-decidable (Q n)
  is-decidable-Q n = d (mod-succ-ℕ k n)
  global-choice-total-Q : global-choice (Σ ℕ Q)
  global-choice-total-Q =
    global-choice-decidable-subtype-ℕ is-prop-Q is-decidable-Q

-- Remark 14.4.2

-- We already defined global-choice above

-- Definition 14.4.3

is-weakly-constant-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-weakly-constant-map {A = A} f = (x y : A) → Id (f x) (f y)

module _
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B)
  where
  
  abstract
    is-prop-is-weakly-constant-map-Set : is-prop (is-weakly-constant-map f)
    is-prop-is-weakly-constant-map-Set =
      is-prop-Π (λ x → is-prop-Π (λ y → is-set-type-Set B (f x) (f y)))
  
  is-weakly-constant-map-set-Prop : UU-Prop (l1 ⊔ l2)
  pr1 is-weakly-constant-map-set-Prop = is-weakly-constant-map f
  pr2 is-weakly-constant-map-set-Prop = is-prop-is-weakly-constant-map-Set

-- Lemma 14.4.4

is-weakly-constant-map-precomp-unit-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (g : type-trunc-Prop A → B) →
  is-weakly-constant-map (g ∘ unit-trunc-Prop)
is-weakly-constant-map-precomp-unit-trunc-Prop g x y =
  ap ( g)
     ( eq-is-prop (is-prop-type-trunc-Prop))

-- Theorem 14.4.5

precomp-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  (type-trunc-Prop A → type-Set B) → Σ (A → type-Set B) is-weakly-constant-map
pr1 (precomp-universal-property-set-quotient-trunc-Prop B g) =
  g ∘ unit-trunc-Prop
pr2 (precomp-universal-property-set-quotient-trunc-Prop B g) =
  is-weakly-constant-map-precomp-unit-trunc-Prop g

abstract
  all-elements-equal-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    all-elements-equal (Σ (type-Set B) (λ b → type-trunc-Prop (fib f b)))
  all-elements-equal-image-is-weakly-constant-map B f H (pair x s) (pair y t) =
    eq-subtype
      ( λ b → trunc-Prop (fib f b))
      ( apply-universal-property-trunc-Prop s
        ( Id-Prop B x y)
        ( λ u →
          apply-universal-property-trunc-Prop t
            ( Id-Prop B x y)
            ( λ v → inv (pr2 u) ∙ (H (pr1 u) (pr1 v) ∙ pr2 v))))

abstract
  is-prop-image-is-weakly-constant-map :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    is-weakly-constant-map f →
    is-prop (Σ (type-Set B) (λ b → type-trunc-Prop (fib f b)))
  is-prop-image-is-weakly-constant-map B f H =
    is-prop-all-elements-equal
      ( all-elements-equal-image-is-weakly-constant-map B f H)

image-weakly-constant-map-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → UU-Prop (l1 ⊔ l2)
pr1 (image-weakly-constant-map-Prop B f H) =
  Σ (type-Set B) (λ b → type-trunc-Prop (fib f b))
pr2 (image-weakly-constant-map-Prop B f H) =
  is-prop-image-is-weakly-constant-map B f H

map-universal-property-set-quotient-trunc-Prop :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
  is-weakly-constant-map f → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop B f H =
  ( pr1) ∘
  ( map-universal-property-trunc-Prop
    ( image-weakly-constant-map-Prop B f H)
    ( λ a → pair (f a) (unit-trunc-Prop (pair a refl))))

map-universal-property-set-quotient-trunc-Prop' :
  {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
  Σ (A → type-Set B) is-weakly-constant-map → type-trunc-Prop A → type-Set B
map-universal-property-set-quotient-trunc-Prop' B (pair f H) =
  map-universal-property-set-quotient-trunc-Prop B f H

abstract
  htpy-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) (f : A → type-Set B) →
    (H : is-weakly-constant-map f) →
    ( map-universal-property-set-quotient-trunc-Prop B f H ∘ unit-trunc-Prop) ~ f
  htpy-universal-property-set-quotient-trunc-Prop B f H a =
    ap ( pr1)
      ( eq-is-prop'
        ( is-prop-image-is-weakly-constant-map B f H)
        ( map-universal-property-trunc-Prop
          ( image-weakly-constant-map-Prop B f H)
          ( λ x → pair (f x) (unit-trunc-Prop (pair x refl)))
          ( unit-trunc-Prop a))
        ( pair (f a) (unit-trunc-Prop (pair a refl))))
  
  issec-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
    ( ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B) ∘
      ( map-universal-property-set-quotient-trunc-Prop' B)) ~ id
  issec-map-universal-property-set-quotient-trunc-Prop B (pair f H) =
    eq-subtype
      ( is-weakly-constant-map-set-Prop B)
      ( eq-htpy (htpy-universal-property-set-quotient-trunc-Prop B f H))

  isretr-map-universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
    ( ( map-universal-property-set-quotient-trunc-Prop' B) ∘
      ( precomp-universal-property-set-quotient-trunc-Prop {A = A} B)) ~ id
  isretr-map-universal-property-set-quotient-trunc-Prop B g =
    eq-htpy
      ( ind-trunc-Prop
        ( λ x →
          Id-Prop B
            ( map-universal-property-set-quotient-trunc-Prop' B
              ( precomp-universal-property-set-quotient-trunc-Prop B g)
              ( x))
            ( g x))
        ( λ x →
          htpy-universal-property-set-quotient-trunc-Prop B
            ( g ∘ unit-trunc-Prop)
            ( is-weakly-constant-map-precomp-unit-trunc-Prop g)
            ( x)))
  
  universal-property-set-quotient-trunc-Prop :
    {l1 l2 : Level} {A : UU l1} (B : UU-Set l2) →
    is-equiv (precomp-universal-property-set-quotient-trunc-Prop {A = A} B)
  universal-property-set-quotient-trunc-Prop {A = A} B =
    is-equiv-has-inverse
      ( map-universal-property-set-quotient-trunc-Prop' B)
      ( issec-map-universal-property-set-quotient-trunc-Prop B)
      ( isretr-map-universal-property-set-quotient-trunc-Prop B)

--------------------------------------------------------------------------------

-- Exercises

--------------------------------------------------------------------------------

-- Exercise 14.1

-- Exercise 14.1 (a)

abstract
  map-trunc-trunc-Prop :
    {l : Level} (A : UU l) →
    type-trunc-Prop (type-trunc-Prop A) → type-trunc-Prop A
  map-trunc-trunc-Prop A = map-universal-property-trunc-Prop (trunc-Prop A) id

abstract
  is-equiv-map-trunc-trunc-Prop :
    {l : Level} (A : UU l) → is-equiv (map-trunc-trunc-Prop A)
  is-equiv-map-trunc-trunc-Prop A =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( unit-trunc-Prop)

abstract
  is-equiv-unit-trunc-trunc-Prop :
    {l : Level} (A : UU l) → is-equiv (unit-trunc-Prop {A = type-trunc-Prop A})
  is-equiv-unit-trunc-trunc-Prop A =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-trunc-trunc-Prop A)

-- Exercise 14.1 (b)

is-inhabited-or-empty : {l1 : Level} → UU l1 → UU l1
is-inhabited-or-empty A = coprod (type-trunc-Prop A) (is-empty A)

abstract
  is-prop-is-inhabited-or-empty :
    {l1 : Level} (A : UU l1) → is-prop (is-inhabited-or-empty A)
  is-prop-is-inhabited-or-empty A =
    is-prop-coprod
      ( λ t → apply-universal-property-trunc-Prop t empty-Prop)
      ( is-prop-type-trunc-Prop)
      ( is-prop-neg)

is-inhabited-or-empty-Prop : {l1 : Level} → UU l1 → UU-Prop l1
pr1 (is-inhabited-or-empty-Prop A) = is-inhabited-or-empty A
pr2 (is-inhabited-or-empty-Prop A) = is-prop-is-inhabited-or-empty A

abstract
  is-prop-is-decidable :
    {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
  is-prop-is-decidable is-prop-A =
    is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)

is-merely-decidable-Prop :
  {l : Level} → UU l → UU-Prop l
is-merely-decidable-Prop A = trunc-Prop (is-decidable A)

is-merely-decidable : {l : Level} → UU l → UU l
is-merely-decidable A = type-trunc-Prop (is-decidable A)

abstract
  is-prop-is-decidable-type-trunc-Prop :
    {l : Level} (A : UU l) → is-prop (is-decidable (type-trunc-Prop A))
  is-prop-is-decidable-type-trunc-Prop A =
    is-prop-is-decidable is-prop-type-trunc-Prop

is-decidable-type-trunc-Prop : {l : Level} → UU l → UU-Prop l
pr1 (is-decidable-type-trunc-Prop A) = is-decidable (type-trunc-Prop A)
pr2 (is-decidable-type-trunc-Prop A) = is-prop-is-decidable-type-trunc-Prop A

is-decidable-type-trunc-Prop-is-merely-decidable :
  {l : Level} (A : UU l) →
  is-merely-decidable A → is-decidable (type-trunc-Prop A)
is-decidable-type-trunc-Prop-is-merely-decidable A =
  map-universal-property-trunc-Prop
    ( is-decidable-type-trunc-Prop A)
    ( f)
  where
  f : is-decidable A → type-Prop (is-decidable-type-trunc-Prop A)
  f (inl a) = inl (unit-trunc-Prop a)
  f (inr f) = inr (map-universal-property-trunc-Prop empty-Prop f)

is-merely-decidable-is-decidable-type-trunc-Prop :
  {l : Level} (A : UU l) →
  is-decidable (type-trunc-Prop A) → is-merely-decidable A
is-merely-decidable-is-decidable-type-trunc-Prop A (inl x) =
   apply-universal-property-trunc-Prop x
     ( is-merely-decidable-Prop A)
     ( unit-trunc-Prop ∘ inl)
is-merely-decidable-is-decidable-type-trunc-Prop A (inr f) =
  unit-trunc-Prop (inr (f ∘ unit-trunc-Prop))

-- Exercise 14.1 (c)

elim-trunc-Prop-is-decidable :
  {l : Level} {A : UU l} → is-decidable A → type-trunc-Prop A → A
elim-trunc-Prop-is-decidable (inl a) x = a
elim-trunc-Prop-is-decidable (inr f) x =
  ex-falso (apply-universal-property-trunc-Prop x empty-Prop f)

-- Exercise 14.1 (d) 

abstract
  dn-dn-type-trunc-Prop :
    {l : Level} (A : UU l) → ¬¬ (type-trunc-Prop A) → ¬¬ A
  dn-dn-type-trunc-Prop A =
    dn-extend (map-universal-property-trunc-Prop (dn-Prop' A) intro-dn)

abstract
  dn-type-trunc-Prop-dn :
    {l : Level} {A : UU l} → ¬¬ A → ¬¬ (type-trunc-Prop A)
  dn-type-trunc-Prop-dn = map-dn unit-trunc-Prop

-- Exercise 14.2

abstract
  is-nonempty-is-inhabited :
    {l : Level} {X : UU l} → type-trunc-Prop X → ¬¬ X
  is-nonempty-is-inhabited {l} {X} =
    map-universal-property-trunc-Prop (dn-Prop' X) intro-dn

is-fixed-point-is-decidable-is-inhabited :
  {l : Level} {X : UU l} → type-trunc-Prop X → is-decidable X ≃ X
is-fixed-point-is-decidable-is-inhabited {l} {X} t =
  right-unit-law-coprod-is-empty X (¬ X) (is-nonempty-is-inhabited t)

-- Exercise 14.3

mere-eq-Prop :
  {l : Level} {A : UU l} → A → A → UU-Prop l
mere-eq-Prop x y = trunc-Prop (Id x y)

mere-eq : {l : Level} {A : UU l} → A → A → UU l
mere-eq x y = type-trunc-Prop (Id x y)

abstract
  refl-mere-eq :
    {l : Level} {A : UU l} {x : A} → mere-eq x x
  refl-mere-eq = unit-trunc-Prop refl

abstract
  symm-mere-eq :
    {l : Level} {A : UU l} {x y : A} → mere-eq x y → mere-eq y x
  symm-mere-eq {x = x} {y} =
    functor-trunc-Prop inv

abstract
  trans-mere-eq :
    {l : Level} {A : UU l} {x y z : A} →
    mere-eq x y → mere-eq y z → mere-eq x z
  trans-mere-eq {x = x} {y} {z} p q =
    apply-universal-property-trunc-Prop p
      ( mere-eq-Prop x z)
      ( λ p' → functor-trunc-Prop (λ q' → p' ∙ q') q)

-- Exercise 14.4

abstract
  is-propositional-truncation-prod :
    {l1 l2 l3 l4 : Level}
    {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P)
    {A' : UU l3} (P' : UU-Prop l4) (f' : A' → type-Prop P') →
    ({l : Level} → is-propositional-truncation l P f) →
    ({l : Level} → is-propositional-truncation l P' f') →
    {l : Level} → is-propositional-truncation l (prod-Prop P P') (map-prod f f')
  is-propositional-truncation-prod P f P' f' is-ptr-f is-ptr-f' Q =
    is-equiv-top-is-equiv-bottom-square
      ( ev-pair)
      ( ev-pair)
      ( precomp (map-prod f f') (type-Prop Q))
      ( λ h a a' → h (f a) (f' a'))
      ( refl-htpy)
      ( is-equiv-ev-pair)
      ( is-equiv-ev-pair)
      ( is-equiv-comp'
        ( λ h a a' → h a (f' a'))
        ( λ h a p' → h (f a) p')
        ( is-ptr-f (pair (type-hom-Prop P' Q) (is-prop-type-hom-Prop P' Q)))
        ( is-equiv-map-Π
          ( λ a g a' → g (f' a'))
          ( λ a → is-ptr-f' Q)))

equiv-prod-trunc-Prop :
  {l1 l2 : Level} (A : UU l1) (A' : UU l2) →
  type-equiv-Prop
    ( trunc-Prop (A × A'))
    ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
equiv-prod-trunc-Prop A A' =
  pr1
    ( center
      ( is-uniquely-unique-propositional-truncation
        ( trunc-Prop (A × A'))
        ( prod-Prop (trunc-Prop A) (trunc-Prop A'))
        ( unit-trunc-Prop)
        ( map-prod unit-trunc-Prop unit-trunc-Prop)
        ( is-propositional-truncation-trunc-Prop (A × A'))
        ( is-propositional-truncation-prod
          ( trunc-Prop A)
          ( unit-trunc-Prop)
          ( trunc-Prop A')
          ( unit-trunc-Prop)
          ( is-propositional-truncation-trunc-Prop A)
          ( is-propositional-truncation-trunc-Prop A'))))

map-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) → type-trunc-Prop A × type-trunc-Prop B
map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
  map-universal-property-trunc-Prop
    ( pair
      ( type-trunc-Prop A × type-trunc-Prop B)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop))
    ( map-prod unit-trunc-Prop unit-trunc-Prop)

map-inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop A × type-trunc-Prop B → type-trunc-Prop (A × B)
map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} t =
  map-universal-property-trunc-Prop
    ( trunc-Prop (A × B))
    ( λ x →
      map-universal-property-trunc-Prop
        ( trunc-Prop (A × B))
        ( unit-trunc-Prop ∘ (pair x))
        ( pr2 t))
    ( pr1 t)

abstract
  is-equiv-map-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-type-trunc-Prop)
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( map-inv-distributive-trunc-prod-Prop)

distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-trunc-Prop (A × B) ≃ (type-trunc-Prop A × type-trunc-Prop B)
pr1 distributive-trunc-prod-Prop = map-distributive-trunc-prod-Prop
pr2 distributive-trunc-prod-Prop = is-equiv-map-distributive-trunc-prod-Prop

abstract
  is-equiv-map-inv-distributive-trunc-prod-Prop :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-equiv (map-inv-distributive-trunc-prod-Prop {A = A} {B = B})
  is-equiv-map-inv-distributive-trunc-prod-Prop {l1} {l2} {A} {B} =
    is-equiv-is-prop
      ( is-prop-prod is-prop-type-trunc-Prop is-prop-type-trunc-Prop)
      ( is-prop-type-trunc-Prop)
      ( map-distributive-trunc-prod-Prop)

inv-distributive-trunc-prod-Prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ( type-trunc-Prop A × type-trunc-Prop B) ≃ type-trunc-Prop (A × B)
pr1 inv-distributive-trunc-prod-Prop = map-inv-distributive-trunc-prod-Prop
pr2 inv-distributive-trunc-prod-Prop =
  is-equiv-map-inv-distributive-trunc-prod-Prop

-- Exercise 14.5

-- Exercise 14.5 (a)

abstract
  is-propositional-truncation-has-section :
    {l l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    (g : type-Prop P → A) → is-propositional-truncation l P f
  is-propositional-truncation-has-section {A = A} P f g Q =
    is-equiv-is-prop
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( is-prop-function-type (is-prop-type-Prop Q))
      ( λ h → h ∘ g)

abstract
  is-propositional-truncation-terminal-map :
    { l l1 : Level} (A : UU l1) (a : A) →
    is-propositional-truncation l unit-Prop (terminal-map {A = A})
  is-propositional-truncation-terminal-map A a =
    is-propositional-truncation-has-section
      ( unit-Prop)
      ( terminal-map)
      ( ind-unit a)

-- Exercise 14.5 (b)

abstract
  is-propositional-truncation-is-equiv :
    {l l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
    {f : type-hom-Prop P Q} →
    is-equiv f → is-propositional-truncation l Q f
  is-propositional-truncation-is-equiv P Q {f} is-equiv-f R =
    is-equiv-precomp-is-equiv f is-equiv-f (type-Prop R)

abstract
  is-propositional-truncation-map-equiv :
    { l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
    (e : type-equiv-Prop P Q) →
    ( l : Level) → is-propositional-truncation l Q (map-equiv e)
  is-propositional-truncation-map-equiv P Q e l R =
    is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) (type-Prop R)

abstract
  is-equiv-is-propositional-truncation :
    {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) {f : type-hom-Prop P Q} →
    ({l : Level} → is-propositional-truncation l Q f) → is-equiv f
  is-equiv-is-propositional-truncation P Q {f} H =
    is-equiv-is-equiv-precomp-Prop P Q f H

abstract
  is-propositional-truncation-id :
    { l1 : Level} (P : UU-Prop l1) →
    ( l : Level) → is-propositional-truncation l P id
  is-propositional-truncation-id P l Q = is-equiv-id

-- Exercise 14.6

-- Definition 14.1.9

dependent-universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  ( P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
dependent-universal-property-propositional-truncation l {l1} {l2} {A} P f =
  ( Q : type-Prop P → UU-Prop l) → is-equiv (precomp-Π f (type-Prop ∘ Q))

-- Theorem 14.2.2

abstract
  dependent-universal-property-is-propositional-truncation :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} → is-propositional-truncation l P f) →
    ( {l : Level} → dependent-universal-property-propositional-truncation l P f)
  dependent-universal-property-is-propositional-truncation
    {l1} {l2} {A} P f is-ptr-f Q =
    is-fiberwise-equiv-is-equiv-map-Σ
      ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
      ( precomp f (type-Prop P))
      ( λ h → precomp-Π f (λ p → type-Prop (Q (h p))))
      ( is-ptr-f P)
      ( is-equiv-top-is-equiv-bottom-square
        ( map-inv-distributive-Π-Σ
          { C = λ (x : type-Prop P) (p : type-Prop P) → type-Prop (Q p)})
        ( map-inv-distributive-Π-Σ
          { C = λ (x : A) (p : type-Prop P) → type-Prop (Q p)})
        ( map-Σ
          ( λ (g : A → type-Prop P) → (x : A) → type-Prop (Q (g x)))
          ( precomp f (type-Prop P))
          ( λ h → precomp-Π f (λ p → type-Prop (Q (h p)))))
        ( precomp f (Σ (type-Prop P) (λ p → type-Prop (Q p))))
        ( ind-Σ (λ h h' → refl))
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-equiv-map-inv-distributive-Π-Σ)
        ( is-ptr-f (Σ-Prop P Q)))
      ( id {A = type-Prop P})

abstract
  dependent-universal-property-trunc-Prop :
    {l1 : Level} {A : UU l1} {l : Level} →
      dependent-universal-property-propositional-truncation l
      ( trunc-Prop A)
      ( unit-trunc-Prop)
  dependent-universal-property-trunc-Prop {A = A} =
    dependent-universal-property-is-propositional-truncation
      ( trunc-Prop A)
      ( unit-trunc-Prop)
      ( is-propositional-truncation-trunc-Prop A)

module _
  {l1 l2 : Level} {A : UU l1} (P : type-trunc-Prop A → UU-Prop l2)
  where
  
  equiv-dependent-universal-property-trunc-Prop :
    ((y : type-trunc-Prop A) → type-Prop (P y)) ≃
    ((x : A) → type-Prop (P (unit-trunc-Prop x)))
  pr1 equiv-dependent-universal-property-trunc-Prop =
    precomp-Π unit-trunc-Prop (type-Prop ∘ P)
  pr2 equiv-dependent-universal-property-trunc-Prop =
    dependent-universal-property-trunc-Prop P

  apply-dependent-universal-property-trunc-Prop :
    (y : type-trunc-Prop A) → ((x : A) → type-Prop (P (unit-trunc-Prop x))) →
    type-Prop (P y)
  apply-dependent-universal-property-trunc-Prop y f =
    map-inv-equiv equiv-dependent-universal-property-trunc-Prop f y    

abstract
  is-propositional-truncation-dependent-universal-property :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ( {l : Level} →
      dependent-universal-property-propositional-truncation l P f) →
    ( {l : Level} → is-propositional-truncation l P f)
  is-propositional-truncation-dependent-universal-property P f dup-f Q =
    dup-f (λ p → Q)

-- Exercise 14.7

-- The impredicative encoding of the propositional truncation --

impredicative-trunc-Prop :
  {l : Level} → UU l → UU-Prop (lsuc l)
impredicative-trunc-Prop {l} A =
  Π-Prop
    ( UU-Prop l)
    ( λ Q → function-Prop (A → type-Prop Q) Q)

type-impredicative-trunc-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-trunc-Prop {l} A =
  type-Prop (impredicative-trunc-Prop A)

map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A → type-impredicative-trunc-Prop A
map-impredicative-trunc-Prop {l} A =
  map-universal-property-trunc-Prop
    ( impredicative-trunc-Prop A)
    ( λ x Q f → f x)

inv-map-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-trunc-Prop A → type-trunc-Prop A
inv-map-impredicative-trunc-Prop A H =
  H (trunc-Prop A) unit-trunc-Prop

equiv-impredicative-trunc-Prop :
  {l : Level} (A : UU l) →
  type-trunc-Prop A ≃ type-impredicative-trunc-Prop A
equiv-impredicative-trunc-Prop A =
  equiv-iff
    ( trunc-Prop A)
    ( impredicative-trunc-Prop A)
    ( map-impredicative-trunc-Prop A)
    ( inv-map-impredicative-trunc-Prop A)

-- The impredicative encoding of conjunction --

impredicative-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-conj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q → function-Prop (type-Prop P1 → (type-Prop P2 → type-Prop Q)) Q)

type-impredicative-conj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-conj-Prop P1 P2 =
  type-Prop (impredicative-conj-Prop P1 P2)

map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-conj-Prop P1 P2 → type-impredicative-conj-Prop P1 P2
map-impredicative-conj-Prop {l1} {l2} P1 P2 (pair p1 p2) Q f =
  f p1 p2

inv-map-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-impredicative-conj-Prop P1 P2 → type-conj-Prop P1 P2
inv-map-impredicative-conj-Prop P1 P2 H =
  H (conj-Prop P1 P2) (λ p1 p2 → pair p1 p2)

equiv-impredicative-conj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-conj-Prop P1 P2 ≃ type-impredicative-conj-Prop P1 P2
equiv-impredicative-conj-Prop P1 P2 =
  equiv-iff
    ( conj-Prop P1 P2)
    ( impredicative-conj-Prop P1 P2)
    ( map-impredicative-conj-Prop P1 P2)
    ( inv-map-impredicative-conj-Prop P1 P2)

-- The impredicative encoding of disjunction --

impredicative-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-disj-Prop {l1} {l2} P1 P2 =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q →
      function-Prop
        ( type-implication-Prop P1 Q)
        ( function-Prop (type-implication-Prop P2 Q) Q))

type-impredicative-disj-Prop :
  {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU (lsuc (l1 ⊔ l2))
type-impredicative-disj-Prop P1 P2 =
  type-Prop (impredicative-disj-Prop P1 P2)

map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-disj-Prop P1 P2 → type-impredicative-disj-Prop P1 P2
map-impredicative-disj-Prop {l1} {l2} P1 P2 =
  map-universal-property-trunc-Prop
    ( impredicative-disj-Prop P1 P2)
    ( ind-coprod
      ( λ x → type-impredicative-disj-Prop P1 P2)
      ( λ x Q f1 f2 → f1 x)
      ( λ y Q f1 f2 → f2 y))
  
inv-map-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-impredicative-disj-Prop P1 P2 → type-disj-Prop P1 P2
inv-map-impredicative-disj-Prop P1 P2 H =
  H (disj-Prop P1 P2) (inl-disj-Prop P1 P2) (inr-disj-Prop P1 P2)

equiv-impredicative-disj-Prop :
  {l1 l2 : Level} (P1 : UU-Prop l1) (P2 : UU-Prop l2) →
  type-disj-Prop P1 P2 ≃ type-impredicative-disj-Prop P1 P2
equiv-impredicative-disj-Prop P1 P2 =
  equiv-iff
    ( disj-Prop P1 P2)
    ( impredicative-disj-Prop P1 P2)
    ( map-impredicative-disj-Prop P1 P2)
    ( inv-map-impredicative-disj-Prop P1 P2)

-- The impredicative encoding of negation --

impredicative-neg-Prop :
  {l : Level} → UU l → UU-Prop (lsuc l)
impredicative-neg-Prop {l} A =
  Π-Prop (UU-Prop l) (λ Q → function-Prop A Q)

type-impredicative-neg-Prop :
  {l : Level} → UU l → UU (lsuc l)
type-impredicative-neg-Prop A =
  type-Prop (impredicative-neg-Prop A)

map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A → type-impredicative-neg-Prop A
map-impredicative-neg-Prop A f Q a = ex-falso (f a)

inv-map-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  type-impredicative-neg-Prop A → ¬ A
inv-map-impredicative-neg-Prop A H a = H (neg-Prop' A) a a

equiv-impredicative-neg-Prop :
  {l : Level} (A : UU l) →
  ¬ A ≃ type-impredicative-neg-Prop A
equiv-impredicative-neg-Prop A =
  equiv-iff
    ( neg-Prop' A)
    ( impredicative-neg-Prop A)
    ( map-impredicative-neg-Prop A)
    ( inv-map-impredicative-neg-Prop A)

-- The impredicative encoding of existential quantification --

impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU-Prop (lsuc (l1 ⊔ l2))
impredicative-exists-Prop {l1} {l2} {A} P =
  Π-Prop
    ( UU-Prop (l1 ⊔ l2))
    ( λ Q → function-Prop ((x : A) → type-Prop (P x) → type-Prop Q) Q)

type-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (lsuc (l1 ⊔ l2))
type-impredicative-exists-Prop P =
  type-Prop (impredicative-exists-Prop P)

map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  exists P → type-impredicative-exists-Prop P
map-impredicative-exists-Prop {l1} {l2} {A} P =
  map-universal-property-trunc-Prop
    ( impredicative-exists-Prop P)
    ( ind-Σ (λ x y Q h → h x y))

inv-map-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  type-impredicative-exists-Prop P → exists P
inv-map-impredicative-exists-Prop {A = A} P H =
  H ( exists-Prop P)
    ( λ x y → unit-trunc-Prop (pair x y))

equiv-impredicative-exists-Prop :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) →
  exists P ≃ type-impredicative-exists-Prop P
equiv-impredicative-exists-Prop P =
  equiv-iff
    ( exists-Prop P)
    ( impredicative-exists-Prop P)
    ( map-impredicative-exists-Prop P)
    ( inv-map-impredicative-exists-Prop P)

-- The impredicative encoding of the based identity type of a set --

impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) → UU-Prop (lsuc l)
impredicative-based-id-Prop {l} A a x =
  Π-Prop (type-Set A → UU-Prop l) (λ Q → hom-Prop (Q a) (Q x))

type-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) → UU (lsuc l)
type-impredicative-based-id-Prop A a x =
  type-Prop (impredicative-based-id-Prop A a x)

map-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  Id a x → type-impredicative-based-id-Prop A a x
map-impredicative-based-id-Prop A a .a refl Q p = p

inv-map-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  type-impredicative-based-id-Prop A a x → Id a x
inv-map-impredicative-based-id-Prop A a x H =
  H (λ x → pair (Id a x) (is-set-type-Set A a x)) refl

equiv-impredicative-based-id-Prop :
  {l : Level} (A : UU-Set l) (a x : type-Set A) →
  Id a x ≃ type-impredicative-based-id-Prop A a x
equiv-impredicative-based-id-Prop A a x =
  equiv-iff
    ( pair (Id a x) (is-set-type-Set A a x))
    ( impredicative-based-id-Prop A a x)
    ( map-impredicative-based-id-Prop A a x)
    ( inv-map-impredicative-based-id-Prop A a x)

-- The impredicative encoding of Martin-Löf's identity type of a set --

impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) → UU-Prop (lsuc l)
impredicative-id-Prop {l} A x y =
  Π-Prop (type-Set A → type-Set A → UU-Prop l)
    (λ Q → function-Prop ((a : type-Set A) → type-Prop (Q a a)) (Q x y))

type-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) → UU (lsuc l)
type-impredicative-id-Prop A x y =
  type-Prop (impredicative-id-Prop A x y)

map-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) →
  Id x y → type-impredicative-id-Prop A x y
map-impredicative-id-Prop A x .x refl Q r = r x

inv-map-impredicative-id-Prop :
  {l : Level} (A : UU-Set l ) (x y : type-Set A) →
  type-impredicative-id-Prop A x y → Id x y
inv-map-impredicative-id-Prop A x y H =
  H (λ a b → pair (Id a b) (is-set-type-Set A a b)) (λ a → refl)

equiv-impredicative-id-Prop :
  {l : Level} (A : UU-Set l) (x y : type-Set A) →
  Id x y ≃ type-impredicative-id-Prop A x y
equiv-impredicative-id-Prop A x y =
  equiv-iff
    ( pair (Id x y) (is-set-type-Set A x y))
    ( impredicative-id-Prop A x y)
    ( map-impredicative-id-Prop A x y)
    ( inv-map-impredicative-id-Prop A x y)

-- Exercise 14.8

--------------------------------------------------------------------------------

postulate 𝕀 : UU lzero

postulate source-𝕀 : 𝕀

postulate target-𝕀 : 𝕀

postulate path-𝕀 : Id source-𝕀 target-𝕀

postulate ind-𝕀 : {l : Level} (P : 𝕀 → UU l) (u : P source-𝕀) (v : P target-𝕀) (q : Id (tr P path-𝕀 u) v) → (x : 𝕀) → P x

postulate comp-source-𝕀 : {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀) (q : Id (tr P path-𝕀 u) v) → Id (ind-𝕀 P u v q source-𝕀) u

postulate comp-target-𝕀 : {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀) (q : Id (tr P path-𝕀 u) v) → Id (ind-𝕀 P u v q target-𝕀) v

postulate comp-path-𝕀 : {l : Level} {P : 𝕀 → UU l} (u : P source-𝕀) (v : P target-𝕀) (q : Id (tr P path-𝕀 u) v) → Id (apd (ind-𝕀 P u v q) path-𝕀 ∙ comp-target-𝕀 u v q) (ap (tr P path-𝕀) (comp-source-𝕀 u v q) ∙ q)

Data-𝕀 : {l : Level} → (𝕀 → UU l) → UU l
Data-𝕀 P = Σ (P source-𝕀) (λ u → Σ (P target-𝕀) (λ v → Id (tr P path-𝕀 u) v))

ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → ((x : 𝕀) → P x) → Data-𝕀 P
ev-𝕀 f = triple (f source-𝕀) (f target-𝕀) (apd f path-𝕀)

Eq-Data-𝕀 : {l : Level} {P : 𝕀 → UU l} (x y : Data-𝕀 P) → UU l
Eq-Data-𝕀 {l} {P} x y =
  Σ ( Id (pr1 x) (pr1 y)) (λ α →
     Σ ( Id (pr1 (pr2 x)) (pr1 (pr2 y))) (λ β →
       Id ( pr2 (pr2 x) ∙ β) ( (ap (tr P path-𝕀) α) ∙ pr2 (pr2 y))))

refl-Eq-Data-𝕀 : {l : Level} {P : 𝕀 → UU l} (x : Data-𝕀 P) → Eq-Data-𝕀 x x
refl-Eq-Data-𝕀 x = triple refl refl right-unit

Eq-eq-Data-𝕀 :
  {l : Level} {P : 𝕀 → UU l} {x y : Data-𝕀 P} → Id x y → Eq-Data-𝕀 x y
Eq-eq-Data-𝕀 {x = x} refl = refl-Eq-Data-𝕀 x

abstract
  is-contr-total-Eq-Data-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (x : Data-𝕀 P) →
    is-contr (Σ (Data-𝕀 P) (Eq-Data-𝕀 x))
  is-contr-total-Eq-Data-𝕀 {l} {P} x =
    is-contr-total-Eq-structure
      ( λ u vq α →
        Σ ( Id (pr1 (pr2 x)) (pr1 vq))
          ( λ β → Id (pr2 (pr2 x) ∙ β) (ap (tr P path-𝕀) α ∙ pr2 vq)))
      ( is-contr-total-path (pr1 x))
      ( pair (pr1 x) refl)
      ( is-contr-total-Eq-structure
        ( λ v q β → Id (pr2 (pr2 x) ∙ β) q)
        ( is-contr-total-path (pr1 (pr2 x)))
        ( pair (pr1 (pr2 x)) refl)
        ( is-contr-total-path (pr2 (pr2 x) ∙ refl)))

abstract
  is-equiv-Eq-eq-Data-𝕀 :
    {l : Level} {P : 𝕀 → UU l} (x y : Data-𝕀 P) →
    is-equiv (Eq-eq-Data-𝕀 {x = x} {y})
  is-equiv-Eq-eq-Data-𝕀 x =
    fundamental-theorem-id x
      ( refl-Eq-Data-𝕀 x)
      ( is-contr-total-Eq-Data-𝕀 x)
      ( λ y → Eq-eq-Data-𝕀 {_} {_} {x} {y})

eq-Eq-Data-𝕀' :
  {l : Level} {P : 𝕀 → UU l} {x y : Data-𝕀 P} → Eq-Data-𝕀 x y → Id x y
eq-Eq-Data-𝕀' {l} {P} {x} {y} = map-inv-is-equiv (is-equiv-Eq-eq-Data-𝕀 x y)

eq-Eq-Data-𝕀 :
  {l : Level} {P : 𝕀 → UU l} {x y : Data-𝕀 P} (α : Id (pr1 x) (pr1 y))
  (β : Id (pr1 (pr2 x)) (pr1 (pr2 y)))
  (γ : Id (pr2 (pr2 x) ∙ β) (ap (tr P path-𝕀) α ∙ pr2 (pr2 y))) →
  Id x y
eq-Eq-Data-𝕀 α β γ = eq-Eq-Data-𝕀' (triple α β γ)

inv-ev-𝕀 : {l : Level} {P : 𝕀 → UU l} → Data-𝕀 P → (x : 𝕀) → P x
inv-ev-𝕀 x = ind-𝕀 _ (pr1 x) (pr1 (pr2 x)) (pr2 (pr2 x))

issec-inv-ev-𝕀 : {l : Level} {P : 𝕀 → UU l} (x : Data-𝕀 P) →
  Id (ev-𝕀 (inv-ev-𝕀 x)) x
issec-inv-ev-𝕀 (pair u (pair v q)) =
  eq-Eq-Data-𝕀
    ( comp-source-𝕀 u v q)
    ( comp-target-𝕀 u v q)
    ( comp-path-𝕀 u v q)

tr-value :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f g : (x : A) → B x) {x y : A}
  (p : Id x y) (q : Id (f x) (g x)) (r : Id (f y) (g y)) →
  Id (apd f p ∙ r) (ap (tr B p) q ∙ apd g p) → Id (tr (λ x → Id (f x) (g x)) p q) r
tr-value f g refl q r s = (inv (ap-id q) ∙ inv right-unit) ∙ inv s

isretr-inv-ev-𝕀 :
  {l : Level} {P : 𝕀 → UU l} (f : (x : 𝕀) → P x) → Id (inv-ev-𝕀 (ev-𝕀 f)) f
isretr-inv-ev-𝕀 {l} {P} f =
  eq-htpy
    ( ind-𝕀
      ( λ x → Id (inv-ev-𝕀 (ev-𝕀 f) x) (f x))
      ( comp-source-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
      ( comp-target-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
      ( tr-value (inv-ev-𝕀 (ev-𝕀 f)) f path-𝕀
        ( comp-source-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
        ( comp-target-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))
        ( comp-path-𝕀 (f source-𝕀) (f target-𝕀) (apd f path-𝕀))))

abstract
  is-equiv-ev-𝕀 :
    {l : Level} (P : 𝕀 → UU l) → is-equiv (ev-𝕀 {P = P})
  is-equiv-ev-𝕀 P =
    is-equiv-has-inverse inv-ev-𝕀 issec-inv-ev-𝕀 isretr-inv-ev-𝕀

tr-eq : {l : Level} {A : UU l} {x y : A} (p : Id x y) → Id (tr (Id x) p refl) p
tr-eq refl = refl

contraction-𝕀 : (x : 𝕀) → Id source-𝕀 x
contraction-𝕀 =
  ind-𝕀
    ( Id source-𝕀)
    ( refl)
    ( path-𝕀)
    ( tr-eq path-𝕀)

abstract
  is-contr-𝕀 : is-contr 𝕀
  pr1 is-contr-𝕀 = source-𝕀
  pr2 is-contr-𝕀 = contraction-𝕀

-----------

abstract
  is-empty-type-trunc-Prop :
    {l1 : Level} {X : UU l1} → is-empty X → is-empty (type-trunc-Prop X)
  is-empty-type-trunc-Prop f =
    map-universal-property-trunc-Prop empty-Prop f

abstract
  is-empty-type-trunc-Prop' :
    {l1 : Level} {X : UU l1} → is-empty (type-trunc-Prop X) → is-empty X
  is-empty-type-trunc-Prop' f = f ∘ unit-trunc-Prop

abstract
  elim-trunc-decidable-fam-Fin :
    {l1 : Level} {k : ℕ} {B : Fin k → UU l1} →
    ((x : Fin k) → is-decidable (B x)) →
    type-trunc-Prop (Σ (Fin k) B) → Σ (Fin k) B
  elim-trunc-decidable-fam-Fin {l1} {zero-ℕ} {B} d y =
    ex-falso (is-empty-type-trunc-Prop pr1 y)
  elim-trunc-decidable-fam-Fin {l1} {succ-ℕ k} {B} d y
    with d (inr star)
  ... | inl x = pair (inr star) x
  ... | inr f =
    map-Σ-map-base inl B
      ( elim-trunc-decidable-fam-Fin {l1} {k} {B ∘ inl}
        ( λ x → d (inl x))
        ( map-equiv-trunc-Prop
          ( ( ( right-unit-law-coprod-is-empty
                ( Σ (Fin k) (B ∘ inl))
                ( B (inr star)) f) ∘e
              ( equiv-coprod id-equiv (left-unit-law-Σ (B ∘ inr)))) ∘e
            ( right-distributive-Σ-coprod (Fin k) unit B))
          ( y)))
```
