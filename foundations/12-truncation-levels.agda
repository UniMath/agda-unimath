{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.12-truncation-levels where

open import foundations.11-fundamental-theorem public

--------------------------------------------------------------------------------

-- Section 12 Propositions, Sets, and general truncation levels

--------------------------------------------------------------------------------

-- Section 12.1 Propositions

{- Definition 12.1.1 -}

is-prop :
  {i : Level} (A : UU i) → UU i
is-prop A = (x y : A) → is-contr (Id x y)

UU-Prop :
  (l : Level) → UU (lsuc l)
UU-Prop l = Σ (UU l) is-prop

type-Prop :
  {l : Level} → UU-Prop l → UU l
type-Prop P = pr1 P

is-prop-type-Prop :
  {l : Level} (P : UU-Prop l) → is-prop (type-Prop P)
is-prop-type-Prop P = pr2 P

{- Example 12.1.2 -}

abstract
  is-prop-unit : is-prop unit
  is-prop-unit = is-prop-is-contr is-contr-unit

unit-Prop : UU-Prop lzero
unit-Prop = pair unit is-prop-unit

is-prop-empty : is-prop empty
is-prop-empty ()

empty-Prop : UU-Prop lzero
empty-Prop = pair empty is-prop-empty

is-prop-leq-Fin :
  {k : ℕ} (x y : Fin k) → is-prop (leq-Fin x y)
is-prop-leq-Fin {succ-ℕ k} (inl x) (inl y) = is-prop-leq-Fin x y
is-prop-leq-Fin {succ-ℕ k} (inl x) (inr star) = is-prop-unit
is-prop-leq-Fin {succ-ℕ k} (inr star) (inl y) = is-prop-empty
is-prop-leq-Fin {succ-ℕ k} (inr star) (inr star) = is-prop-unit

{- Proposition 12.1.3 -}

all-elements-equal :
  {i : Level} (A : UU i) → UU i
all-elements-equal A = (x y : A) → Id x y

is-proof-irrelevant :
  {l1 : Level} → UU l1 → UU l1
is-proof-irrelevant A = A → is-contr A

is-subterminal :
  {l1 : Level} → UU l1 → UU l1
is-subterminal A = is-emb (terminal-map {A = A})

abstract
  is-prop-all-elements-equal :
    {i : Level} {A : UU i} → all-elements-equal A → is-prop A
  is-prop-all-elements-equal {i} {A} H x y =
    pair
      ( (inv (H x x)) ∙ (H x y))
      ( λ { refl → left-inv (H x x)})

abstract
  eq-is-prop' :
    {i : Level} {A : UU i} → is-prop A → all-elements-equal A
  eq-is-prop' H x y = pr1 (H x y)

abstract
  eq-is-prop :
    {i : Level} {A : UU i} → is-prop A → {x y : A} → Id x y
  eq-is-prop H {x} {y} = eq-is-prop' H x y

abstract
  is-proof-irrelevant-all-elements-equal :
    {l1 : Level} {A : UU l1} → all-elements-equal A → is-proof-irrelevant A
  is-proof-irrelevant-all-elements-equal H a = pair a (H a)

abstract
  is-proof-irrelevant-is-prop :
    {i : Level} {A : UU i} → is-prop A → is-proof-irrelevant A
  is-proof-irrelevant-is-prop =
    is-proof-irrelevant-all-elements-equal ∘ eq-is-prop'

abstract
  is-prop-is-proof-irrelevant :
    {i : Level} {A : UU i} → is-proof-irrelevant A → is-prop A
  is-prop-is-proof-irrelevant H x y = is-prop-is-contr (H x) x y

abstract
  eq-is-proof-irrelevant :
    {l1 : Level} {A : UU l1} → is-proof-irrelevant A → all-elements-equal A
  eq-is-proof-irrelevant H =
    eq-is-prop' (is-prop-is-proof-irrelevant H)

is-emb-is-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (A → is-emb f) → is-emb f
is-emb-is-emb H x y = H x x y

abstract
  is-subterminal-is-proof-irrelevant :
    {l1 : Level} {A : UU l1} → is-proof-irrelevant A → is-subterminal A
  is-subterminal-is-proof-irrelevant H =
    is-emb-is-emb
      ( λ x → is-emb-is-equiv (is-equiv-is-contr _ (H x) is-contr-unit))

abstract
  is-subterminal-all-elements-equal :
    {l1 : Level} {A : UU l1} → all-elements-equal A → is-subterminal A
  is-subterminal-all-elements-equal =
    is-subterminal-is-proof-irrelevant ∘ is-proof-irrelevant-all-elements-equal

abstract
  is-subterminal-is-prop :
    {l1 : Level} {A : UU l1} → is-prop A → is-subterminal A
  is-subterminal-is-prop =
    is-subterminal-all-elements-equal ∘ eq-is-prop'

abstract
  is-prop-is-subterminal :
    {l1 : Level} {A : UU l1} → is-subterminal A → is-prop A
  is-prop-is-subterminal {l1} {A} H x y =
    is-contr-is-equiv
      ( Id star star)
      ( ap terminal-map)
      ( H x y)
      ( is-prop-is-contr is-contr-unit star star)

abstract
  eq-is-subterminal :
    {l1 : Level} {A : UU l1} → is-subterminal A → all-elements-equal A
  eq-is-subterminal = eq-is-prop' ∘ is-prop-is-subterminal

abstract
  is-proof-irrelevant-is-subterminal :
    {l1 : Level} {A : UU l1} → is-subterminal A → is-proof-irrelevant A
  is-proof-irrelevant-is-subterminal H =
    is-proof-irrelevant-all-elements-equal (eq-is-subterminal H)

{- Proposition 12.1.4 -}

abstract
  is-equiv-is-prop : {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A →
    is-prop B → {f : A → B} → (B → A) → is-equiv f
  is-equiv-is-prop is-prop-A is-prop-B {f} g =
    is-equiv-has-inverse
      ( g)
      ( λ y → center (is-prop-B (f (g y)) y))
      ( λ x → center (is-prop-A (g (f x)) x))

equiv-prop :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-prop A → is-prop B →
  (A → B) → (B → A) → A ≃ B
equiv-prop is-prop-A is-prop-B f g =
  pair f (is-equiv-is-prop is-prop-A is-prop-B g)

--------------------------------------------------------------------------------

-- Section 12.2 Subtypes

{- Definition 12.2.1 -}

is-subtype : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-subtype B = (x : _) → is-prop (B x)

is-property : {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → UU (l1 ⊔ l2)
is-property B = is-subtype B

is-prop-map : {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-prop-map f = (b : _) → is-prop (fib f b)

total-subtype :
  {l1 l2 : Level} {A : UU l1} (P : A → UU-Prop l2) → UU (l1 ⊔ l2)
total-subtype {A = A} P = Σ A (λ x → pr1 (P x))

{- Lemma 12.2.2 -}

abstract
  is-prop-is-equiv :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) (f : A → B) (E : is-equiv f) →
    is-prop B → is-prop A
  is-prop-is-equiv B f E H x y =
    is-contr-is-equiv _ (ap f {x} {y}) (is-emb-is-equiv E x y) (H (f x) (f y))

is-prop-equiv :
  {l1 l2 : Level} {A : UU l1} (B : UU l2) (e : A ≃ B) → is-prop B → is-prop A
is-prop-equiv B (pair f is-equiv-f) = is-prop-is-equiv B f is-equiv-f

abstract
  is-prop-is-equiv' :
    {l1 l2 : Level} (A : UU l1) {B : UU l2} (f : A → B) (E : is-equiv f) →
    is-prop A → is-prop B
  is-prop-is-equiv' A f E H =
    is-prop-is-equiv _ (map-inv-is-equiv E) (is-equiv-map-inv-is-equiv E) H

is-prop-equiv' :
  {l1 l2 : Level} (A : UU l1) {B : UU l2} (e : A ≃ B) → is-prop A → is-prop B
is-prop-equiv' A (pair f is-equiv-f) = is-prop-is-equiv' A f is-equiv-f

{- Theorem 12.2.3 -}

abstract
  is-emb-is-prop-map :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-prop-map f → is-emb f
  is-emb-is-prop-map {f = f} is-prop-map-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
      ( λ y → ap f)

abstract
  is-prop-map-is-emb :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-emb f → is-prop-map f
  is-prop-map-is-emb {f = f} is-emb-f y =
    is-prop-is-proof-irrelevant α
    where
    α : (t : fib f y) → is-contr (fib f y)
    α (pair x refl) =
      fundamental-theorem-id' x refl
        ( λ y → inv ∘ ap f)
        ( λ y →
          is-equiv-comp' inv (ap f)
            ( is-emb-f x y)
            ( is-equiv-inv (f x) (f y)))

is-prop-map-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : B ↪ A) → is-prop-map (map-emb f)
is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

fib-emb-Prop :
  {i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → B → UU-Prop (i ⊔ j)
fib-emb-Prop f y =
  pair ( fib (map-emb f) y)
       ( is-prop-map-is-emb (is-emb-map-emb f) y)

abstract
  is-emb-pr1 :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-subtype B → is-emb (pr1 {B = B})
  is-emb-pr1 {B = B} H =
    is-emb-is-prop-map (λ x → is-prop-equiv (B x) (equiv-fib-pr1 x) (H x))

equiv-ap-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
  is-subtype B → {s t : Σ A B} → Id s t ≃ Id (pr1 s) (pr1 t)
equiv-ap-pr1 is-subtype-B {s} {t} =
  pair (ap pr1) (is-emb-pr1 is-subtype-B s t)

abstract
  is-subtype-is-emb-pr1 : {i j : Level} {A : UU i} {B : A → UU j} →
    is-emb (pr1 {B = B}) → is-subtype B
  is-subtype-is-emb-pr1 H x =
    is-prop-equiv' (fib pr1 x) (equiv-fib-pr1 x) (is-prop-map-is-emb H x)

{- Remark 12.2.5 -}

equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) ≃ Σ (Σ A C) (λ t → B (pr1 t))
equiv-double-structure {A = A} B C =
  ( ( inv-assoc-Σ A C (λ t → B (pr1 t))) ∘e
    ( equiv-tot (λ x → commutative-prod))) ∘e
  ( assoc-Σ A B (λ t → C (pr1 t)))

map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  Σ (Σ A B) (λ t → C (pr1 t)) → Σ (Σ A C) (λ t → B (pr1 t))
map-equiv-double-structure B C = map-equiv (equiv-double-structure B C)

is-equiv-map-equiv-double-structure :
  {l1 l2 l3 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3) →
  is-equiv (map-equiv-double-structure B C)
is-equiv-map-equiv-double-structure B C =
  is-equiv-map-equiv (equiv-double-structure B C)

{- The following is a general construction that will help us show that
   the identity type of a subtype agrees with the identity type of the 
   original type. We already know that the first projection of a family of
   propositions is an embedding, but the following lemma still has its uses. -}

abstract
  is-contr-total-Eq-substructure :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {P : A → UU l3} →
    is-contr (Σ A B) → (is-subtype P) → (a : A) (b : B a) (p : P a) →
    is-contr (Σ (Σ A P) (λ t → B (pr1 t)))
  is-contr-total-Eq-substructure {A = A} {B} {P}
    is-contr-AB is-subtype-P a b p =
    is-contr-equiv
      ( Σ (Σ A B) (λ t → P (pr1 t)))
      ( equiv-double-structure P B)
      ( is-contr-equiv
        ( P a)
        ( left-unit-law-Σ-is-contr
          ( is-contr-AB)
          ( pair a b))
        ( is-proof-irrelevant-is-prop (is-subtype-P a) p))

Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-subtype B →
  (Σ A B) → (Σ A B) → UU l1
Eq-total-subtype is-subtype-B p p' = Id (pr1 p) (pr1 p') 

reflexive-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → Eq-total-subtype is-subtype-B p p
reflexive-Eq-total-subtype is-subtype-B (pair x y) = refl

Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → Id p p' → Eq-total-subtype is-subtype-B p p'
Eq-total-subtype-eq is-subtype-B p .p refl =
  reflexive-Eq-total-subtype is-subtype-B p

is-contr-total-Eq-total-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p : Σ A B) → is-contr (Σ (Σ A B) (Eq-total-subtype is-subtype-B p))
is-contr-total-Eq-total-subtype is-subtype-B (pair x y) =
  is-contr-total-Eq-substructure
    ( is-contr-total-path x)
    ( is-subtype-B)
    x refl y

is-equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → is-equiv (Eq-total-subtype-eq is-subtype-B p p')
is-equiv-Eq-total-subtype-eq is-subtype-B p =
  fundamental-theorem-id p
    ( reflexive-Eq-total-subtype is-subtype-B p)
    ( is-contr-total-Eq-total-subtype is-subtype-B p)
    ( Eq-total-subtype-eq is-subtype-B p)

equiv-Eq-total-subtype-eq :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  (p p' : Σ A B) → (Id p p') ≃ (Eq-total-subtype is-subtype-B p p')
equiv-Eq-total-subtype-eq is-subtype-B p p' =
  pair
    ( Eq-total-subtype-eq is-subtype-B p p')
    ( is-equiv-Eq-total-subtype-eq is-subtype-B p p')

eq-subtype :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (is-subtype-B : is-subtype B) →
  {p p' : Σ A B} → Eq-total-subtype is-subtype-B p p' → Id p p'
eq-subtype is-subtype-B {p} {p'} =
  map-inv-is-equiv (is-equiv-Eq-total-subtype-eq is-subtype-B p p')

--------------------------------------------------------------------------------

-- Section 12.3 Sets

is-set :
  {i : Level} → UU i → UU i
is-set A = (x y : A) → is-prop (Id x y)

UU-Set :
  (i : Level) → UU (lsuc i)
UU-Set i = Σ (UU i) is-set

type-Set :
  {l : Level} → UU-Set l → UU l
type-Set X = pr1 X

is-set-type-Set :
  {l : Level} (X : UU-Set l) → is-set (type-Set X)
is-set-type-Set X = pr2 X

Id-Prop :
  {l : Level} (X : UU-Set l) (x y : type-Set X) → UU-Prop l
Id-Prop X x y = pair (Id x y) (is-set-type-Set X x y)

axiom-K :
  {i : Level} → UU i → UU i
axiom-K A = (x : A) (p : Id x x) → Id refl p

abstract
  is-set-axiom-K' :
    {l1 : Level} {A : UU l1} → axiom-K A → (x y : A) → all-elements-equal (Id x y)
  is-set-axiom-K' K x .x refl q with K x q
  ... | refl = refl

abstract
  is-set-axiom-K :
    {i : Level} {A : UU i} → axiom-K A → is-set A
  is-set-axiom-K H x y = is-prop-all-elements-equal (is-set-axiom-K' H x y) 

abstract
  axiom-K-is-set :
    {i : Level} (A : UU i) → is-set A → axiom-K A
  axiom-K-is-set A H x p =
    ( inv (contraction (is-proof-irrelevant-is-prop (H x x) refl) refl)) ∙ 
    ( contraction (is-proof-irrelevant-is-prop (H x x) refl) p)

abstract
  is-equiv-prop-in-id :
    {i j : Level} {A : UU i}
    (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    (x y : A) → is-equiv (i x y)
  is-equiv-prop-in-id R p ρ i x =
    fundamental-theorem-id-retr x (i x)
      (λ y → pair
        (ind-Id x (λ z p → R x z) (ρ x) y)
        ((λ r → eq-is-prop (p x y))))

abstract
  is-set-prop-in-id :
    {i j : Level} {A : UU i} (R : A → A → UU j)
    (p : (x y : A) → is-prop (R x y))
    (ρ : (x : A) → R x x)
    (i : (x y : A) → R x y → Id x y) →
    is-set A
  is-set-prop-in-id R p ρ i x y =
    is-prop-is-equiv'
      ( R x y)
      ( i x y)
      ( is-equiv-prop-in-id R p ρ i x y) (p x y)

abstract
  is-prop-Eq-ℕ :
    (n m : ℕ) → is-prop (Eq-ℕ n m)
  is-prop-Eq-ℕ zero-ℕ zero-ℕ = is-prop-unit
  is-prop-Eq-ℕ zero-ℕ (succ-ℕ m) = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) zero-ℕ = is-prop-empty
  is-prop-Eq-ℕ (succ-ℕ n) (succ-ℕ m) = is-prop-Eq-ℕ n m

abstract
  is-set-ℕ : is-set ℕ
  is-set-ℕ =
    is-set-prop-in-id
      Eq-ℕ
      is-prop-Eq-ℕ
      refl-Eq-ℕ
      eq-Eq-ℕ

ℕ-Set : UU-Set lzero
ℕ-Set = pair ℕ is-set-ℕ

{- Next, we show that types with decidable equality are sets. To see this, we 
   will construct a fiberwise equivalence with the binary relation R that is
   defined by R x y := unit if (x = y), and empty otherwise. In order to define
   this relation, we first define a type family over ((x = y) + ¬(x = y)) that 
   returns unit on the left and empty on the right. -}
   
Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) → is-decidable (Id x y) → UU lzero
Eq-has-decidable-equality' x y (inl p) = unit
Eq-has-decidable-equality' x y (inr f) = empty

Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) → A → A → UU lzero
Eq-has-decidable-equality d x y = Eq-has-decidable-equality' x y (d x y)

is-prop-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  is-prop (Eq-has-decidable-equality' x y t)
is-prop-Eq-has-decidable-equality' x y (inl p) = is-prop-unit
is-prop-Eq-has-decidable-equality' x y (inr f) = is-prop-empty

is-prop-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A)
  {x y : A} → is-prop (Eq-has-decidable-equality d x y)
is-prop-Eq-has-decidable-equality d {x} {y} =
  is-prop-Eq-has-decidable-equality' x y (d x y)

reflexive-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) (x : A) →
  Eq-has-decidable-equality d x x 
reflexive-Eq-has-decidable-equality d x with d x x
... | inl α = star
... | inr f = f refl

Eq-has-decidable-equality-eq :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Id x y → Eq-has-decidable-equality d x y
Eq-has-decidable-equality-eq {l} {A} d {x} {.x} refl =
  reflexive-Eq-has-decidable-equality d x

eq-Eq-has-decidable-equality' :
  {l : Level} {A : UU l} (x y : A) (t : is-decidable (Id x y)) →
  Eq-has-decidable-equality' x y t → Id x y
eq-Eq-has-decidable-equality' x y (inl p) t = p
eq-Eq-has-decidable-equality' x y (inr f) t = ex-falso t

eq-Eq-has-decidable-equality :
  {l : Level} {A : UU l} (d : has-decidable-equality A) {x y : A} →
  Eq-has-decidable-equality d x y → Id x y
eq-Eq-has-decidable-equality d {x} {y} =
  eq-Eq-has-decidable-equality' x y (d x y)

is-set-has-decidable-equality :
  {l : Level} {A : UU l} → has-decidable-equality A → is-set A
is-set-has-decidable-equality d =
  is-set-prop-in-id
    ( λ x y → Eq-has-decidable-equality d x y)
    ( λ x y → is-prop-Eq-has-decidable-equality d)
    ( λ x → reflexive-Eq-has-decidable-equality d x)
    ( λ x y → eq-Eq-has-decidable-equality d)

{- We also prove a unary version of Hedberg's theorem -}

Eq-unary-Hedberg' :
  {l : Level} {A : UU l} {x y : A} → is-decidable (Id x y) → UU lzero
Eq-unary-Hedberg' (inl p) = unit 
Eq-unary-Hedberg' (inr f) = empty

Eq-unary-Hedberg :
  {l : Level} {A : UU l} {x : A} (d : (y : A) → is-decidable (Id x y)) →
  A → UU lzero
Eq-unary-Hedberg d y = Eq-unary-Hedberg' (d y)

is-prop-Eq-unary-Hedberg' :
  {l : Level} {A : UU l} {x y : A} (d : is-decidable (Id x y)) →
  is-prop (Eq-unary-Hedberg' d)
is-prop-Eq-unary-Hedberg' (inl p) = is-prop-unit
is-prop-Eq-unary-Hedberg' (inr f) = is-prop-empty

is-prop-Eq-unary-Hedberg :
  {l : Level} {A : UU l} {x : A} (d : (y : A) → is-decidable (Id x y)) →
  (y : A) → is-prop (Eq-unary-Hedberg d y)
is-prop-Eq-unary-Hedberg d y = is-prop-Eq-unary-Hedberg' (d y)

refl-Eq-unary-Hedberg :
  {l : Level} {A : UU l} {x : A} (d : (y : A) → is-decidable (Id x y)) →
  Eq-unary-Hedberg d x
refl-Eq-unary-Hedberg {x = x} d with (d x)
... | inl p = star
... | inr f = f refl

{-
contraction-total-Eq-unary-Hedberg' :
  {l : Level} {A : UU l} {x : A} (d : (y : A) → is-decidable (Id x y)) →
  (t : Σ A (Eq-unary-Hedberg d)) →
  (u : is-decidable (Id x (pr1 t))) (v : Id (d (pr1 t)) u) →
  Id (pair x (refl-Eq-unary-Hedberg d)) t
contraction-total-Eq-unary-Hedberg' {l} {A} {x} d (pair y t) (inl x₁) v =
  eq-pair-Σ {!map-inv-is-equiv (is-emb-inl (Id x y) (¬ (Id x y)) ? ?!} {!!}
contraction-total-Eq-unary-Hedberg' {l} {A} {x} d (pair y t) (inr x₁) v = {!!}

is-contr-total-Eq-unary-Hedberg :
  {l : Level} {A : UU l} {x : A} (d : (y : A) → is-decidable (Id x y)) →
  is-contr (Σ A (Eq-unary-Hedberg d))
is-contr-total-Eq-unary-Hedberg {l} {A} {x} d =
  pair
    ( pair x (refl-Eq-unary-Hedberg d))
    {! α!}
-}

--------------------------------------------------------------------------------

-- Section 12.3 General truncation levels

data 𝕋 : UU lzero where
  neg-two-𝕋 : 𝕋
  succ-𝕋 : 𝕋 → 𝕋

neg-one-𝕋 : 𝕋
neg-one-𝕋 = succ-𝕋 (neg-two-𝕋)

zero-𝕋 : 𝕋
zero-𝕋 = succ-𝕋 (neg-one-𝕋)

one-𝕋 : 𝕋
one-𝕋 = succ-𝕋 (zero-𝕋)

truncation-level-ℕ : ℕ → 𝕋
truncation-level-ℕ zero-ℕ = zero-𝕋
truncation-level-ℕ (succ-ℕ k) = succ-𝕋 (truncation-level-ℕ k)

truncation-level-minus-one-ℕ : ℕ → 𝕋
truncation-level-minus-one-ℕ zero-ℕ = neg-one-𝕋
truncation-level-minus-one-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-one-ℕ k)

truncation-level-minus-two-ℕ : ℕ → 𝕋
truncation-level-minus-two-ℕ zero-ℕ = neg-two-𝕋
truncation-level-minus-two-ℕ (succ-ℕ k) =
  succ-𝕋 (truncation-level-minus-two-ℕ k)

-- Probably it is better to define this where we first need it.
add-𝕋 : 𝕋 → 𝕋 → 𝕋
add-𝕋 neg-two-𝕋 neg-two-𝕋 = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 neg-two-𝕋) = neg-two-𝕋
add-𝕋 neg-two-𝕋 (succ-𝕋 (succ-𝕋 y)) = y
add-𝕋 (succ-𝕋 neg-two-𝕋) neg-two-𝕋 = neg-two-𝕋
add-𝕋 (succ-𝕋 neg-two-𝕋) (succ-𝕋 y) = y
add-𝕋 (succ-𝕋 (succ-𝕋 neg-two-𝕋)) y = y
add-𝕋 (succ-𝕋 (succ-𝕋 (succ-𝕋 x))) y = succ-𝕋 (add-𝕋 (succ-𝕋 (succ-𝕋 x)) y)

-- Definition 12.4.1

-- Truncated types

is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)

-- Truncated maps

is-trunc-map :
  {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} → (A → B) → UU (i ⊔ j)
is-trunc-map k f = (y : _) → is-trunc k (fib f y)

trunc-map : {i j : Level} (k : 𝕋) (A : UU i) (B : UU j) → UU (i ⊔ j)
trunc-map k A B = Σ (A → B) (is-trunc-map k)


-- We introduce some notation for the special case of 1-types --

is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

UU-1-Type : (l : Level) → UU (lsuc l)
UU-1-Type l = Σ (UU l) is-1-type

type-1-Type :
  {l : Level} → UU-1-Type l → UU l
type-1-Type = pr1

is-1-type-type-1-Type :
  {l : Level} (A : UU-1-Type l) → is-1-type (type-1-Type A)
is-1-type-type-1-Type = pr2

-- We introduce some notation for the special case of 2-types --

is-2-type : {l : Level} → UU l → UU l
is-2-type = is-trunc (succ-𝕋 one-𝕋)

UU-2-Type : (l : Level) → UU (lsuc l)
UU-2-Type l = Σ (UU l) is-2-type

type-2-Type :
  {l : Level} → UU-2-Type l → UU l
type-2-Type = pr1

is-2-type-type-2-Type :
  {l : Level} (A : UU-2-Type l) → is-2-type (type-2-Type A)
is-2-type-type-2-Type = pr2

-- We introduce some notation for the universe of k-truncated types --

UU-Truncated-Type : 𝕋 → (l : Level) → UU (lsuc l)
UU-Truncated-Type k l = Σ (UU l) (is-trunc k)

type-Truncated-Type :
  {k : 𝕋} {l : Level} → UU-Truncated-Type k l → UU l
type-Truncated-Type = pr1

is-trunc-type-Truncated-Type :
  {k : 𝕋} {l : Level} (A : UU-Truncated-Type k l) →
  is-trunc k (type-Truncated-Type A)
is-trunc-type-Truncated-Type = pr2

{- Remark 12.4.2

We can't formalise this remark in Agda, because universes are handled 
differently. -}

-- Proposition 12.4.3

-- We show that if a type is k-truncated, then it is (k+1)-truncated. --

abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : UU i} →
    is-trunc k A → is-trunc (succ-𝕋 k) A
  is-trunc-succ-is-trunc neg-two-𝕋 H =
    is-prop-is-contr H
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y =
    is-trunc-succ-is-trunc k (H x y)

is-set-is-prop :
  {l : Level} {P : UU l} → is-prop P → is-set P
is-set-is-prop = is-trunc-succ-is-trunc neg-one-𝕋

abstract
  is-trunc-map-succ-is-trunc-map :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f : A → B) → is-trunc-map k f → is-trunc-map (succ-𝕋 k) f
  is-trunc-map-succ-is-trunc-map k f is-trunc-f b =
    is-trunc-succ-is-trunc k (is-trunc-f b)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type k l → UU-Truncated-Type (succ-𝕋 k) l
truncated-type-succ-Truncated-Type k A =
  pair
    ( type-Truncated-Type A)
    ( is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A))

set-Prop :
  {l : Level} → UU-Prop l → UU-Set l
set-Prop P = truncated-type-succ-Truncated-Type neg-one-𝕋 P

1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A

-- We conclude that a contractible type is k-truncated for any k

is-trunc-is-contr :
  { l : Level} (k : 𝕋) {A : UU l} → is-contr A → is-trunc k A
is-trunc-is-contr neg-two-𝕋 is-contr-A = is-contr-A
is-trunc-is-contr (succ-𝕋 k) is-contr-A =
  is-trunc-succ-is-trunc k (is-trunc-is-contr k is-contr-A)

is-set-is-contr :
  {l : Level} {A : UU l} → is-contr A → is-set A
is-set-is-contr = is-trunc-is-contr zero-𝕋

-- We also conclude that a proposition is (k+1)-truncated for any k

is-trunc-is-prop :
  { l : Level} (k : 𝕋) {A : UU l} → is-prop A → is-trunc (succ-𝕋 k) A
is-trunc-is-prop k is-prop-A x y = is-trunc-is-contr k (is-prop-A x y)

abstract
  is-trunc-succ-empty : (k : 𝕋) → is-trunc (succ-𝕋 k) empty
  is-trunc-succ-empty k = ind-empty

is-trunc-is-empty :
  {l : Level} (k : 𝕋) {A : UU l} → is-empty A → is-trunc (succ-𝕋 k) A
is-trunc-is-empty k f = is-trunc-is-prop k (λ x → ex-falso (f x))

-- Corollary 12.4.4

abstract
  is-trunc-Id : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id neg-two-𝕋 is-trunc-A = is-prop-is-contr is-trunc-A
  is-trunc-Id (succ-𝕋 k) is-trunc-A x y =
    is-trunc-succ-is-trunc k {A = Id x y} (is-trunc-A x y)

-- Proposition 12.4.5

-- We show that k-truncated types are closed under equivalences --

abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv neg-two-𝕋 B f is-equiv-f H =
    is-contr-is-equiv B f is-equiv-f H
  is-trunc-is-equiv (succ-𝕋 k) B f is-equiv-f H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y})
      ( is-emb-is-equiv is-equiv-f x y) (H (f x) (f y))

abstract
  is-set-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-set B → is-set A
  is-set-is-equiv = is-trunc-is-equiv zero-𝕋

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-set-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) →
    is-set B → is-set A
  is-set-equiv = is-trunc-equiv zero-𝕋

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-set-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) → is-equiv f →
    is-set A → is-set B
  is-set-is-equiv' = is-trunc-is-equiv' zero-𝕋

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

abstract
  is-set-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) →
    is-set A → is-set B
  is-set-equiv' = is-trunc-equiv' zero-𝕋

-- Corollary 12.4.6

-- We show that if A embeds into a (k+1)-type B, then A is a (k+1)-type. --

abstract
  is-trunc-is-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j}
    (f : A → B) → is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb : {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} →
    (f : A ↪ B) → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)

-- Proposition 12.4.7

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-trunc-map-is-trunc-ap :
      ((x y : A) → is-trunc-map k (ap f {x} {y})) → is-trunc-map (succ-𝕋 k) f
    is-trunc-map-is-trunc-ap is-trunc-ap-f b (pair x p) (pair x' p') =
      is-trunc-is-equiv k
        ( fib (ap f) (p ∙ (inv p')))
        ( fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-equiv-fib-ap-eq-fib f (pair x p) (pair x' p'))
        ( is-trunc-ap-f x x' (p ∙ (inv p')))

  abstract
    is-trunc-ap-is-trunc-map :
      is-trunc-map (succ-𝕋 k) f → (x y : A) → is-trunc-map k (ap f {x} {y})
    is-trunc-ap-is-trunc-map is-trunc-map-f x y p =
      is-trunc-is-equiv' k
        ( Id (pair x p) (pair y refl))
        ( eq-fib-fib-ap f x y p)
        ( is-equiv-eq-fib-fib-ap f x y p)
        ( is-trunc-map-f (f y) (pair x p) (pair y refl))

-- 

abstract
  is-trunc-pr1-is-trunc-fam :
    {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    ((x : A) → is-trunc k (B x)) → is-trunc-map k (pr1 {i} {j} {A} {B})
  is-trunc-pr1-is-trunc-fam k B H x =
    is-trunc-equiv k (B x) (equiv-fib-pr1 x) (H x)

trunc-pr1 :
  {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU-Truncated-Type k j) →
  trunc-map k (Σ A (λ x → pr1 (B x))) A
trunc-pr1 k B =
  pair pr1 (is-trunc-pr1-is-trunc-fam k (λ x → pr1 (B x)) (λ x → pr2 (B x)))

abstract
  is-trunc-fam-is-trunc-pr1 : {i j : Level} (k : 𝕋) {A : UU i} (B : A → UU j) →
    is-trunc-map k (pr1 {i} {j} {A} {B}) → ((x : A) → is-trunc k (B x))
  is-trunc-fam-is-trunc-pr1 k B is-trunc-pr1 x =
    is-trunc-equiv k (fib pr1 x) (inv-equiv-fib-pr1 B x) (is-trunc-pr1 x)
    
abstract
  is-trunc-succ-subtype :
    {i j : Level} (k : 𝕋) {A : UU i} {P : A → UU j} →
    ((x : A) → is-prop (P x)) →
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (Σ A P)
  is-trunc-succ-subtype k H is-trunc-A =
    is-trunc-is-emb k pr1 (is-emb-pr1 H) is-trunc-A

abstract
  is-prop-subtype :
    {i j : Level} {A : UU i} {P : A → UU j} →
    ((x : A) → is-prop (P x)) → is-prop A → is-prop (Σ A P)
  is-prop-subtype = is-trunc-succ-subtype neg-two-𝕋

abstract
  is-set-subtype :
    {i j : Level} {A : UU i} {P : A → UU j} →
    ((x : A) → is-prop (P x)) → is-set A → is-set (Σ A P)
  is-set-subtype = is-trunc-succ-subtype neg-one-𝕋

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 12.1

abstract
  is-prop-Eq-𝟚 : (x y : bool) → is-prop (Eq-𝟚 x y)
  is-prop-Eq-𝟚 true true = is-prop-unit
  is-prop-Eq-𝟚 true false = is-prop-empty
  is-prop-Eq-𝟚 false true = is-prop-empty
  is-prop-Eq-𝟚 false false = is-prop-unit

abstract
  is-set-bool : is-set bool
  is-set-bool = is-set-prop-in-id Eq-𝟚 is-prop-Eq-𝟚 reflexive-Eq-𝟚 (λ x y → eq-Eq-𝟚)

set-bool : UU-Set lzero
set-bool = pair bool is-set-bool

-- Exercise 12.2

-- Exercise 12.2 (a)

abstract
  is-emb-is-injective' : {l1 l2 : Level} {A : UU l1} (is-set-A : is-set A)
    {B : UU l2} (is-set-B : is-set B) (f : A → B) →
    is-injective f → is-emb f
  is-emb-is-injective' is-set-A is-set-B f is-injective-f x y =
    is-equiv-is-prop
      ( is-set-A x y)
      ( is-set-B (f x) (f y))
      ( is-injective-f)

  is-set-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-set A
  is-set-is-injective {f = f} H I =
    is-set-prop-in-id
      ( λ x y → Id (f x) (f y))
      ( λ x y → H (f x) (f y))
      ( λ x → refl)
      ( λ x y → I)

  is-emb-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-emb f
  is-emb-is-injective {f = f} H I =
    is-emb-is-injective' (is-set-is-injective H I) H f I

  is-prop-map-is-injective :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
    is-set B → is-injective f → is-prop-map f
  is-prop-map-is-injective {f = f} H I =
    is-prop-map-is-emb (is-emb-is-injective H I)

-- Exercise 12.2 (b)

is-emb-add-ℕ : (x : ℕ) → is-emb (add-ℕ x)
is-emb-add-ℕ x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ x)

is-emb-add-ℕ' : (x : ℕ) → is-emb (add-ℕ' x)
is-emb-add-ℕ' x = is-emb-is-injective is-set-ℕ (is-injective-add-ℕ' x)

-- Exercise 12.2 (c)

is-emb-mul-ℕ : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ x)
is-emb-mul-ℕ x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ x H)

is-emb-mul-ℕ' : (x : ℕ) → is-nonzero-ℕ x → is-emb (mul-ℕ' x)
is-emb-mul-ℕ' x H = is-emb-is-injective is-set-ℕ (is-injective-mul-ℕ' x H)

-- We conclude that some maps, that were known to be injective, are embeddings
                                                                    
is-emb-nat-Fin : {k : ℕ} → is-emb (nat-Fin {k})
is-emb-nat-Fin {k} = is-emb-is-injective is-set-ℕ is-injective-nat-Fin

emb-nat-Fin : (k : ℕ) → Fin k ↪ ℕ
emb-nat-Fin k = pair nat-Fin is-emb-nat-Fin

-- Exercise 12.3

-- Exercise 12.3 (a)

is-not-contractible-coprod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-contr A → is-contr B →
  ¬ (is-contr (coprod A B))
is-not-contractible-coprod-is-contr {l1} {l2} {A} {B} HA HB HAB =
  map-inv-raise
    ( Eq-eq-coprod A B (inl (center HA)) (inr (center HB)) (eq-is-contr HAB))

-- Exercise 12.3 (b)

abstract
  all-elements-equal-coprod :
    {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
    (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
    all-elements-equal (coprod P Q)
  all-elements-equal-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inl p') =
    ap inl (is-prop-P p p')
  all-elements-equal-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inl p) (inr q') =
    ex-falso (f p q')
  all-elements-equal-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inl p') =
    ex-falso (f p' q)
  all-elements-equal-coprod
    {P = P} {Q = Q} f is-prop-P is-prop-Q (inr q) (inr q') =
    ap inr (is-prop-Q q q')

abstract
  is-prop-coprod :
    {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
    (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
  is-prop-coprod f is-prop-P is-prop-Q =
    is-prop-all-elements-equal
      ( all-elements-equal-coprod f
        ( eq-is-prop' is-prop-P)
        ( eq-is-prop' is-prop-Q))

-- Exercise 12.3 (c)

abstract
  is-trunc-coprod : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc (succ-𝕋 (succ-𝕋 k)) A → is-trunc (succ-𝕋 (succ-𝕋 k)) B →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (coprod A B)
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inl y) =
    is-trunc-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inl y))
      ( equiv-Eq-eq-coprod A B (inl x) (inl y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( Id x y)
        ( equiv-raise _ (Id x y))
        ( is-trunc-A x y))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inl x) (inr y) =
    is-trunc-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inl x) (inr y))
      ( equiv-Eq-eq-coprod A B (inl x) (inr y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( empty)
        ( equiv-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inl y) =
    is-trunc-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inl y))
      ( equiv-Eq-eq-coprod A B (inr x) (inl y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( empty)
        ( equiv-raise _ empty)
        ( is-trunc-succ-empty k))
  is-trunc-coprod k {A} {B} is-trunc-A is-trunc-B (inr x) (inr y) =
    is-trunc-equiv (succ-𝕋 k)
      ( Eq-coprod A B (inr x) (inr y))
      ( equiv-Eq-eq-coprod A B (inr x) (inr y))
      ( is-trunc-equiv' (succ-𝕋 k)
        ( Id x y)
        ( equiv-raise _ (Id x y))
        ( is-trunc-B x y))

abstract
  is-set-coprod : {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (coprod A B)
  is-set-coprod = is-trunc-coprod neg-two-𝕋

coprod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
coprod-Set (pair A is-set-A) (pair B is-set-B) =
  pair (coprod A B) (is-set-coprod is-set-A is-set-B)

abstract
  is-set-unit : is-set unit
  is-set-unit = is-trunc-succ-is-trunc neg-one-𝕋 is-prop-unit

unit-Set : UU-Set lzero
unit-Set = pair unit is-set-unit

abstract
  is-set-ℤ : is-set ℤ
  is-set-ℤ = is-set-coprod is-set-ℕ (is-set-coprod is-set-unit is-set-ℕ)

ℤ-Set : UU-Set lzero
ℤ-Set = pair ℤ is-set-ℤ

is-set-empty : is-set empty
is-set-empty ()

empty-Set : UU-Set lzero
empty-Set = pair empty is-set-empty

abstract
  is-set-Fin :
    (n : ℕ) → is-set (Fin n)
  is-set-Fin zero-ℕ = is-set-empty
  is-set-Fin (succ-ℕ n) =
    is-set-coprod (is-set-Fin n) is-set-unit

Fin-Set :
  (n : ℕ) → UU-Set lzero
Fin-Set n = pair (Fin n) (is-set-Fin n)

-- Exercise 12.4

module _
  {l : Level} (A : UU l)
  where

  diagonal : A → A × A
  diagonal x = pair x x

  -- Exercise 12.4 (a)
  
  abstract
    is-prop-is-equiv-diagonal : is-equiv diagonal → is-prop A
    is-prop-is-equiv-diagonal is-equiv-d =
      is-prop-all-elements-equal ( λ x y →
        let α = issec-map-inv-is-equiv is-equiv-d (pair x y) in
        ( inv (ap pr1 α)) ∙ (ap pr2 α))
  
  eq-fib-diagonal : (t : A × A) → fib diagonal t → Id (pr1 t) (pr2 t)
  eq-fib-diagonal (pair x y) (pair z α) = (inv (ap pr1 α)) ∙ (ap pr2 α)
  
  fib-diagonal-eq : (t : A × A) → Id (pr1 t) (pr2 t) → fib diagonal t
  fib-diagonal-eq (pair x y) β = pair x (eq-pair refl β)
  
  issec-fib-diagonal-eq :
    (t : A × A) → ((eq-fib-diagonal t) ∘ (fib-diagonal-eq t)) ~ id
  issec-fib-diagonal-eq (pair x .x) refl = refl
  
  isretr-fib-diagonal-eq :
    (t : A × A) → ((fib-diagonal-eq t) ∘ (eq-fib-diagonal t)) ~ id
  isretr-fib-diagonal-eq .(pair z z) (pair z refl) = refl
  
  abstract
    is-equiv-eq-fib-diagonal : (t : A × A) → is-equiv (eq-fib-diagonal t)
    is-equiv-eq-fib-diagonal t =
      is-equiv-has-inverse
        ( fib-diagonal-eq t)
        ( issec-fib-diagonal-eq t)
        ( isretr-fib-diagonal-eq t)

-- Exercise 12.4 (c)

module _
  {l : Level} (k : 𝕋) (A : UU l)
  where
  
  abstract
    is-trunc-is-trunc-diagonal :
      is-trunc-map k (diagonal A) → is-trunc (succ-𝕋 k) A
    is-trunc-is-trunc-diagonal is-trunc-d x y =
      is-trunc-is-equiv' k
        ( fib (diagonal A) (pair x y))
        ( eq-fib-diagonal A (pair x y))
        ( is-equiv-eq-fib-diagonal A (pair x y))
        ( is-trunc-d (pair x y))
  
  abstract
    is-trunc-diagonal-is-trunc : 
      is-trunc (succ-𝕋 k) A → is-trunc-map k (diagonal A)
    is-trunc-diagonal-is-trunc is-trunc-A t =
      is-trunc-is-equiv k
        ( Id (pr1 t) (pr2 t))
        ( eq-fib-diagonal A t)
        ( is-equiv-eq-fib-diagonal A t)
        ( is-trunc-A (pr1 t) (pr2 t))

-- Exercise 12.5

-- Exercise 12.5 (a)

abstract
  is-trunc-Σ : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → ((x : A) → is-trunc k (B x)) → is-trunc k (Σ A B)
  is-trunc-Σ neg-two-𝕋 is-trunc-A is-trunc-B =
    is-contr-Σ is-trunc-A is-trunc-B
  is-trunc-Σ (succ-𝕋 k) {B = B} is-trunc-A is-trunc-B s t =
    is-trunc-is-equiv k
      ( Σ (Id (pr1 s) (pr1 t)) (λ p → Id (tr B p (pr2 s)) (pr2 t)))
      ( pair-eq-Σ)
      ( is-equiv-pair-eq-Σ s t)
      ( is-trunc-Σ k
        ( is-trunc-A (pr1 s) (pr1 t))
        ( λ p → is-trunc-B (pr1 t) (tr B p (pr2 s)) (pr2 t)))

-- Exercise 12.5 (b)

-- Bureaucracy

abstract
  is-prop-Σ : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-prop A → is-subtype B → is-prop (Σ A B)
  is-prop-Σ = is-trunc-Σ neg-one-𝕋

Σ-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : type-Prop P → UU-Prop l2) →
  UU-Prop (l1 ⊔ l2)
Σ-Prop P Q =
  pair
    ( Σ (type-Prop P) (λ p → type-Prop (Q p)))
    ( is-prop-Σ
      ( is-prop-type-Prop P)
      ( λ p → is-prop-type-Prop (Q p)))

abstract
  is-set-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-set A → ((x : A) → is-set (B x)) → is-set (Σ A B)
  is-set-Σ = is-trunc-Σ zero-𝕋

Σ-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : pr1 A → UU-Set l2) → UU-Set (l1 ⊔ l2)
Σ-Set A B =
  pair
    ( Σ (type-Set A) (λ x → (type-Set (B x))))
    ( is-set-Σ (is-set-type-Set A) (λ x → is-set-type-Set (B x)))

prod-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2) → UU-Set (l1 ⊔ l2)
prod-Set A B = Σ-Set A (λ x → B)

-- Exercise 12.5 (b)

abstract
  is-trunc-map-is-trunc-domain-codomain :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1}
    {B : UU l2} {f : A → B} → is-trunc k A → is-trunc k B → is-trunc-map k f
  is-trunc-map-is-trunc-domain-codomain k {f = f} is-trunc-A is-trunc-B b =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-Id k is-trunc-B (f x) b)

-- Bureaucracy

abstract
  is-trunc-fam-is-trunc-Σ :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
    is-trunc k A → is-trunc k (Σ A B) → (x : A) → is-trunc k (B x)
  is-trunc-fam-is-trunc-Σ k {B = B} is-trunc-A is-trunc-ΣAB x =
    is-trunc-equiv' k
      ( fib pr1 x)
      ( equiv-fib-pr1 x)
      ( is-trunc-map-is-trunc-domain-codomain k is-trunc-ΣAB is-trunc-A x)

-- Exercise 12.6

abstract
  is-trunc-prod :
    {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    is-trunc k A → is-trunc k B → is-trunc k (A × B)
  is-trunc-prod k is-trunc-A is-trunc-B =
    is-trunc-Σ k is-trunc-A (λ x → is-trunc-B)

is-trunc-prod' :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  (B → is-trunc (succ-𝕋 k) A) → (A → is-trunc (succ-𝕋 k) B) →
  is-trunc (succ-𝕋 k) (A × B)
is-trunc-prod' k f g (pair a b) (pair a' b') =
  is-trunc-equiv k
    ( Eq-prod (pair a b) (pair a' b'))
    ( equiv-pair-eq (pair a b) (pair a' b'))
    ( is-trunc-prod k (f b a a') (g a b b'))

is-trunc-left-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → B → is-trunc k A
is-trunc-left-factor-prod neg-two-𝕋 {A} {B} H b =
  is-contr-left-factor-prod A B H
is-trunc-left-factor-prod (succ-𝕋 k) H b a a' =
  is-trunc-left-factor-prod k {A = Id a a'} {B = Id b b}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a' b))
      ( equiv-pair-eq (pair a b) (pair a' b))
      ( H (pair a b) (pair a' b)))
    ( refl)

is-trunc-right-factor-prod :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  is-trunc k (A × B) → A → is-trunc k B
is-trunc-right-factor-prod neg-two-𝕋 {A} {B} H a =
  is-contr-right-factor-prod A B H
is-trunc-right-factor-prod (succ-𝕋 k) {A} {B} H a b b' =
  is-trunc-right-factor-prod k {A = Id a a} {B = Id b b'}
    ( is-trunc-equiv' k
      ( Id (pair a b) (pair a b'))
      ( equiv-pair-eq (pair a b) (pair a b'))
      ( H (pair a b) (pair a b')))
    ( refl)

-- Bureaucracy

abstract
  is-prop-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-prop A → is-prop B → is-prop (A × B)
  is-prop-prod = is-trunc-prod neg-one-𝕋

prod-Prop : {l1 l2 : Level} → UU-Prop l1 → UU-Prop l2 → UU-Prop (l1 ⊔ l2)
prod-Prop P Q =
  pair
    ( type-Prop P × type-Prop Q)
    ( is-prop-prod (is-prop-type-Prop P) (is-prop-type-Prop Q))

abstract
  is-set-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-set A → is-set B → is-set (A × B)
  is-set-prod = is-trunc-prod zero-𝕋

-- Exercise 12.7

-- Exercise 12.7 (a)

{- In this exercise we show that if A is a retract of B, then so are its 
   identity types. -}

ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → Id (i x) (i y) → Id x y
ap-retraction i r H x y p =
    ( inv (H x)) ∙ ((ap r p) ∙ (H y))

isretr-ap-retraction :
  {i j : Level} {A : UU i} {B : UU j}
  (i : A → B) (r : B → A) (H : (r ∘ i) ~ id)
  (x y : A) → ((ap-retraction i r H x y) ∘ (ap i {x} {y})) ~ id
isretr-ap-retraction i r H x .x refl = left-inv (H x)

retr-ap :
  {i j : Level} {A : UU i} {B : UU j} (i : A → B) →
  retr i → (x y : A) → retr (ap i {x} {y})
retr-ap i (pair r H) x y =
  pair (ap-retraction i r H x y) (isretr-ap-retraction i r H x y)

retract-eq :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (R : A retract-of B) →
  (x y : A) → (Id x y) retract-of (Id (pr1 R x) (pr1 R y))
retract-eq (pair i (pair r H)) x y =
  pair (ap i) (retr-ap i (pair r H) x y)

-- Exercise 12.7 (b)

abstract
  is-trunc-retract-of : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of neg-two-𝕋 (pair i (pair r H)) is-trunc-B =
    is-contr-retract-of _ (pair i (pair r H)) is-trunc-B
  is-trunc-retract-of (succ-𝕋 k) (pair i retr-i) is-trunc-B x y =
    is-trunc-retract-of k
      ( retract-eq (pair i retr-i) x y)
      ( is-trunc-B (i x) (i y))

-- Exercise 12.8

fib-const :
  {l : Level} {A : UU l} (x y : A) → fib (const unit A x) y ≃ (Id x y)
fib-const x y = left-unit-law-prod (Id x y)

abstract
  is-trunc-const-is-trunc : {l : Level} (k : 𝕋) {A : UU l} →
    is-trunc (succ-𝕋 k) A → (x : A) → is-trunc-map k (const unit A x)
  is-trunc-const-is-trunc k is-trunc-A x y =
    is-trunc-equiv k
      ( Id x y)
      ( fib-const x y)
      ( is-trunc-A x y)

abstract
  is-trunc-is-trunc-const : {l : Level} (k : 𝕋) {A : UU l} →
    ((x : A) → is-trunc-map k (const unit A x)) → is-trunc (succ-𝕋 k) A
  is-trunc-is-trunc-const k is-trunc-const x y =
    is-trunc-equiv' k
      ( Σ unit (λ t → Id x y))
      ( left-unit-law-Σ (λ t → Id x y))
      ( is-trunc-const x y)

-- Exercise 12.9

map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → fib (g ∘ h) x → Σ (fib g x) (λ t → fib h (pr1 t))
map-fib-comp g h x (pair a p) =
  pair
    ( pair (h a) p)
    ( pair a refl)

inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) → Σ (fib g x) (λ t → fib h (pr1 t)) → fib (g ∘ h) x
inv-map-fib-comp g h c t =
  pair (pr1 (pr2 t)) ((ap g (pr2 (pr2 t))) ∙ (pr2 (pr1 t)))

issec-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) →
  (x : X) →
  ((map-fib-comp g h x) ∘ (inv-map-fib-comp g h x)) ~ id
issec-inv-map-fib-comp g h x
  (pair (pair .(h a) refl) (pair a refl)) = refl

isretr-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  {X : UU l3} (g : B → X) (h : A → B) (x : X) →
  ((inv-map-fib-comp g h x) ∘ (map-fib-comp g h x)) ~ id
isretr-inv-map-fib-comp g h .(g (h a)) (pair a refl) = refl

abstract
  is-equiv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (map-fib-comp g h x)
  is-equiv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)

abstract
  is-equiv-inv-map-fib-comp : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {X : UU l3} (g : B → X) (h : A → B) (x : X) →
    is-equiv (inv-map-fib-comp g h x)
  is-equiv-inv-map-fib-comp g h x =
    is-equiv-has-inverse
      ( map-fib-comp g h x)
      ( isretr-inv-map-fib-comp g h x)
      ( issec-inv-map-fib-comp g h x)

abstract
  is-trunc-map-htpy : {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    (f g : A → B) → f ~ g → is-trunc-map k g → is-trunc-map k f
  is-trunc-map-htpy k {A} f g H is-trunc-g b =
    is-trunc-is-equiv k
      ( Σ A (λ z → Id (g z) b))
      ( fib-triangle f g id H b)
      ( is-fiberwise-equiv-is-equiv-triangle f g id H is-equiv-id b)
      ( is-trunc-g b)

abstract
  is-trunc-map-comp : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k h → is-trunc-map k f
  is-trunc-map-comp k f g h H is-trunc-g is-trunc-h =
    is-trunc-map-htpy k f (g ∘ h) H
      ( λ x → is-trunc-is-equiv k
        ( Σ (fib g x) (λ t → fib h (pr1 t)))
        ( map-fib-comp g h x)
        ( is-equiv-map-fib-comp g h x)
        ( is-trunc-Σ k
          ( is-trunc-g x)
          ( λ t → is-trunc-h (pr1 t))))

abstract
  is-trunc-map-right-factor : {l1 l2 l3 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
    {X : UU l3} (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-trunc-map k g → is-trunc-map k f → is-trunc-map k h
  is-trunc-map-right-factor k {A} f g h H is-trunc-g is-trunc-f b =
    is-trunc-fam-is-trunc-Σ k
      ( is-trunc-g (g b))
      ( is-trunc-is-equiv' k
        ( Σ A (λ z → Id (g (h z)) (g b)))
        ( map-fib-comp g h (g b))
        ( is-equiv-map-fib-comp g h (g b))
        ( is-trunc-map-htpy k (g ∘ h) f (inv-htpy H) is-trunc-f (g b)))
      ( pair b refl)

-- Exercise 12.10

module _
  {l1 l2 l3 : Level} (k : 𝕋)  {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  is-fiberwise-trunc : UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-trunc = (x : A) → is-trunc-map k (f x)

  abstract
    is-trunc-tot-is-fiberwise-trunc :
      is-fiberwise-trunc → is-trunc-map k (tot f)
    is-trunc-tot-is-fiberwise-trunc is-fiberwise-trunc-f (pair x z) =
      is-trunc-is-equiv k
        ( fib (f x) z)
        ( fib-ftr-fib-tot f (pair x z))
        ( is-equiv-fib-ftr-fib-tot f (pair x z))
        ( is-fiberwise-trunc-f x z)

  abstract
    is-fiberwise-trunc-is-trunc-tot : 
      is-trunc-map k (tot f) → is-fiberwise-trunc
    is-fiberwise-trunc-is-trunc-tot is-trunc-tot-f x z =
      is-trunc-is-equiv k
        ( fib (tot f) (pair x z))
        ( fib-tot-fib-ftr f (pair x z))
        ( is-equiv-fib-tot-fib-ftr f (pair x z))
        ( is-trunc-tot-f (pair x z))

-- Exercise 12.11

fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) → B x → Σ A B
fiber-inclusion B x = pair x

fib-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) (a : A) (t : Σ A B) →
  fib (fiber-inclusion B a) t ≃ Id a (pr1 t)
fib-fiber-inclusion B a t =
  ( ( right-unit-law-Σ-is-contr
      ( λ p → is-contr-map-is-equiv (is-equiv-tr B p) (pr2 t))) ∘e
    ( equiv-left-swap-Σ)) ∘e
  ( equiv-tot (λ b → equiv-pair-eq-Σ (pair a b) t))

is-trunc-is-trunc-map-fiber-inclusion :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} →
  ((B : A → UU l2) (a : A) → is-trunc-map k (fiber-inclusion B a)) →
  is-trunc (succ-𝕋 k) A
is-trunc-is-trunc-map-fiber-inclusion {l1} {l2} k {A} H x y =
  is-trunc-equiv' k
    ( fib (fiber-inclusion B x) (pair y raise-star))
    ( fib-fiber-inclusion B x (pair y raise-star))
    ( H B x (pair y raise-star))
  where
  B : A → UU l2
  B a = raise-unit l2

is-trunc-map-fiber-inclusion-is-trunc :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} (B : A → UU l2) (a : A) →
  is-trunc (succ-𝕋 k) A → is-trunc-map k (fiber-inclusion B a)
is-trunc-map-fiber-inclusion-is-trunc k B a H t =
  is-trunc-equiv k
    ( Id a (pr1 t))
    ( fib-fiber-inclusion B a t)
    ( H a (pr1 t))

is-emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  is-set A → (x : A) → is-emb (fiber-inclusion B x)
is-emb-fiber-inclusion B H x =
  is-emb-is-prop-map (is-trunc-map-fiber-inclusion-is-trunc neg-one-𝕋 B x H)

emb-fiber-inclusion :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) → is-set A → (x : A) → B x ↪ Σ A B
emb-fiber-inclusion B H x =
  pair (fiber-inclusion B x) (is-emb-fiber-inclusion B H x)

-- Exercise 12.12

is-isolated :
  {l1 : Level} {X : UU l1} (x : X) → UU l1
is-isolated {l1} {X} x = (y : X) → is-decidable (Id x y)

isolated-point :
  {l1 : Level} (X : UU l1) → UU l1
isolated-point X = Σ X is-isolated

-- We will use a few facts about decidability in this exercise

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-decidable-map : (A → B) → UU (l1 ⊔ l2)
  is-decidable-map f = (y : B) → is-decidable (fib f y)

  is-decidable-retract-of :
    A retract-of B → is-decidable B → is-decidable A
  is-decidable-retract-of (pair i (pair r H)) (inl b) = inl (r b)
  is-decidable-retract-of (pair i (pair r H)) (inr f) = inr (f ∘ i)

  is-decidable-is-equiv :
    {f : A → B} → is-equiv f → is-decidable B → is-decidable A
  is-decidable-is-equiv {f} (pair (pair g G) (pair h H)) =
    is-decidable-retract-of (pair f (pair h H))

  is-decidable-equiv :
    (e : A ≃ B) → is-decidable B → is-decidable A
  is-decidable-equiv e = is-decidable-iff (map-inv-equiv e) (map-equiv e)

is-decidable-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-decidable A → is-decidable B
is-decidable-equiv' e = is-decidable-equiv (inv-equiv e)

module _
  {l1 : Level} {A : UU l1} (a : A)
  where
  
  -- Exercise 12.12 (a)
  
  is-decidable-map-const-is-isolated :
    is-isolated a → is-decidable-map (const unit A a)
  is-decidable-map-const-is-isolated d x =
    is-decidable-equiv (fib-const a x) (d x)

  is-isolated-is-decidable-map-const :
    is-decidable-map (const unit A a) → is-isolated a
  is-isolated-is-decidable-map-const d x =
    is-decidable-equiv' (fib-const a x) (d x)

  -- Exercise 12.12 (b)
  
  cases-Eq-isolated-point :
    is-isolated a → (x : A) → is-decidable (Id a x) → UU lzero
  cases-Eq-isolated-point H x (inl p) = unit
  cases-Eq-isolated-point H x (inr f) = empty

  is-prop-cases-Eq-isolated-point :
    (d : is-isolated a) (x : A) (dx : is-decidable (Id a x)) →
    is-prop (cases-Eq-isolated-point d x dx)
  is-prop-cases-Eq-isolated-point d x (inl p) = is-prop-unit
  is-prop-cases-Eq-isolated-point d x (inr f) = is-prop-empty

  Eq-isolated-point : is-isolated a → A → UU lzero
  Eq-isolated-point d x = cases-Eq-isolated-point d x (d x)

  is-prop-Eq-isolated-point :
    (d : is-isolated a) (x : A) → is-prop (Eq-isolated-point d x)
  is-prop-Eq-isolated-point d x =
    is-prop-cases-Eq-isolated-point d x (d x)

  decide-reflexivity :
    (d : is-decidable (Id a a)) → Σ (Id a a) (λ p → Id (inl p) d)
  decide-reflexivity (inl p) = pair p refl
  decide-reflexivity (inr f) = ex-falso (f refl)

  refl-Eq-isolated-point : (d : is-isolated a) → Eq-isolated-point d a
  refl-Eq-isolated-point d =
    tr ( cases-Eq-isolated-point d a)
       ( pr2 (decide-reflexivity (d a)))
       ( star)

  Eq-eq-isolated-point :
    (d : is-isolated a) {x : A} → Id a x → Eq-isolated-point d x
  Eq-eq-isolated-point d refl = refl-Eq-isolated-point d

  center-total-Eq-isolated-point :
    (d : is-isolated a) → Σ A (Eq-isolated-point d)
  center-total-Eq-isolated-point d =
    pair a (refl-Eq-isolated-point d)

  cases-contraction-total-Eq-isolated-point :
    (d : is-isolated a) (x : A) (dx : is-decidable (Id a x))
    (e : cases-Eq-isolated-point d x dx) → Id a x
  cases-contraction-total-Eq-isolated-point d x (inl p) e = p

  contraction-total-Eq-isolated-point :
    (d : is-isolated a) (t : Σ A (Eq-isolated-point d)) →
    Id (center-total-Eq-isolated-point d) t
  contraction-total-Eq-isolated-point d (pair x e) =
    eq-subtype
      ( is-prop-Eq-isolated-point d)
      ( cases-contraction-total-Eq-isolated-point d x (d x) e)

  is-contr-total-Eq-isolated-point :
    (d : is-isolated a) → is-contr (Σ A (Eq-isolated-point d))
  is-contr-total-Eq-isolated-point d =
    pair ( center-total-Eq-isolated-point d)
         ( contraction-total-Eq-isolated-point d)

  is-equiv-Eq-eq-isolated-point :
    (d : is-isolated a) (x : A) → is-equiv (Eq-eq-isolated-point d {x})
  is-equiv-Eq-eq-isolated-point d =
    fundamental-theorem-id a
      ( refl-Eq-isolated-point d)
      ( is-contr-total-Eq-isolated-point d)
      ( λ x → Eq-eq-isolated-point d {x})

  equiv-Eq-eq-isolated-point :
    (d : is-isolated a) (x : A) → Id a x ≃ Eq-isolated-point d x
  equiv-Eq-eq-isolated-point d x =
    pair (Eq-eq-isolated-point d) (is-equiv-Eq-eq-isolated-point d x)

  is-prop-eq-isolated-point : (d : is-isolated a) (x : A) → is-prop (Id a x)
  is-prop-eq-isolated-point d x =
    is-prop-equiv
      ( Eq-isolated-point d x)
      ( equiv-Eq-eq-isolated-point d x)
      ( is-prop-Eq-isolated-point d x)

  is-emb-const-is-isolated : is-isolated a → is-emb (const unit A a)
  is-emb-const-is-isolated d star =
    fundamental-theorem-id star
      refl
      ( is-contr-equiv
        ( Id a a)
        ( left-unit-law-prod (Id a a))
        ( is-proof-irrelevant-is-prop
          ( is-prop-eq-isolated-point d a)
          ( refl)))
      ( λ x → ap (λ y → a))

has-decidable-equality-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → has-decidable-equality B → has-decidable-equality A
has-decidable-equality-retract-of (pair i (pair r H)) d x y =
  is-decidable-retract-of
    ( retract-eq (pair i (pair r H)) x y)
    ( d (i x) (i y))

--------------------------------------------------------------------------------

-- Extra stuff

has-decidable-equality-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  has-decidable-equality A → ((x : A) → has-decidable-equality (B x)) →
  has-decidable-equality (Σ A B)
has-decidable-equality-Σ dA dB (pair x y) (pair x' y') with dA x x'
... | inr np = inr (λ r → np (ap pr1 r))
... | inl p =
  is-decidable-iff eq-pair-Σ' pair-eq-Σ
    ( is-decidable-equiv
      ( left-unit-law-Σ-is-contr
        ( is-proof-irrelevant-is-prop
          ( is-set-has-decidable-equality dA x x') p)
        ( p))
      ( dB x' (tr _ p y) y'))

has-decidable-equality-is-prop :
  {l1 : Level} {A : UU l1} → is-prop A → has-decidable-equality A
has-decidable-equality-is-prop H x y = inl (eq-is-prop H)

has-decidable-equality-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality B → has-decidable-equality A
has-decidable-equality-equiv e dB x y =
  is-decidable-equiv (equiv-ap e x y) (dB (map-equiv e x) (map-equiv e y))

has-decidable-equality-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  has-decidable-equality A → has-decidable-equality B
has-decidable-equality-equiv' e = has-decidable-equality-equiv (inv-equiv e)

has-decidable-equality-fiber-has-decidable-equality-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  has-decidable-equality A → has-decidable-equality (Σ A B) →
  (x : A) → has-decidable-equality (B x)
has-decidable-equality-fiber-has-decidable-equality-Σ {B = B} dA dΣ x =
  has-decidable-equality-equiv'
    ( equiv-fib-pr1 x)
    ( has-decidable-equality-Σ dΣ
      (λ t → has-decidable-equality-is-prop
               ( is-set-has-decidable-equality dA (pr1 t) x)))

is-injective-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-injective (map-section b)
is-injective-map-section b = ap pr1

has-decidable-equality-base-has-decidable-equality-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  has-decidable-equality (Σ A B) → ((x : A) → has-decidable-equality (B x)) →
  has-decidable-equality A
has-decidable-equality-base-has-decidable-equality-Σ b dΣ dB =
  has-decidable-equality-equiv'
    ( equiv-total-fib (map-section b))
    ( has-decidable-equality-Σ dΣ
      ( λ t →
        has-decidable-equality-is-prop
          ( is-prop-map-is-injective
            ( is-set-has-decidable-equality dΣ)
            ( is-injective-map-section b)
            ( t))))

is-injective-const-true : is-injective (const unit bool true)
is-injective-const-true {star} {star} p = refl

is-injective-const-false : is-injective (const unit bool false)
is-injective-const-false {star} {star} p = refl

equiv-total-subtype :
  { l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2} {Q : A → UU l3} →
  ( is-subtype-P : is-subtype P) (is-subtype-Q : is-subtype Q) →
  ( f : (x : A) → P x → Q x) →
  ( g : (x : A) → Q x → P x) →
  ( Σ A P) ≃ (Σ A Q)
equiv-total-subtype is-subtype-P is-subtype-Q f g =
  pair
    ( tot f)
    ( is-equiv-tot-is-fiberwise-equiv {f = f}
      ( λ x → is-equiv-is-prop (is-subtype-P x) (is-subtype-Q x) (g x)))

{- We show that if f : A → B is an embedding, then the induced map
   Σ A (C ∘ f) → Σ A C is also an embedding. -}

is-emb-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  is-emb f → is-emb (map-Σ-map-base f C)
is-emb-map-Σ-map-base f C is-emb-f =
  is-emb-is-prop-map
    ( λ x →
      is-prop-equiv'
        ( fib f (pr1 x))
        ( equiv-fib-map-Σ-map-base-fib f C x)
        ( is-prop-map-is-emb is-emb-f (pr1 x)))
