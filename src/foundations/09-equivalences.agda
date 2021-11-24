{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.09-equivalences where

open import foundations.08-integers public

--------------------------------------------------------------------------------

-- Section 9.1 Homotopies

-- Definition 9.1.2

_~_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f g : (x : A) → B x) → UU (l1 ⊔ l2)
f ~ g = (x : _) → Id (f x) (g x)

-- Example 9.1.3

neg-neg-𝟚 : (neg-𝟚 ∘ neg-𝟚) ~ id
neg-neg-𝟚 true = refl
neg-neg-𝟚 false = refl

-- Remark 9.1.4

square :
  {l1 : Level} {A : UU l1} {x y1 y2 z : A}
  (p-left : Id x y1) (p-bottom : Id y1 z)
  (p-top : Id x y2) (p-right : Id y2 z) → UU l1
square p-left p-bottom p-top p-right = Id (p-left ∙ p-bottom) (p-top ∙ p-right)

-- Definition 9.1.5

refl-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f : (x : A) → B x} → f ~ f
refl-htpy x = refl

{- Most of the time we get by with refl-htpy. However, sometimes Agda wants us
   to specify the implicit argument. The it is easier to call refl-htpy' than
   to use Agda's {f = ?} notation. -}
   
refl-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) → f ~ f
refl-htpy' f = refl-htpy

inv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (g ~ f)
inv-htpy H x = inv (H x)

_∙h_ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (f ~ g) → (g ~ h) → (f ~ h)
_∙h_ H K x = (H x) ∙ (K x)

concat-htpy :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  (f ~ g) → (h : (x : A) → B x) → (g ~ h) → (f ~ h)
concat-htpy H h K x = concat (H x) (h x) (K x)

concat-htpy' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (f : (x : A) → B x) {g h : (x : A) → B x} →
  (g ~ h) → (f ~ g) → (f ~ h)
concat-htpy' f K H = H ∙h K

-- Proposition 9.1.6

-- Proposition 9.1.6 (i)

assoc-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g h k : (x : A) → B x} →
  (H : f ~ g) → (K : g ~ h) → (L : h ~ k) →
  ((H ∙h K) ∙h L) ~ (H ∙h (K ∙h L))
assoc-htpy H K L x = assoc (H x) (K x) (L x)

-- Proposition 9.1.6 (ii)

left-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (refl-htpy ∙h H) ~ H
left-unit-htpy x = left-unit

right-unit-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  {H : f ~ g} → (H ∙h refl-htpy) ~ H
right-unit-htpy x = right-unit

-- Proposition 9.1.6 (iii)

left-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → ((inv-htpy H) ∙h H) ~ refl-htpy
left-inv-htpy H x = left-inv (H x)

right-inv-htpy :
  {i j : Level} {A : UU i} {B : A → UU j} {f g : (x : A) → B x}
  (H : f ~ g) → (H ∙h (inv-htpy H)) ~ refl-htpy
right-inv-htpy H x = right-inv (H x)

-- Definition 9.1.7

-- Definition 9.1.7 (i)

htpy-left-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  (h : B → C) {f g : A → B} → (f ~ g) → ((h ∘ f) ~ (h ∘ g))
htpy-left-whisk h H x = ap h (H x)

_·l_ = htpy-left-whisk

-- Definition 9.1.7 (ii)

htpy-right-whisk :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k}
  {g h : B → C} (H : g ~ h) (f : A → B) → ((g ∘ f) ~ (h ∘ f))
htpy-right-whisk H f x = H (f x)

_·r_ = htpy-right-whisk

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq

--------------------------------------------------------------------------------

-- Section 9.2 Bi-invertible maps

-- Definition 9.2.1

-- Definition 9.2.1 (i)

sec :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
sec {i} {j} {A} {B} f = Σ (B → A) (λ g → (f ∘ g) ~ id)

-- Definition 9.2.1 (ii)

retr :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
retr {i} {j} {A} {B} f = Σ (B → A) (λ g → (g ∘ f) ~ id)

_retract-of_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A retract-of B = Σ (A → B) retr

section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → A retract-of B → A → B
section-retract-of = pr1

retr-section-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  retr (section-retract-of R)
retr-section-retract-of = pr2

retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} → (A retract-of B) → B → A
retraction-retract-of R = pr1 (retr-section-retract-of R)

is-retr-retraction-retract-of :
  {i j : Level} {A : UU i} {B : UU j} (R : A retract-of B) →
  ((retraction-retract-of R) ∘ (section-retract-of R)) ~ id
is-retr-retraction-retract-of R = pr2 (retr-section-retract-of R)

-- Definition 9.2.1 (ii)

is-equiv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) (λ f → is-equiv f)

map-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A → B)
map-equiv e = pr1 e

is-equiv-map-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-equiv e)
is-equiv-map-equiv e = pr2 e

-- Example 9.2.3

is-equiv-id :
  {i : Level} {A : UU i} → is-equiv (id {i} {A})
pr1 (pr1 is-equiv-id) = id
pr2 (pr1 is-equiv-id) = refl-htpy
pr1 (pr2 is-equiv-id) = id
pr2 (pr2 is-equiv-id) = refl-htpy

equiv-id :
  {i : Level} {A : UU i} → A ≃ A
pr1 equiv-id = id
pr2 equiv-id = is-equiv-id

-- Example 9.2.4

abstract
  is-equiv-neg-𝟚 : is-equiv neg-𝟚
  pr1 (pr1 is-equiv-neg-𝟚) = neg-𝟚
  pr2 (pr1 is-equiv-neg-𝟚) = neg-neg-𝟚
  pr1 (pr2 is-equiv-neg-𝟚) = neg-𝟚
  pr2 (pr2 is-equiv-neg-𝟚) = neg-neg-𝟚

equiv-neg-𝟚 : bool ≃ bool
pr1 equiv-neg-𝟚 = neg-𝟚
pr2 equiv-neg-𝟚 = is-equiv-neg-𝟚

-- Example 9.2.5

-- We show that succ-ℤ is an equivalence

abstract
  is-equiv-succ-ℤ : is-equiv succ-ℤ
  pr1 (pr1 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr1 is-equiv-succ-ℤ) = right-inverse-pred-ℤ
  pr1 (pr2 is-equiv-succ-ℤ) = pred-ℤ
  pr2 (pr2 is-equiv-succ-ℤ) = left-inverse-pred-ℤ

equiv-succ-ℤ : ℤ ≃ ℤ
pr1 equiv-succ-ℤ = succ-ℤ
pr2 equiv-succ-ℤ = is-equiv-succ-ℤ

-- We show that pred-ℤ is an equivalence

abstract
  is-equiv-pred-ℤ : is-equiv pred-ℤ
  pr1 (pr1 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr1 is-equiv-pred-ℤ) = left-inverse-pred-ℤ
  pr1 (pr2 is-equiv-pred-ℤ) = succ-ℤ
  pr2 (pr2 is-equiv-pred-ℤ) = right-inverse-pred-ℤ

equiv-pred-ℤ : ℤ ≃ ℤ
pr1 equiv-pred-ℤ = pred-ℤ
pr2 equiv-pred-ℤ = is-equiv-pred-ℤ

-- We show that add-ℤ x is an equivalence

abstract
  is-equiv-add-ℤ : (x : ℤ) → is-equiv (add-ℤ x)
  pr1 (pr1 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr1 (is-equiv-add-ℤ x)) y =
    ( inv (associative-add-ℤ x (neg-ℤ x) y)) ∙
    ( ( ap (add-ℤ' y) (right-inverse-law-add-ℤ x)) ∙
      ( left-unit-law-add-ℤ y))
  pr1 (pr2 (is-equiv-add-ℤ x)) = add-ℤ (neg-ℤ x)
  pr2 (pr2 (is-equiv-add-ℤ x)) y =
    ( inv (associative-add-ℤ (neg-ℤ x) x y)) ∙
    ( ( ap (add-ℤ' y) (left-inverse-law-add-ℤ x)) ∙
      ( left-unit-law-add-ℤ y))

equiv-add-ℤ : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ x) = add-ℤ x
pr2 (equiv-add-ℤ x) = is-equiv-add-ℤ x

-- We show that add-ℤ' y is an equivalence

abstract
  is-equiv-add-ℤ' : (y : ℤ) → is-equiv (add-ℤ' y)
  pr1 (pr1 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr1 (is-equiv-add-ℤ' y)) x =
    ( associative-add-ℤ x (neg-ℤ y) y) ∙
    ( ( ap (add-ℤ x) (left-inverse-law-add-ℤ y)) ∙
      ( right-unit-law-add-ℤ x))
  pr1 (pr2 (is-equiv-add-ℤ' y)) = add-ℤ' (neg-ℤ y)
  pr2 (pr2 (is-equiv-add-ℤ' y)) x =
    ( associative-add-ℤ x y (neg-ℤ y)) ∙
    ( ( ap (add-ℤ x) (right-inverse-law-add-ℤ y)) ∙
      ( right-unit-law-add-ℤ x))

equiv-add-ℤ' : ℤ → (ℤ ≃ ℤ)
pr1 (equiv-add-ℤ' y) = add-ℤ' y
pr2 (equiv-add-ℤ' y) = is-equiv-add-ℤ' y

-- We show that neg-ℤ is an equivalence

abstract
  is-equiv-neg-ℤ : is-equiv neg-ℤ
  pr1 (pr1 is-equiv-neg-ℤ) = neg-ℤ
  pr2 (pr1 is-equiv-neg-ℤ) = neg-neg-ℤ
  pr1 (pr2 is-equiv-neg-ℤ) = neg-ℤ
  pr2 (pr2 is-equiv-neg-ℤ) = neg-neg-ℤ

equiv-neg-ℤ : ℤ ≃ ℤ
pr1 equiv-neg-ℤ = neg-ℤ
pr2 equiv-neg-ℤ = is-equiv-neg-ℤ

-- We show that succ-Fin k is an equivalence

is-equiv-succ-Fin : {k : ℕ} → is-equiv (succ-Fin {k})
pr1 (pr1 is-equiv-succ-Fin) = pred-Fin
pr2 (pr1 is-equiv-succ-Fin) = succ-pred-Fin
pr1 (pr2 is-equiv-succ-Fin) = pred-Fin
pr2 (pr2 is-equiv-succ-Fin) = pred-succ-Fin

equiv-succ-Fin : {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-succ-Fin = succ-Fin
pr2 equiv-succ-Fin = is-equiv-succ-Fin

-- We show that pred-Fin k is an equivalence

is-equiv-pred-Fin : {k : ℕ} → is-equiv (pred-Fin {k})
pr1 (pr1 is-equiv-pred-Fin) = succ-Fin
pr2 (pr1 is-equiv-pred-Fin) = pred-succ-Fin
pr1 (pr2 is-equiv-pred-Fin) = succ-Fin
pr2 (pr2 is-equiv-pred-Fin) = succ-pred-Fin

equiv-pred-Fin : {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-pred-Fin = pred-Fin
pr2 equiv-pred-Fin = is-equiv-pred-Fin

-- We show that add-Fin k x is an equivalence

is-equiv-add-Fin :
  {k : ℕ} (x : Fin k) → is-equiv (add-Fin x)
pr1 (pr1 (is-equiv-add-Fin x)) = add-Fin (neg-Fin x)
pr2 (pr1 (is-equiv-add-Fin x)) = add-add-neg-Fin x
pr1 (pr2 (is-equiv-add-Fin x)) = add-Fin (neg-Fin x)
pr2 (pr2 (is-equiv-add-Fin x)) = add-neg-add-Fin x

equiv-add-Fin :
  {k : ℕ} (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin x) = add-Fin x
pr2 (equiv-add-Fin x) = is-equiv-add-Fin x

-- We show that add-Fin' k y is an equivalence

add-add-neg-Fin' :
  {k : ℕ} (x y : Fin k) → Id (add-Fin' x (add-Fin' (neg-Fin x) y)) y
add-add-neg-Fin' {succ-ℕ k} x y =
  ( associative-add-Fin y (neg-Fin x) x) ∙
  ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
    ( right-unit-law-add-Fin y))

add-neg-add-Fin' :
  {k : ℕ} (x y : Fin k) → Id (add-Fin' (neg-Fin x) (add-Fin' x y)) y
add-neg-add-Fin' {succ-ℕ k} x y =
  ( associative-add-Fin y x (neg-Fin x)) ∙
  ( ( ap (add-Fin y) (right-inverse-law-add-Fin x)) ∙
    ( right-unit-law-add-Fin y))

is-equiv-add-Fin' :
  {k : ℕ} (x : Fin k) → is-equiv (add-Fin' x)
pr1 (pr1 (is-equiv-add-Fin' x)) = add-Fin' (neg-Fin x)
pr2 (pr1 (is-equiv-add-Fin' x)) = add-add-neg-Fin' x
pr1 (pr2 (is-equiv-add-Fin' x)) = add-Fin' (neg-Fin x)
pr2 (pr2 (is-equiv-add-Fin' x)) = add-neg-add-Fin' x

equiv-add-Fin' :
  {k : ℕ} (x : Fin k) → Fin k ≃ Fin k
pr1 (equiv-add-Fin' x) = add-Fin' x
pr2 (equiv-add-Fin' x) = is-equiv-add-Fin' x

-- We show that neg-Fin k is an equivalence

neg-neg-Fin :
  {k : ℕ} (x : Fin k) → Id (neg-Fin (neg-Fin x)) x
neg-neg-Fin {succ-ℕ k} x =
  ( inv (right-unit-law-add-Fin (neg-Fin (neg-Fin x)))) ∙
  ( ( ap (add-Fin (neg-Fin (neg-Fin x))) (inv (left-inverse-law-add-Fin x))) ∙
    ( ( inv (associative-add-Fin (neg-Fin (neg-Fin x)) (neg-Fin x) x)) ∙
      ( ( ap (add-Fin' x) (left-inverse-law-add-Fin (neg-Fin x))) ∙
        ( left-unit-law-add-Fin x))))

is-equiv-neg-Fin :
  {k : ℕ} → is-equiv (neg-Fin {k})
pr1 (pr1 is-equiv-neg-Fin) = neg-Fin
pr2 (pr1 is-equiv-neg-Fin) = neg-neg-Fin
pr1 (pr2 is-equiv-neg-Fin) = neg-Fin
pr2 (pr2 is-equiv-neg-Fin) = neg-neg-Fin

equiv-neg-Fin :
  {k : ℕ} → Fin k ≃ Fin k
pr1 equiv-neg-Fin = neg-Fin
pr2 equiv-neg-Fin = is-equiv-neg-Fin

-- Further examples

is-equiv-nat-nonnegative-ℤ : is-equiv nat-nonnegative-ℤ
pr1 (pr1 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr1 is-equiv-nat-nonnegative-ℤ) = isretr-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nat-nonnegative-ℤ) = nonnegative-int-ℕ
pr2 (pr2 is-equiv-nat-nonnegative-ℤ) = issec-nat-nonnegative-ℤ

is-equiv-nonnegative-int-ℕ : is-equiv nonnegative-int-ℕ
pr1 (pr1 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr1 is-equiv-nonnegative-int-ℕ) = issec-nat-nonnegative-ℤ
pr1 (pr2 is-equiv-nonnegative-int-ℕ) = nat-nonnegative-ℤ
pr2 (pr2 is-equiv-nonnegative-int-ℕ) = isretr-nat-nonnegative-ℤ

equiv-nonnegative-int-ℕ : ℕ ≃ nonnegative-ℤ
pr1 equiv-nonnegative-int-ℕ = nonnegative-int-ℕ
pr2 equiv-nonnegative-int-ℕ = is-equiv-nonnegative-int-ℕ

-- Remark 9.2.6

has-inverse :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
has-inverse {i} {j} {A} {B} f =
  Σ (B → A) (λ g → ((f ∘ g) ~ id) × ((g ∘ f) ~ id))

-- Proposition 9.2.7

is-equiv-has-inverse' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  has-inverse f → is-equiv f
pr1 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = g
pr2 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = H
pr1 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = g
pr2 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = K

is-equiv-has-inverse :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
is-equiv-has-inverse g H K =
  is-equiv-has-inverse' (pair g (pair H K))

-- Corollary 9.2.8

htpy-section-retraction :
  { i j : Level} {A : UU i} {B : UU j} {f : A → B}
  ( is-equiv-f : is-equiv f) →
  ( (pr1 (pr1 is-equiv-f))) ~ (pr1 (pr2 is-equiv-f))
htpy-section-retraction {i} {j} {A} {B} {f} (pair (pair g G) (pair h H)) =
    (inv-htpy (H ·r g)) ∙h (h ·l G)

has-inverse-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-equiv f → has-inverse f
pr1
  ( has-inverse-is-equiv {i} {j} {A} {B} {f}
    ( pair (pair g G) (pair h H))) = g
pr1
  ( pr2
    ( has-inverse-is-equiv {i} {j} {A} {B} {f}
      ( pair (pair g G) (pair h H)))) = G
pr2
  ( pr2
    ( has-inverse-is-equiv {i} {j} {A} {B} {f}
      ( pair (pair g G) (pair h H)))) =
  (((inv-htpy (H ·r g)) ∙h (h ·l G)) ·r f) ∙h H

map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → B → A
map-inv-is-equiv is-equiv-f = pr1 (has-inverse-is-equiv is-equiv-f)

issec-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → (f ∘ (map-inv-is-equiv is-equiv-f)) ~ id
issec-map-inv-is-equiv' is-equiv-f = pr1 (pr2 (has-inverse-is-equiv is-equiv-f))

isretr-map-inv-is-equiv' :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → ((map-inv-is-equiv is-equiv-f) ∘ f) ~ id
isretr-map-inv-is-equiv' is-equiv-f =
  pr2 (pr2 (has-inverse-is-equiv is-equiv-f))

is-equiv-map-inv-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  (is-equiv-f : is-equiv f) → is-equiv (map-inv-is-equiv is-equiv-f)
is-equiv-map-inv-is-equiv {i} {j} {A} {B} {f} is-equiv-f =
  is-equiv-has-inverse f
    ( isretr-map-inv-is-equiv' is-equiv-f)
    ( issec-map-inv-is-equiv' is-equiv-f)

map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B → A)
map-inv-equiv' e = map-inv-is-equiv (is-equiv-map-equiv e)

issec-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-equiv e) ∘ (map-inv-equiv' e)) ~ id
issec-map-inv-equiv' e = issec-map-inv-is-equiv' (is-equiv-map-equiv e)

isretr-map-inv-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  ((map-inv-equiv' e) ∘ (map-equiv e)) ~ id
isretr-map-inv-equiv' e = isretr-map-inv-is-equiv' (is-equiv-map-equiv e)

is-equiv-map-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) → is-equiv (map-inv-equiv' e)
is-equiv-map-inv-equiv e =
  is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (B ≃ A)
pr1 (inv-equiv e) = map-inv-equiv' e
pr2 (inv-equiv e) = is-equiv-map-inv-equiv e

-- Equivalences are injective

is-injective-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-injective f
is-injective-is-equiv {l1} {l2} {A} {B} {f} H {x} {y} p =
  ( inv (isretr-map-inv-is-equiv' H x)) ∙
  ( ( ap (map-inv-is-equiv H) p) ∙
    ( isretr-map-inv-is-equiv' H y))

abstract
  is-injective-map-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (e : A ≃ B) → is-injective (map-equiv e)
  is-injective-map-equiv (pair f H) = is-injective-is-equiv H

abstract
  is-injective-map-inv-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    (e : A ≃ B) → is-injective (map-inv-equiv' e)
  is-injective-map-inv-equiv e =
    is-injective-is-equiv (is-equiv-map-inv-equiv e)

is-equiv-is-injective :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  sec f → is-injective f → is-equiv f
is-equiv-is-injective {f = f} (pair g G) H =
  is-equiv-has-inverse g G (λ x → H (G (f x)))

-- Remarks

-- Left unit law of coproducts

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty A)
  where

  map-inv-left-unit-law-coprod-is-empty : B → coprod A B
  map-inv-left-unit-law-coprod-is-empty = inr

  issec-map-inv-left-unit-law-coprod-is-empty :
    ( map-left-unit-law-coprod-is-empty A B H ∘
      map-inv-left-unit-law-coprod-is-empty) ~ id
  issec-map-inv-left-unit-law-coprod-is-empty = refl-htpy

  isretr-map-inv-left-unit-law-coprod-is-empty :
    ( map-inv-left-unit-law-coprod-is-empty ∘
      map-left-unit-law-coprod-is-empty A B H) ~ id
  isretr-map-inv-left-unit-law-coprod-is-empty (inl a) = ex-falso (H a)
  isretr-map-inv-left-unit-law-coprod-is-empty (inr b) = refl

  is-equiv-map-left-unit-law-coprod-is-empty :
    is-equiv (map-left-unit-law-coprod-is-empty A B H)
  is-equiv-map-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-left-unit-law-coprod-is-empty
      issec-map-inv-left-unit-law-coprod-is-empty
      isretr-map-inv-left-unit-law-coprod-is-empty

  left-unit-law-coprod-is-empty : coprod A B ≃ B
  pr1 left-unit-law-coprod-is-empty = map-left-unit-law-coprod-is-empty A B H
  pr2 left-unit-law-coprod-is-empty = is-equiv-map-left-unit-law-coprod-is-empty

  inv-left-unit-law-coprod-is-empty : B ≃ coprod A B
  pr1 inv-left-unit-law-coprod-is-empty = map-inv-left-unit-law-coprod-is-empty
  pr2 inv-left-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-left-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-left-unit-law-coprod-is-empty)
      ( issec-map-inv-left-unit-law-coprod-is-empty)

module _
  {l : Level} (B : UU l)
  where

  map-left-unit-law-coprod : coprod empty B → B
  map-left-unit-law-coprod = map-left-unit-law-coprod-is-empty empty B id

  map-inv-left-unit-law-coprod : B → coprod empty B
  map-inv-left-unit-law-coprod = inr

  issec-map-inv-left-unit-law-coprod :
    ( map-left-unit-law-coprod ∘ map-inv-left-unit-law-coprod) ~ id
  issec-map-inv-left-unit-law-coprod =
    issec-map-inv-left-unit-law-coprod-is-empty empty B id

  isretr-map-inv-left-unit-law-coprod :
    ( map-inv-left-unit-law-coprod ∘ map-left-unit-law-coprod) ~ id
  isretr-map-inv-left-unit-law-coprod =
    isretr-map-inv-left-unit-law-coprod-is-empty empty B id

  is-equiv-map-left-unit-law-coprod : is-equiv map-left-unit-law-coprod
  is-equiv-map-left-unit-law-coprod =
    is-equiv-map-left-unit-law-coprod-is-empty empty B id
  
  left-unit-law-coprod : coprod empty B ≃ B
  left-unit-law-coprod = left-unit-law-coprod-is-empty empty B id

  inv-left-unit-law-coprod : B ≃ (coprod empty B)
  inv-left-unit-law-coprod = inv-left-unit-law-coprod-is-empty empty B id

-- The right unit law for coproducts

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (H : is-empty B)
  where
  
  map-inv-right-unit-law-coprod-is-empty : A → coprod A B
  map-inv-right-unit-law-coprod-is-empty = inl

  issec-map-inv-right-unit-law-coprod-is-empty :
    ( map-right-unit-law-coprod-is-empty A B H ∘
      map-inv-right-unit-law-coprod-is-empty) ~ id
  issec-map-inv-right-unit-law-coprod-is-empty a = refl

  isretr-map-inv-right-unit-law-coprod-is-empty :
    ( map-inv-right-unit-law-coprod-is-empty ∘
      map-right-unit-law-coprod-is-empty A B H) ~ id
  isretr-map-inv-right-unit-law-coprod-is-empty (inl a) = refl
  isretr-map-inv-right-unit-law-coprod-is-empty (inr b) = ex-falso (H b)

  is-equiv-map-right-unit-law-coprod-is-empty :
    is-equiv (map-right-unit-law-coprod-is-empty A B H)
  is-equiv-map-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      map-inv-right-unit-law-coprod-is-empty
      issec-map-inv-right-unit-law-coprod-is-empty
      isretr-map-inv-right-unit-law-coprod-is-empty

  is-equiv-inl-is-empty : is-equiv (inl {l1} {l2} {A} {B})
  is-equiv-inl-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

  right-unit-law-coprod-is-empty : coprod A B ≃ A
  pr1 right-unit-law-coprod-is-empty = map-right-unit-law-coprod-is-empty A B H
  pr2 right-unit-law-coprod-is-empty =
    is-equiv-map-right-unit-law-coprod-is-empty

  inv-right-unit-law-coprod-is-empty : A ≃ (coprod A B)
  pr1 inv-right-unit-law-coprod-is-empty = inl
  pr2 inv-right-unit-law-coprod-is-empty =
    is-equiv-has-inverse
      ( map-right-unit-law-coprod-is-empty A B H)
      ( isretr-map-inv-right-unit-law-coprod-is-empty)
      ( issec-map-inv-right-unit-law-coprod-is-empty)

module _
  {l : Level} (A : UU l)
  where

  map-right-unit-law-coprod : coprod A empty → A
  map-right-unit-law-coprod = map-right-unit-law-coprod-is-empty A empty id

  map-inv-right-unit-law-coprod : A → coprod A empty
  map-inv-right-unit-law-coprod = inl

  issec-map-inv-right-unit-law-coprod :
    ( map-right-unit-law-coprod ∘ map-inv-right-unit-law-coprod) ~ id
  issec-map-inv-right-unit-law-coprod =
    issec-map-inv-right-unit-law-coprod-is-empty A empty id

  isretr-map-inv-right-unit-law-coprod :
    ( map-inv-right-unit-law-coprod ∘ map-right-unit-law-coprod) ~ id
  isretr-map-inv-right-unit-law-coprod =
    isretr-map-inv-right-unit-law-coprod-is-empty A empty id

  is-equiv-map-right-unit-law-coprod : is-equiv map-right-unit-law-coprod
  is-equiv-map-right-unit-law-coprod =
    is-equiv-map-right-unit-law-coprod-is-empty A empty id

  right-unit-law-coprod : coprod A empty ≃ A
  right-unit-law-coprod = right-unit-law-coprod-is-empty A empty id

  inv-right-unit-law-coprod : A ≃ coprod A empty
  inv-right-unit-law-coprod =
    inv-right-unit-law-coprod-is-empty A empty id

-- Commutativity of coproducts

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  map-commutative-coprod : coprod A B → coprod B A
  map-commutative-coprod (inl a) = inr a
  map-commutative-coprod (inr b) = inl b
  
  map-inv-commutative-coprod : coprod B A → coprod A B
  map-inv-commutative-coprod (inl b) = inr b
  map-inv-commutative-coprod (inr a) = inl a
  
  issec-map-inv-commutative-coprod :
    ( map-commutative-coprod ∘ map-inv-commutative-coprod) ~ id
  issec-map-inv-commutative-coprod (inl b) = refl
  issec-map-inv-commutative-coprod (inr a) = refl
  
  isretr-map-inv-commutative-coprod :
    ( map-inv-commutative-coprod ∘ map-commutative-coprod) ~ id
  isretr-map-inv-commutative-coprod (inl a) = refl
  isretr-map-inv-commutative-coprod (inr b) = refl

  is-equiv-map-commutative-coprod : is-equiv map-commutative-coprod
  is-equiv-map-commutative-coprod =
    is-equiv-has-inverse
      map-inv-commutative-coprod
      issec-map-inv-commutative-coprod
      isretr-map-inv-commutative-coprod

-- Associativity of coproducts

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where
  
  map-assoc-coprod : coprod (coprod A B) C → coprod A (coprod B C)
  map-assoc-coprod (inl (inl x)) = inl x
  map-assoc-coprod (inl (inr x)) = inr (inl x)
  map-assoc-coprod (inr x) = inr (inr x)

  map-inv-assoc-coprod : coprod A (coprod B C) → coprod (coprod A B) C
  map-inv-assoc-coprod (inl x) = inl (inl x)
  map-inv-assoc-coprod (inr (inl x)) = inl (inr x)
  map-inv-assoc-coprod (inr (inr x)) = inr x

  issec-map-inv-assoc-coprod : (map-assoc-coprod ∘ map-inv-assoc-coprod) ~ id
  issec-map-inv-assoc-coprod (inl x) = refl
  issec-map-inv-assoc-coprod (inr (inl x)) = refl
  issec-map-inv-assoc-coprod (inr (inr x)) = refl

  isretr-map-inv-assoc-coprod : (map-inv-assoc-coprod ∘ map-assoc-coprod) ~ id
  isretr-map-inv-assoc-coprod (inl (inl x)) = refl
  isretr-map-inv-assoc-coprod (inl (inr x)) = refl
  isretr-map-inv-assoc-coprod (inr x) = refl

  is-equiv-map-assoc-coprod : is-equiv map-assoc-coprod
  is-equiv-map-assoc-coprod =
    is-equiv-has-inverse
      map-inv-assoc-coprod
      issec-map-inv-assoc-coprod
      isretr-map-inv-assoc-coprod

  is-equiv-map-inv-assoc-coprod : is-equiv map-inv-assoc-coprod
  is-equiv-map-inv-assoc-coprod =
    is-equiv-has-inverse
      map-assoc-coprod
      isretr-map-inv-assoc-coprod
      issec-map-inv-assoc-coprod

  assoc-coprod : coprod (coprod A B) C ≃ coprod A (coprod B C)
  pr1 assoc-coprod = map-assoc-coprod
  pr2 assoc-coprod = is-equiv-map-assoc-coprod
  
  inv-assoc-coprod : coprod A (coprod B C) ≃ coprod (coprod A B) C
  pr1 inv-assoc-coprod = map-inv-assoc-coprod
  pr2 inv-assoc-coprod = is-equiv-map-inv-assoc-coprod

{- We prove a left zero law for cartesian products. -}

module _
  {l : Level} (X : UU l)
  where

  inv-pr1-prod-empty : empty → empty × X
  inv-pr1-prod-empty ()

  issec-inv-pr1-prod-empty : (pr1 ∘ inv-pr1-prod-empty) ~ id
  issec-inv-pr1-prod-empty ()

  isretr-inv-pr1-prod-empty : (inv-pr1-prod-empty ∘ pr1) ~ id
  isretr-inv-pr1-prod-empty (pair () x)

  is-equiv-pr1-prod-empty : is-equiv (pr1 {A = empty} {B = λ t → X})
  is-equiv-pr1-prod-empty =
    is-equiv-has-inverse
      inv-pr1-prod-empty
      issec-inv-pr1-prod-empty
      isretr-inv-pr1-prod-empty

  left-zero-law-prod : (empty × X) ≃ empty
  pr1 left-zero-law-prod = pr1
  pr2 left-zero-law-prod = is-equiv-pr1-prod-empty

{- We prove the right zero law for cartesian products. -}

module _
  {l : Level} (X : UU l)
  where

  inv-pr2-prod-empty : empty → (X × empty)
  inv-pr2-prod-empty ()

  issec-inv-pr2-prod-empty : (pr2 ∘ inv-pr2-prod-empty) ~ id
  issec-inv-pr2-prod-empty ()

  isretr-inv-pr2-prod-empty : (inv-pr2-prod-empty ∘ pr2) ~ id
  isretr-inv-pr2-prod-empty (pair x ())

  is-equiv-pr2-prod-empty : is-equiv (pr2 {A = X} {B = λ x → empty})
  is-equiv-pr2-prod-empty =
    is-equiv-has-inverse
      inv-pr2-prod-empty
      issec-inv-pr2-prod-empty
      isretr-inv-pr2-prod-empty

  right-zero-law-prod : (X × empty) ≃ empty
  pr1 right-zero-law-prod = pr2
  pr2 right-zero-law-prod = is-equiv-pr2-prod-empty

-- Right absorption law for Σ-types and cartesian products

abstract
  is-equiv-is-empty :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-empty B → is-equiv f
  is-equiv-is-empty f H =
    is-equiv-has-inverse
      ( ex-falso ∘ H)
      ( λ y → ex-falso (H y))
      ( λ x → ex-falso (H (f x)))

abstract
  is-equiv-is-empty' :
    {l : Level} {A : UU l} (f : is-empty A) → is-equiv f
  is-equiv-is-empty' f = is-equiv-is-empty f id

module _
  {l : Level} (A : UU l)
  where
  
  map-right-absorption-Σ : Σ A (λ x → empty) → empty
  map-right-absorption-Σ (pair x ())
  
  map-right-absorption-prod : A × empty → empty
  map-right-absorption-prod = map-right-absorption-Σ

  is-equiv-map-right-absorption-Σ : is-equiv map-right-absorption-Σ
  is-equiv-map-right-absorption-Σ = is-equiv-is-empty' map-right-absorption-Σ

  is-equiv-map-right-absorption-prod : is-equiv map-right-absorption-prod
  is-equiv-map-right-absorption-prod = is-equiv-map-right-absorption-Σ
  
  right-absorption-Σ : Σ A (λ x → empty) ≃ empty
  right-absorption-Σ =
    pair map-right-absorption-Σ is-equiv-map-right-absorption-Σ
  
  right-absorption-prod : (A × empty) ≃ empty
  right-absorption-prod = right-absorption-Σ

-- Left absorption law for Σ and cartesian products

module _
  {l : Level} (A : empty → UU l)
  where

  map-left-absorption-Σ : Σ empty A → empty
  map-left-absorption-Σ = pr1
  
  is-equiv-map-left-absorption-Σ : is-equiv map-left-absorption-Σ
  is-equiv-map-left-absorption-Σ =
    is-equiv-is-empty' map-left-absorption-Σ
  
  left-absorption-Σ : Σ empty A ≃ empty
  pr1 left-absorption-Σ = map-left-absorption-Σ
  pr2 left-absorption-Σ = is-equiv-map-left-absorption-Σ

module _
  {l : Level} (A : UU l)
  where

  map-left-absorption-prod : empty × A → empty
  map-left-absorption-prod = map-left-absorption-Σ (λ x → A)
  
  is-equiv-map-left-absorption-prod : is-equiv map-left-absorption-prod
  is-equiv-map-left-absorption-prod =
    is-equiv-map-left-absorption-Σ (λ x → A)
    
  left-absorption-prod : (empty × A) ≃ empty
  left-absorption-prod = left-absorption-Σ (λ x → A)
  
-- Unit laws for Σ-types and cartesian products

module _
  {l : Level} (A : unit → UU l)
  where

  map-left-unit-law-Σ : Σ unit A → A star
  map-left-unit-law-Σ (pair star a) = a

  map-inv-left-unit-law-Σ : A star → Σ unit A
  pr1 (map-inv-left-unit-law-Σ a) = star
  pr2 (map-inv-left-unit-law-Σ a) = a

  issec-map-inv-left-unit-law-Σ :
    ( map-left-unit-law-Σ ∘ map-inv-left-unit-law-Σ) ~ id
  issec-map-inv-left-unit-law-Σ a = refl

  isretr-map-inv-left-unit-law-Σ :
    ( map-inv-left-unit-law-Σ ∘ map-left-unit-law-Σ) ~ id
  isretr-map-inv-left-unit-law-Σ (pair star a) = refl

  is-equiv-map-left-unit-law-Σ : is-equiv map-left-unit-law-Σ
  is-equiv-map-left-unit-law-Σ =
    is-equiv-has-inverse
      map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ

  left-unit-law-Σ : Σ unit A ≃ A star
  pr1 left-unit-law-Σ = map-left-unit-law-Σ
  pr2 left-unit-law-Σ = is-equiv-map-left-unit-law-Σ
  
  is-equiv-map-inv-left-unit-law-Σ : is-equiv map-inv-left-unit-law-Σ
  is-equiv-map-inv-left-unit-law-Σ =
    is-equiv-has-inverse
      map-left-unit-law-Σ
      isretr-map-inv-left-unit-law-Σ
      issec-map-inv-left-unit-law-Σ

  inv-left-unit-law-Σ : A star ≃ Σ unit A
  pr1 inv-left-unit-law-Σ = map-inv-left-unit-law-Σ
  pr2 inv-left-unit-law-Σ = is-equiv-map-inv-left-unit-law-Σ

module _
  {l : Level} {A : UU l}
  where

  map-left-unit-law-prod : unit × A → A
  map-left-unit-law-prod = pr2

  map-inv-left-unit-law-prod : A → unit × A
  map-inv-left-unit-law-prod = map-inv-left-unit-law-Σ (λ x → A)

  issec-map-inv-left-unit-law-prod :
    ( map-left-unit-law-prod ∘ map-inv-left-unit-law-prod) ~ id
  issec-map-inv-left-unit-law-prod =
    issec-map-inv-left-unit-law-Σ (λ x → A)

  isretr-map-inv-left-unit-law-prod :
    ( map-inv-left-unit-law-prod ∘ map-left-unit-law-prod) ~ id
  isretr-map-inv-left-unit-law-prod (pair star a) = refl

  is-equiv-map-left-unit-law-prod : is-equiv map-left-unit-law-prod
  is-equiv-map-left-unit-law-prod =
    is-equiv-has-inverse
      map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod

  left-unit-law-prod : (unit × A) ≃ A
  pr1 left-unit-law-prod = map-left-unit-law-prod
  pr2 left-unit-law-prod = is-equiv-map-left-unit-law-prod

  is-equiv-map-inv-left-unit-law-prod : is-equiv map-inv-left-unit-law-prod
  is-equiv-map-inv-left-unit-law-prod =
    is-equiv-has-inverse
      map-left-unit-law-prod
      isretr-map-inv-left-unit-law-prod
      issec-map-inv-left-unit-law-prod

  inv-left-unit-law-prod : A ≃ (unit × A)
  pr1 inv-left-unit-law-prod = map-inv-left-unit-law-prod
  pr2 inv-left-unit-law-prod = is-equiv-map-inv-left-unit-law-prod

  map-right-unit-law-prod : A × unit → A
  map-right-unit-law-prod = pr1

  map-inv-right-unit-law-prod : A → A × unit
  pr1 (map-inv-right-unit-law-prod a) = a
  pr2 (map-inv-right-unit-law-prod a) = star

  issec-map-inv-right-unit-law-prod :
    (map-right-unit-law-prod ∘ map-inv-right-unit-law-prod) ~ id
  issec-map-inv-right-unit-law-prod a = refl

  isretr-map-inv-right-unit-law-prod :
    (map-inv-right-unit-law-prod ∘ map-right-unit-law-prod) ~ id
  isretr-map-inv-right-unit-law-prod (pair a star) = refl

  is-equiv-map-right-unit-law-prod : is-equiv map-right-unit-law-prod
  is-equiv-map-right-unit-law-prod =
    is-equiv-has-inverse
      map-inv-right-unit-law-prod
      issec-map-inv-right-unit-law-prod
      isretr-map-inv-right-unit-law-prod

  right-unit-law-prod : (A × unit) ≃ A
  pr1 right-unit-law-prod = map-right-unit-law-prod
  pr2 right-unit-law-prod = is-equiv-map-right-unit-law-prod

-- Associativity of Σ-types

triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
pr1 (triple a b c) = a
pr1 (pr2 (triple a b c)) = b
pr2 (pr2 (triple a b c)) = c

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
pr1 (pr1 (triple' a b c)) = a
pr2 (pr1 (triple' a b c)) = b
pr2 (triple' a b c) = c

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

-- Another way to phrase associativity of Σ-types.

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

-- Commutativity of cartesian products

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-commutative-prod : A × B → B × A
  pr1 (map-commutative-prod (pair a b)) = b
  pr2 (map-commutative-prod (pair a b)) = a
  
  map-inv-commutative-prod : B × A → A × B
  pr1 (map-inv-commutative-prod (pair b a)) = a
  pr2 (map-inv-commutative-prod (pair b a)) = b

  issec-map-inv-commutative-prod :
    (map-commutative-prod ∘ map-inv-commutative-prod) ~ id
  issec-map-inv-commutative-prod (pair b a) = refl

  isretr-map-inv-commutative-prod :
    (map-inv-commutative-prod ∘ map-commutative-prod) ~ id
  isretr-map-inv-commutative-prod (pair a b) = refl

  is-equiv-map-commutative-prod : is-equiv map-commutative-prod
  is-equiv-map-commutative-prod =
    is-equiv-has-inverse
      map-inv-commutative-prod
      issec-map-inv-commutative-prod
      isretr-map-inv-commutative-prod

  commutative-prod : (A × B) ≃ (B × A)
  pr1 commutative-prod = map-commutative-prod
  pr2 commutative-prod = is-equiv-map-commutative-prod

-- Associativity of cartesian products

module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where
  
  map-assoc-prod : (A × B) × C → A × (B × C)
  map-assoc-prod = map-assoc-Σ A (λ x → B) (λ w → C)

  map-inv-assoc-prod : A × (B × C) → (A × B) × C
  map-inv-assoc-prod = map-inv-assoc-Σ A (λ x → B) (λ w → C)

  issec-map-inv-assoc-prod : (map-assoc-prod ∘ map-inv-assoc-prod) ~ id
  issec-map-inv-assoc-prod = issec-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  isretr-map-inv-assoc-prod : (map-inv-assoc-prod ∘ map-assoc-prod) ~ id
  isretr-map-inv-assoc-prod = isretr-map-inv-assoc-Σ A (λ x → B) (λ w → C)

  is-equiv-map-assoc-prod : is-equiv map-assoc-prod
  is-equiv-map-assoc-prod = is-equiv-map-assoc-Σ A (λ x → B) (λ w → C)

  assoc-prod : ((A × B) × C) ≃ (A × (B × C))
  assoc-prod = assoc-Σ A (λ x → B) (λ w → C)

-- Right distributivity of Σ over coproducts

module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : coprod A B → UU l3)
  where
  
  map-right-distributive-Σ-coprod :
    Σ (coprod A B) C → coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  map-right-distributive-Σ-coprod (pair (inl x) z) = inl (pair x z)
  map-right-distributive-Σ-coprod (pair (inr y) z) = inr (pair y z)

  map-inv-right-distributive-Σ-coprod :
    coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y))) → Σ (coprod A B) C
  pr1 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = inl x
  pr2 (map-inv-right-distributive-Σ-coprod (inl (pair x z))) = z
  pr1 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = inr y
  pr2 (map-inv-right-distributive-Σ-coprod (inr (pair y z))) = z

  issec-map-inv-right-distributive-Σ-coprod :
    ( map-right-distributive-Σ-coprod ∘ map-inv-right-distributive-Σ-coprod) ~
    ( id)
  issec-map-inv-right-distributive-Σ-coprod (inl (pair x z)) = refl
  issec-map-inv-right-distributive-Σ-coprod (inr (pair y z)) = refl

  isretr-map-inv-right-distributive-Σ-coprod :
    ( map-inv-right-distributive-Σ-coprod ∘ map-right-distributive-Σ-coprod) ~
    ( id)
  isretr-map-inv-right-distributive-Σ-coprod (pair (inl x) z) = refl
  isretr-map-inv-right-distributive-Σ-coprod (pair (inr y) z) = refl

  abstract
    is-equiv-map-right-distributive-Σ-coprod :
      is-equiv map-right-distributive-Σ-coprod
    is-equiv-map-right-distributive-Σ-coprod =
      is-equiv-has-inverse
        map-inv-right-distributive-Σ-coprod
        issec-map-inv-right-distributive-Σ-coprod
        isretr-map-inv-right-distributive-Σ-coprod

  right-distributive-Σ-coprod :
    Σ (coprod A B) C ≃ coprod (Σ A (λ x → C (inl x))) (Σ B (λ y → C (inr y)))
  pr1 right-distributive-Σ-coprod = map-right-distributive-Σ-coprod
  pr2 right-distributive-Σ-coprod = is-equiv-map-right-distributive-Σ-coprod

-- Left distributivity of Σ over coproducts

module _
  {l1 l2 l3 : Level} (A : UU l1) (B : A → UU l2) (C : A → UU l3)
  where

  map-left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) → coprod (Σ A B) (Σ A C)
  map-left-distributive-Σ-coprod (pair x (inl y)) = inl (pair x y)
  map-left-distributive-Σ-coprod (pair x (inr z)) = inr (pair x z)

  map-inv-left-distributive-Σ-coprod :
    coprod (Σ A B) (Σ A C) → Σ A (λ x → coprod (B x) (C x))
  pr1 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inl (pair x y))) = inl y
  pr1 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = x
  pr2 (map-inv-left-distributive-Σ-coprod (inr (pair x z))) = inr z

  issec-map-inv-left-distributive-Σ-coprod :
    ( map-left-distributive-Σ-coprod ∘ map-inv-left-distributive-Σ-coprod) ~ id
  issec-map-inv-left-distributive-Σ-coprod (inl (pair x y)) = refl
  issec-map-inv-left-distributive-Σ-coprod (inr (pair x z)) = refl

  isretr-map-inv-left-distributive-Σ-coprod :
    ( map-inv-left-distributive-Σ-coprod ∘ map-left-distributive-Σ-coprod) ~ id
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inl y)) = refl
  isretr-map-inv-left-distributive-Σ-coprod (pair x (inr z)) = refl

  is-equiv-map-left-distributive-Σ-coprod :
    is-equiv map-left-distributive-Σ-coprod
  is-equiv-map-left-distributive-Σ-coprod =
    is-equiv-has-inverse
      map-inv-left-distributive-Σ-coprod
      issec-map-inv-left-distributive-Σ-coprod
      isretr-map-inv-left-distributive-Σ-coprod

  left-distributive-Σ-coprod :
    Σ A (λ x → coprod (B x) (C x)) ≃ coprod (Σ A B) (Σ A C)
  pr1 left-distributive-Σ-coprod = map-left-distributive-Σ-coprod
  pr2 left-distributive-Σ-coprod = is-equiv-map-left-distributive-Σ-coprod

-- Right distributivity of products over coproducts

module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-right-distributive-prod-coprod : (coprod A B) × C → coprod (A × C) (B × C)
  map-right-distributive-prod-coprod =
    map-right-distributive-Σ-coprod A B (λ x → C)

  map-inv-right-distributive-prod-coprod :
    coprod (A × C) (B × C) → (coprod A B) × C
  map-inv-right-distributive-prod-coprod =
    map-inv-right-distributive-Σ-coprod A B (λ x → C)

  issec-map-inv-right-distributive-prod-coprod :
    ( map-right-distributive-prod-coprod ∘
      map-inv-right-distributive-prod-coprod) ~ id
  issec-map-inv-right-distributive-prod-coprod =
    issec-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  isretr-map-inv-right-distributive-prod-coprod :
    ( map-inv-right-distributive-prod-coprod ∘
      map-right-distributive-prod-coprod) ~ id
  isretr-map-inv-right-distributive-prod-coprod =
    isretr-map-inv-right-distributive-Σ-coprod A B (λ x → C)

  abstract
    is-equiv-map-right-distributive-prod-coprod :
      is-equiv map-right-distributive-prod-coprod
    is-equiv-map-right-distributive-prod-coprod =
      is-equiv-map-right-distributive-Σ-coprod A B (λ x → C)
  
  right-distributive-prod-coprod : ((coprod A B) × C) ≃ coprod (A × C) (B × C)
  right-distributive-prod-coprod = right-distributive-Σ-coprod A B (λ x → C)

-- Left distributivity of products over coproducts

module _
  {l1 l2 l3 : Level} (A : UU l1) (B : UU l2) (C : UU l3)
  where

  map-left-distributive-prod-coprod : A × (coprod B C) → coprod (A × B) (A × C)
  map-left-distributive-prod-coprod =
    map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  map-inv-left-distributive-prod-coprod :
    coprod (A × B) (A × C) → A × (coprod B C)
  map-inv-left-distributive-prod-coprod =
    map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  issec-map-inv-left-distributive-prod-coprod :
    ( map-left-distributive-prod-coprod ∘
      map-inv-left-distributive-prod-coprod) ~ id
  issec-map-inv-left-distributive-prod-coprod =
    issec-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  isretr-map-inv-left-distributive-prod-coprod :
    ( map-inv-left-distributive-prod-coprod ∘
      map-left-distributive-prod-coprod) ~ id
  isretr-map-inv-left-distributive-prod-coprod =
    isretr-map-inv-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  is-equiv-map-left-distributive-prod-coprod :
    is-equiv map-left-distributive-prod-coprod
  is-equiv-map-left-distributive-prod-coprod =
    is-equiv-map-left-distributive-Σ-coprod A (λ x → B) (λ x → C)

  left-distributive-prod-coprod : (A × (coprod B C)) ≃ coprod (A × B) (A × C)
  left-distributive-prod-coprod =
    left-distributive-Σ-coprod A (λ x → B) (λ x → C)
  
-- Exercise 7.10

-- We define swap on the left

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : A → B → UU l3}
  where

  map-left-swap-Σ : Σ A (λ x → Σ B (C x)) → Σ B (λ y → Σ A (λ x → C x y))
  pr1 (map-left-swap-Σ (pair a (pair b c))) = b
  pr1 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = a
  pr2 (pr2 (map-left-swap-Σ (pair a (pair b c)))) = c
  -- pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  map-inv-left-swap-Σ :
    Σ B (λ y → Σ A (λ x → C x y)) → Σ A (λ x → Σ B (C x))
  pr1 (map-inv-left-swap-Σ (pair b (pair a c))) = a
  pr1 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = b
  pr2 (pr2 (map-inv-left-swap-Σ (pair b (pair a c)))) = c
  -- pair (pr1 (pr2 t)) (pair (pr1 t) (pr2 (pr2 t)))
  
  isretr-map-inv-left-swap-Σ : (map-inv-left-swap-Σ ∘ map-left-swap-Σ) ~ id
  isretr-map-inv-left-swap-Σ (pair a (pair b c)) = refl

  issec-map-inv-left-swap-Σ : (map-left-swap-Σ ∘ map-inv-left-swap-Σ) ~ id
  issec-map-inv-left-swap-Σ (pair b (pair a c)) = refl
  
  abstract
    is-equiv-map-left-swap-Σ : is-equiv map-left-swap-Σ
    is-equiv-map-left-swap-Σ =
      is-equiv-has-inverse
        map-inv-left-swap-Σ
        issec-map-inv-left-swap-Σ
        isretr-map-inv-left-swap-Σ
  
  equiv-left-swap-Σ : Σ A (λ a → Σ B (C a)) ≃ Σ B (λ b → Σ A (λ a → C a b))
  pr1 equiv-left-swap-Σ = map-left-swap-Σ
  pr2 equiv-left-swap-Σ = is-equiv-map-left-swap-Σ

-- We also define swap on the right

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  map-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) → Σ (Σ A C) (B ∘ pr1)
  map-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  map-inv-right-swap-Σ : Σ (Σ A C) (B ∘ pr1) → Σ (Σ A B) (C ∘ pr1)
  map-inv-right-swap-Σ t = pair (pair (pr1 (pr1 t)) (pr2 t)) (pr2 (pr1 t))

  issec-map-inv-right-swap-Σ : (map-right-swap-Σ ∘ map-inv-right-swap-Σ) ~ id
  issec-map-inv-right-swap-Σ (pair (pair x y) z) = refl

  isretr-map-inv-right-swap-Σ : (map-inv-right-swap-Σ ∘ map-right-swap-Σ) ~ id
  isretr-map-inv-right-swap-Σ (pair (pair x z) y) = refl

  is-equiv-map-right-swap-Σ : is-equiv map-right-swap-Σ
  is-equiv-map-right-swap-Σ =
    is-equiv-has-inverse
      map-inv-right-swap-Σ
      issec-map-inv-right-swap-Σ
      isretr-map-inv-right-swap-Σ

  equiv-right-swap-Σ : Σ (Σ A B) (C ∘ pr1) ≃ Σ (Σ A C) (B ∘ pr1)
  equiv-right-swap-Σ = pair map-right-swap-Σ is-equiv-map-right-swap-Σ

--------------------------------------------------------------------------------

-- Section 9.3 The identity type of a Σ-type

-- Definition 9.3.1

Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) → UU (i ⊔ j)
Eq-Σ {B = B} s t = Σ (Id (pr1 s) (pr1 t)) (λ α → Id (tr B α (pr2 s)) (pr2 t))

-- Lemma 9.3.2

reflexive-Eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s : Σ A B) → Eq-Σ s s
reflexive-Eq-Σ (pair a b) = pair refl refl

-- Definition 9.3.3

pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (Id s t) → Eq-Σ s t
pair-eq-Σ {s = s} refl = reflexive-Eq-Σ s

-- Theorem 9.3.4

eq-pair-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  (α : Id (pr1 s) (pr1 t)) → Id (tr B α (pr2 s)) (pr2 t) → Id s t
eq-pair-Σ {B = B} {pair x y} {pair .x .y} refl refl = refl

eq-pair-Σ' :
  {i j : Level} {A : UU i} {B : A → UU j} {s t : Σ A B} →
  Eq-Σ s t → Id s t
eq-pair-Σ' (pair α β) = eq-pair-Σ α β

isretr-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((pair-eq-Σ {s = s} {t}) ∘ (eq-pair-Σ' {s = s} {t})) ~ id {A = Eq-Σ s t}
isretr-pair-eq-Σ (pair x y) (pair .x .y) (pair refl refl) = refl

issec-pair-eq-Σ :
  {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
  ((eq-pair-Σ' {s = s} {t}) ∘ (pair-eq-Σ {s = s} {t})) ~ id
issec-pair-eq-Σ (pair x y) .(pair x y) refl = refl

abstract
  is-equiv-eq-pair-Σ :
    {i j : Level} {A : UU i} {B : A → UU j} (s t : Σ A B) →
    is-equiv (eq-pair-Σ' {s = s} {t})
  is-equiv-eq-pair-Σ s t =
    is-equiv-has-inverse
      ( pair-eq-Σ)
      ( issec-pair-eq-Σ s t)
      ( isretr-pair-eq-Σ s t)

equiv-eq-pair-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Eq-Σ s t ≃ Id s t
equiv-eq-pair-Σ s t = pair eq-pair-Σ' (is-equiv-eq-pair-Σ s t)

abstract
  is-equiv-pair-eq-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) →
    is-equiv (pair-eq-Σ {s = s} {t})
  is-equiv-pair-eq-Σ s t =
    is-equiv-has-inverse
      ( eq-pair-Σ')
      ( isretr-pair-eq-Σ s t)
      ( issec-pair-eq-Σ s t)

equiv-pair-eq-Σ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (s t : Σ A B) → Id s t ≃ Eq-Σ s t
equiv-pair-eq-Σ s t = pair pair-eq-Σ (is-equiv-pair-eq-Σ s t)

η-pair :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (t : Σ A B) →
  Id (pair (pr1 t) (pr2 t)) t
η-pair t = eq-pair-Σ refl refl

{- For our convenience, we repeat the above argument for cartesian products. -}

Eq-prod :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) → UU (i ⊔ j)
Eq-prod s t = (Id (pr1 s) (pr1 t)) × (Id (pr2 s) (pr2 t))

{- We also define a function eq-pair-Σ-triv, which is like eq-pair-Σ but simplified 
   for the case where B is just a type. -}

eq-pair' :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Eq-prod s t → Id s t
eq-pair' {s = pair x y} {pair .x .y} (pair refl refl) = refl

eq-pair :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id (pr1 s) (pr1 t) → Id (pr2 s) (pr2 t) → Id s t
eq-pair p q = eq-pair' (pair p q)

{- Ideally, we would use the 3-for-2 property of equivalences to show that 
   eq-pair-triv is an equivalence, using that eq-pair-Σ is an equivalence. 
   Indeed, there is an equivalence 
   
     (Id x x') × (Id y y') → Σ (Id x x') (λ p → Id (tr (λ x → B) p y) y'). 

   However, to show that this map is an equivalence we either give a direct 
   proof (in which case we might as well have given a direct proof that 
   eq-pair-triv is an equivalence), or we use the fact that it is the induced 
   map on total spaces of a fiberwise equivalence (the topic of Lecture 8). 
   Thus it seems that a direct proof showing that eq-pair-triv is an 
   equivalence is quickest for now. -}

pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  Id s t → Eq-prod s t
pair-eq α = pair (ap pr1 α) (ap pr2 α)

isretr-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((pair-eq {s = s} {t}) ∘ (eq-pair' {s = s} {t})) ~ id
isretr-pair-eq {s = pair x y} {pair .x .y} (pair refl refl) = refl

issec-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} {s t : prod A B} →
  ((eq-pair' {s = s} {t}) ∘ (pair-eq {s = s} {t})) ~ id
issec-pair-eq {s = pair x y} {pair .x .y} refl = refl

abstract
  is-equiv-eq-pair :
    {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
    is-equiv (eq-pair' {s = s} {t})
  is-equiv-eq-pair s t =
    is-equiv-has-inverse pair-eq issec-pair-eq isretr-pair-eq

equiv-eq-pair :
  {i j : Level} {A : UU i} {B : UU j} (s t : prod A B) →
  Eq-prod s t ≃ Id s t
equiv-eq-pair s t = pair eq-pair' (is-equiv-eq-pair s t)

abstract
  is-equiv-pair-eq :
    {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
    is-equiv (pair-eq {s = s} {t})
  is-equiv-pair-eq s t =
    is-equiv-has-inverse eq-pair' isretr-pair-eq issec-pair-eq

equiv-pair-eq :
  {i j : Level} {A : UU i} {B : UU j} (s t : A × B) →
  Id s t ≃ Eq-prod s t
equiv-pair-eq s t = pair pair-eq (is-equiv-pair-eq s t)

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 9.1

{- We show that inv is an equivalence. -}

inv-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (inv (inv p)) p
inv-inv refl = refl

abstract
  is-equiv-inv :
    {i : Level} {A : UU i} (x y : A) →
    is-equiv (λ (p : Id x y) → inv p)
  is-equiv-inv x y =
    is-equiv-has-inverse inv inv-inv inv-inv

equiv-inv :
  {i : Level} {A : UU i} (x y : A) → (Id x y) ≃ (Id y x)
equiv-inv x y = pair inv (is-equiv-inv x y)

{- We show that concat p is an equivalence, for any path p. -}

inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  (Id x z) → (Id y z)
inv-concat p = concat (inv p)

isretr-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((inv-concat p z) ∘ (concat p z)) ~ id
isretr-inv-concat refl z q = refl

issec-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  ((concat p z) ∘ (inv-concat p z)) ~ id
issec-inv-concat refl z refl = refl

abstract
  is-equiv-concat :
    {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
    is-equiv (concat p z)
  is-equiv-concat p z =
    is-equiv-has-inverse
      ( inv-concat p z)
      ( issec-inv-concat p z)
      ( isretr-inv-concat p z)

equiv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) (z : A) →
  Id y z ≃ Id x z
equiv-concat p z = pair (concat p z) (is-equiv-concat p z)

{- We show that concat' q is an equivalence, for any path q. -}

concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z → Id x y → Id x z
concat' x q p = p ∙ q

inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} → Id y z →
  Id x z → Id x y
inv-concat' x q = concat' x (inv q)

isretr-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((inv-concat' x q) ∘ (concat' x q)) ~ id
isretr-inv-concat' x refl refl = refl

issec-inv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  ((concat' x q) ∘ (inv-concat' x q)) ~ id
issec-inv-concat' x refl refl = refl

abstract
  is-equiv-concat' :
    {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
    is-equiv (concat' x q)
  is-equiv-concat' x q =
    is-equiv-has-inverse
      ( inv-concat' x q)
      ( issec-inv-concat' x q)
      ( isretr-inv-concat' x q)

equiv-concat' :
  {i : Level} {A : UU i} (x : A) {y z : A} (q : Id y z) →
  Id x y ≃ Id x z
equiv-concat' x q = pair (concat' x q) (is-equiv-concat' x q)

{- We show that tr B p is an equivalence, for an path p and any type family B.
   -}
   
inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} →
  Id x y → B y → B x
inv-tr B p = tr B (inv p)

isretr-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((inv-tr B p ) ∘ (tr B p)) ~ id
isretr-inv-tr B refl b = refl

issec-inv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → ((tr B p) ∘ (inv-tr B p)) ~ id
issec-inv-tr B refl b = refl

abstract
  is-equiv-tr :
    {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
    (p : Id x y) → is-equiv (tr B p)
  is-equiv-tr B p =
    is-equiv-has-inverse
      ( inv-tr B p)
      ( issec-inv-tr B p)
      ( isretr-inv-tr B p)

equiv-tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A}
  (p : Id x y) → (B x) ≃ (B y)
equiv-tr B p = pair (tr B p) (is-equiv-tr B p)

-- Exercise 9.2

abstract
  not-equiv-const :
    (b : bool) → ¬ (is-equiv (const bool bool b))
  not-equiv-const true (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (inv (issec false))
  not-equiv-const false (pair (pair s issec) (pair r isretr)) =
    neq-false-true-𝟚 (issec true)

-- Exercise 9.3

-- Exercise 9.3(a)

abstract
  is-equiv-htpy :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} (g : A → B) →
    f ~ g → is-equiv g → is-equiv f
  is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)) =
    pair
      ( pair gs ((H ·r gs) ∙h issec))
      ( pair gr ((gr ·l H) ∙h isretr))

is-equiv-htpy-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} (e : A ≃ B) →
  f ~ map-equiv e → is-equiv f
is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

abstract
  is-equiv-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {g : A → B} →
    f ~ g → is-equiv f → is-equiv g
  is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

is-equiv-htpy-equiv' :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) {g : A → B} →
  map-equiv e ~ g → is-equiv g
is-equiv-htpy-equiv' e H = is-equiv-htpy' (map-equiv e) H (is-equiv-map-equiv e)

-- Exercise 9.3(b)

inv-htpy-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f f' : A → B} (H : f ~ f') →
  (is-equiv-f : is-equiv f) (is-equiv-f' : is-equiv f') →
  (map-inv-is-equiv is-equiv-f) ~ (map-inv-is-equiv is-equiv-f')
inv-htpy-is-equiv H is-equiv-f is-equiv-f' b =
  ( inv
    ( isretr-map-inv-is-equiv' is-equiv-f' (map-inv-is-equiv is-equiv-f b))) ∙
  ( ap (map-inv-is-equiv is-equiv-f')
    ( ( inv (H (map-inv-is-equiv is-equiv-f b))) ∙
      ( issec-map-inv-is-equiv' is-equiv-f b)))

-- Exercise 9.4

-- Exercise 9.4(a)

{- Exercise 9.4 (a) asks to show that, given a commuting triangle f ~ g ∘ h and
   a section s of h, we get a new commuting triangle g ~ f ∘ s. Moreover, under
   the same assumptions it follows that f has a section if and only if g has a 
   section. -}

triangle-section :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (S : sec h) →
  g ~ (f ∘ (pr1 S))
triangle-section f g h H (pair s issec) =
  inv-htpy (( H ·r s) ∙h (g ·l issec))

section-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec f → sec g
section-comp f g h H sec-h sec-f =
  pair (h ∘ (pr1 sec-f)) ((inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f))

section-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  sec h → sec g → sec f
section-comp' f g h H sec-h sec-g =
  pair
    ( (pr1 sec-h) ∘ (pr1 sec-g))
    ( ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
      ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g))))

-- Exercise 9.4(b)

{- Exercise 9.4 (b) is dual to exercise 9.4 (a). It asks to show that, given a 
   commuting triangle f ~ g ∘ h and a retraction r of g, we get a new commuting
   triangle h ~ r ∘ f. Moreover, under these assumptions it also follows that f
   has a retraction if and only if h has a retraction. -}

triangle-retraction :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) (R : retr g) →
  h ~ ((pr1 R) ∘ f)
triangle-retraction f g h H (pair r isretr) =
  inv-htpy (( r ·l H) ∙h (isretr ·r h))

retraction-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr f → retr h
retraction-comp f g h H retr-g retr-f =
  pair
    ( (pr1 retr-f) ∘ g)
    ( (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f))

retraction-comp' :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  retr g → retr h → retr f
retraction-comp' f g h H retr-g retr-h =
  pair
    ( (pr1 retr-h) ∘ (pr1 retr-g))
    ( ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
      ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h)))

-- Exercise 9.4(c)

{- In Exercise 9.4 (c) we use the constructions of parts (a) and (b) to derive 
   the 3-for-2 property of equivalences. -}

abstract
  is-equiv-comp :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv h → is-equiv g → is-equiv f
  is-equiv-comp f g h H (pair sec-h retr-h) (pair sec-g retr-g) =
    pair
      ( section-comp' f g h H sec-h sec-g)
      ( retraction-comp' f g h H retr-g retr-h)

abstract
  is-equiv-comp' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv h → is-equiv g → is-equiv (g ∘ h)
  is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

equiv-comp :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
equiv-comp g h =
  pair ((pr1 g) ∘ (pr1 h)) (is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g))

_∘e_ :
  {i j k : Level} {A : UU i} {B : UU j} {X : UU k} →
  (B ≃ X) → (A ≃ B) → (A ≃ X)
_∘e_ = equiv-comp

abstract
  is-equiv-left-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv f → is-equiv h → is-equiv g
  is-equiv-left-factor f g h H
    ( pair sec-f retr-f)
    ( pair (pair sh sh-issec) retr-h) =
    pair
      ( section-comp f g h H (pair sh sh-issec) sec-f)
      ( retraction-comp' g f sh
        ( triangle-section f g h H (pair sh sh-issec))
        ( retr-f)
        ( pair h sh-issec))

abstract
  is-equiv-left-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor' g h =
    is-equiv-left-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-right-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    is-equiv g → is-equiv f → is-equiv h
  is-equiv-right-factor f g h H
    ( pair sec-g (pair rg rg-isretr))
    ( pair sec-f retr-f) =
    pair
      ( section-comp' h rg f
        ( triangle-retraction f g h H (pair rg rg-isretr))
        ( sec-f)
        ( pair g rg-isretr))
      ( retraction-comp f g h H (pair rg rg-isretr) retr-f)

abstract
  is-equiv-right-factor' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k} (g : B → X) (h : A → B) → 
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor' g h =
    is-equiv-right-factor (g ∘ h) g h refl-htpy

abstract
  is-equiv-is-section-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f → (f ∘ g) ~ id → is-equiv g
  is-equiv-is-section-is-equiv {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-factor id f g (inv-htpy H) is-equiv-f is-equiv-id

abstract
  is-equiv-is-retraction-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f  → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction-is-equiv {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-left-factor id g f (inv-htpy H) is-equiv-id is-equiv-f

-- Bureaucracy

is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor'
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-comp
      ( map-equiv j ∘ f)
      ( g)
      ( map-equiv i)
      ( H)
      ( is-equiv-map-equiv i)
      ( K))

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' {f = f} {g} i j H K =
  is-equiv-left-factor'
    ( g)
    ( map-equiv i)
    ( is-equiv-comp
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)

equiv-is-empty :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-empty A → is-empty B → A ≃ B
equiv-is-empty f g =
  ( inv-equiv (pair g (is-equiv-is-empty g id))) ∘e
  ( pair f (is-equiv-is-empty f id))

convert-eq-values-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → Id (f x) (f y) ≃ Id (g x) (g y)
convert-eq-values-htpy {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))
    
-- Exercise 9.5

-- Exercise 9.5 (a)

iterate : {l : Level} {X : UU l} → ℕ → (X → X) → (X → X)
iterate zero-ℕ f x = x
iterate (succ-ℕ k) f x = f (iterate k f x)

iterate-succ-ℕ :
  {l : Level} {X : UU l} (k : ℕ) (f : X → X) (x : X) →
  Id (iterate (succ-ℕ k) f x) (iterate k f (f x))
iterate-succ-ℕ zero-ℕ f x = refl
iterate-succ-ℕ (succ-ℕ k) f x = ap f (iterate-succ-ℕ k f x)

iterate-add-ℕ :
  {l : Level} {X : UU l} (k l : ℕ) (f : X → X) (x : X) →
  Id (iterate (add-ℕ k l) f x) (iterate k f (iterate l f x))
iterate-add-ℕ k zero-ℕ f x = refl
iterate-add-ℕ k (succ-ℕ l) f x =
  ap f (iterate-add-ℕ k l f x) ∙ iterate-succ-ℕ k f (iterate l f x)

iterate-iterate :
  {l : Level} {X : UU l} (k l : ℕ) (f : X → X) (x : X) →
  Id (iterate k f (iterate l f x)) (iterate l f (iterate k f x))
iterate-iterate k l f x =
  ( inv (iterate-add-ℕ k l f x)) ∙
  ( ( ap (λ t → iterate t f x) (commutative-add-ℕ k l)) ∙
    ( iterate-add-ℕ l k f x))

is-cyclic-map : {l : Level} {X : UU l} (f : X → X) → UU l
is-cyclic-map {l} {X} f = (x y : X) → Σ ℕ (λ k → Id (iterate k f x) y)

length-path-is-cyclic-map :
  {l : Level} {X : UU l} {f : X → X} → is-cyclic-map f → X → X → ℕ
length-path-is-cyclic-map H x y = pr1 (H x y)

eq-is-cyclic-map :
  {l : Level} {X : UU l} {f : X → X} (H : is-cyclic-map f) (x y : X) →
  Id (iterate (length-path-is-cyclic-map H x y) f x) y
eq-is-cyclic-map H x y = pr2 (H x y)

map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) → X → X
map-inv-is-cyclic-map f H x =
  iterate (length-path-is-cyclic-map H (f x) x) f x

issec-map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) →
  (f ∘ map-inv-is-cyclic-map f H) ~ id
issec-map-inv-is-cyclic-map f H x =
  ( iterate-succ-ℕ (length-path-is-cyclic-map H (f x) x) f x) ∙
  ( eq-is-cyclic-map H (f x) x)

isretr-map-inv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) (H : is-cyclic-map f) →
  (map-inv-is-cyclic-map f H ∘ f) ~ id
isretr-map-inv-is-cyclic-map f H x =
  ( ap ( iterate (length-path-is-cyclic-map H (f (f x)) (f x)) f ∘ f)
       ( inv (eq-is-cyclic-map H (f x) x))) ∙
  ( ( ap ( iterate (length-path-is-cyclic-map H (f (f x)) (f x)) f)
         ( iterate-succ-ℕ (length-path-is-cyclic-map H (f x) x) f (f x))) ∙
    ( ( iterate-iterate
        ( length-path-is-cyclic-map H (f (f x)) (f x))
        ( length-path-is-cyclic-map H (f x) x) f (f (f x))) ∙
      ( ( ap ( iterate (length-path-is-cyclic-map H (f x) x) f)
           ( eq-is-cyclic-map H (f (f x)) (f x))) ∙
        ( eq-is-cyclic-map H (f x) x))))

is-equiv-is-cyclic-map :
  {l : Level} {X : UU l} (f : X → X) → is-cyclic-map f → is-equiv f
is-equiv-is-cyclic-map f H =
  is-equiv-has-inverse
    ( map-inv-is-cyclic-map f H)
    ( issec-map-inv-is-cyclic-map f H)
    ( isretr-map-inv-is-cyclic-map f H)

-- Exercise 9.5 (b)

compute-iterate-succ-Fin :
  {k : ℕ} (n : ℕ) (x : Fin (succ-ℕ k)) →
  Id (iterate n succ-Fin x) (add-Fin x (mod-succ-ℕ k n))
compute-iterate-succ-Fin zero-ℕ x = inv (right-unit-law-add-Fin x)
compute-iterate-succ-Fin {k} (succ-ℕ n) x =
  ( ap succ-Fin (compute-iterate-succ-Fin n x)) ∙
  ( inv (right-successor-law-add-Fin x (mod-succ-ℕ k n)))

is-cyclic-succ-Fin : {k : ℕ} → is-cyclic-map (succ-Fin {k})
is-cyclic-succ-Fin {succ-ℕ k} x y =
  pair
    ( nat-Fin (add-Fin y (neg-Fin x)))
    ( ( compute-iterate-succ-Fin (nat-Fin (add-Fin y (neg-Fin x))) x) ∙
      ( ( ap (add-Fin x) (issec-nat-Fin (add-Fin y (neg-Fin x)))) ∙
        ( ( commutative-add-Fin x (add-Fin y (neg-Fin x))) ∙
          ( ( associative-add-Fin y (neg-Fin x) x) ∙
            ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
              ( right-unit-law-add-Fin y))))))

-- Exercise 9.6

{- In this exercise we construct an equivalence from A + B to B + A, showing 
   that the coproduct is commutative. -}

swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B → coprod B A
swap-coprod A B (inl x) = inr x
swap-coprod A B (inr x) = inl x

swap-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-coprod B A) ∘ (swap-coprod A B)) ~ id
swap-swap-coprod A B (inl x) = refl
swap-swap-coprod A B (inr x) = refl

abstract
  is-equiv-swap-coprod :
    {i j : Level} (A : UU i) (B : UU j) → is-equiv (swap-coprod A B)
  is-equiv-swap-coprod A B =
    is-equiv-has-inverse
      ( swap-coprod B A)
      ( swap-swap-coprod B A)
      ( swap-swap-coprod A B)

equiv-swap-coprod :
  {i j : Level} (A : UU i) (B : UU j) → coprod A B ≃ coprod B A
equiv-swap-coprod A B = pair (swap-coprod A B) (is-equiv-swap-coprod A B)

swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → prod A B → prod B A
swap-prod A B t = pair (pr2 t) (pr1 t)

swap-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) →
  ((swap-prod B A) ∘ (swap-prod A B)) ~ id
swap-swap-prod A B (pair x y) = refl

abstract
  is-equiv-swap-prod :
    {i j : Level} (A : UU i) (B : UU j) →
    is-equiv (swap-prod A B)
  is-equiv-swap-prod A B =
    is-equiv-has-inverse
      ( swap-prod B A)
      ( swap-swap-prod B A)
      ( swap-swap-prod A B)

equiv-swap-prod :
  {i j : Level} (A : UU i) (B : UU j) → (A × B) ≃ (B × A)
equiv-swap-prod A B = pair (swap-prod A B) (is-equiv-swap-prod A B)

-- Exercise 9.8

-- Exercise 9.9

-- Exercise 9.11

{-
abstract
  is-equiv-add-ℤ :
    (x : ℤ) → is-equiv (add-ℤ x)
  is-equiv-add-ℤ x =
    is-equiv-has-inverse
      ( add-ℤ (neg-ℤ x))
      ( issec-add-neg-ℤ x)
      ( isretr-add-neg-ℤ x)

abstract
  is-equiv-add-ℤ' :
    (y : ℤ) → is-equiv (add-ℤ' y)
  is-equiv-add-ℤ' y =
    is-equiv-htpy (add-ℤ y)
      ( λ x → commutative-add-ℤ x y)
      ( is-equiv-add-ℤ-right y)
-}

-- Exercise 9.12

-- Exercise 9.13

{- We construct the functoriality of coproducts. -}

htpy-map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {f f' : A → A'} (H : f ~ f') {g g' : B → B'} (K : g ~ g') →
  (map-coprod f g) ~ (map-coprod f' g')
htpy-map-coprod H K (inl x) = ap inl (H x)
htpy-map-coprod H K (inr y) = ap inr (K y)

id-map-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) →
  (map-coprod (id {A = A}) (id {A = B})) ~ id
id-map-coprod A B (inl x) = refl
id-map-coprod A B (inr x) = refl

compose-map-coprod :
  {l1 l2 l1' l2' l1'' l2'' : Level}
  {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
  {A'' : UU l1''} {B'' : UU l2''}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  (map-coprod (f' ∘ f) (g' ∘ g)) ~
  ((map-coprod f' g') ∘ (map-coprod f g))
compose-map-coprod f f' g g' (inl x) = refl
compose-map-coprod f f' g g' (inr y) = refl

abstract
  is-equiv-map-coprod :
    {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'}
    {f : A → A'} {g : B → B'} →
    is-equiv f → is-equiv g → is-equiv (map-coprod f g)
  is-equiv-map-coprod {A = A} {B = B} {A' = A'} {B' = B'} {f = f} {g = g}
    (pair (pair sf issec-sf) (pair rf isretr-rf))
    (pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( map-coprod sf sg)
        ( ( ( inv-htpy (compose-map-coprod sf f sg g)) ∙h
            ( htpy-map-coprod issec-sf issec-sg)) ∙h
          ( id-map-coprod A' B')))
      ( pair
        ( map-coprod rf rg)
        ( ( ( inv-htpy (compose-map-coprod f rf g rg)) ∙h
            ( htpy-map-coprod isretr-rf isretr-rg)) ∙h
          ( id-map-coprod A B)))
  
equiv-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A ≃ A') → (B ≃ B') → ((coprod A B) ≃ (coprod A' B'))
equiv-coprod (pair e is-equiv-e) (pair f is-equiv-f) =
  pair
    ( map-coprod e f)
    ( is-equiv-map-coprod is-equiv-e is-equiv-f)

--------------------------------------------------------------------------------

-- Extra material

abstract
  is-equiv-inv-con :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (inv-con p q r)
  is-equiv-inv-con refl q r = is-equiv-id

equiv-inv-con :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id q ((inv p) ∙ r)
equiv-inv-con p q r = pair (inv-con p q r) (is-equiv-inv-con p q r)

abstract
  is-equiv-con-inv :
    {i : Level} {A : UU i} {x y z : A} (p : Id x y)
    (q : Id y z) (r : Id x z) → is-equiv (con-inv p q r)
  is-equiv-con-inv p refl r =
    is-equiv-comp'
      ( concat' p (inv right-unit))
      ( concat (inv right-unit) r)
      ( is-equiv-concat (inv right-unit) r)
      ( is-equiv-concat' p (inv right-unit))

equiv-con-inv :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) (q : Id y z) (r : Id x z) →
  Id (p ∙ q) r ≃ Id p (r ∙ (inv q))
equiv-con-inv p q r = pair (con-inv p q r) (is-equiv-con-inv p q r)

-- Extra constructions with homotopies

inv-htpy-con :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → K ~ ((inv-htpy H) ∙h L)
inv-htpy-con H K L M x = inv-con (H x) (K x) (L x) (M x)

htpy-con-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) (L : f ~ h) →
  (H ∙h K) ~ L → H ~ (L ∙h (inv-htpy K))
htpy-con-inv H K L M x = con-inv (H x) (K x) (L x) (M x)

htpy-ap-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K K' : g ~ h) →
  K ~ K' → (H ∙h K) ~ (H ∙h K')
htpy-ap-concat {g = g} {h} H K K' L x =
  ap (concat (H x) (h x)) (L x)

htpy-ap-concat' :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H H' : f ~ g) (K : g ~ h) →
  H ~ H' → (H ∙h K) ~ (H' ∙h K)
htpy-ap-concat' H H' K L x =
  ap (concat' _ (K x)) (L x)

htpy-distributive-inv-concat :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g h : (x : A) → B x} →
  (H : f ~ g) (K : g ~ h) →
  (inv-htpy (H ∙h K)) ~ ((inv-htpy K) ∙h (inv-htpy H))
htpy-distributive-inv-concat H K x = distributive-inv-concat (H x) (K x)

htpy-ap-inv :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} →
  {H H' : f ~ g} →
  H ~ H' → (inv-htpy H) ~ (inv-htpy H')
htpy-ap-inv K x = ap inv (K x)

htpy-left-whisk-inv-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f f' : A → B} (g : B → C) (H : f ~ f') →
  (g ·l (inv-htpy H)) ~ inv-htpy (g ·l H)
htpy-left-whisk-inv-htpy g H x = ap-inv g (H x)

htpy-right-whisk-inv-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g g' : B → C} (H : g ~ g') (f : A → B) →
  ((inv-htpy H) ·r f) ~ (inv-htpy (H ·r f))
htpy-right-whisk-inv-htpy H f = refl-htpy

--------------------------------------------------------------------------------

coprod-Fin :
  (k l : ℕ) → coprod (Fin k) (Fin l) ≃ Fin (add-ℕ k l)
coprod-Fin k zero-ℕ = right-unit-law-coprod (Fin k)
coprod-Fin k (succ-ℕ l) =
  (equiv-coprod (coprod-Fin k l) equiv-id) ∘e inv-assoc-coprod

Fin-add-ℕ :
  (k l : ℕ) → Fin (add-ℕ k l) ≃ coprod (Fin k) (Fin l)
Fin-add-ℕ k l = inv-equiv (coprod-Fin k l)

{- We construct the functoriality of cartesian products. -}

map-prod-pr1 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
map-prod-pr1 f g (pair a b) = refl

map-prod-pr2 :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
map-prod-pr2 f g (pair a b) = refl

{- For our convenience we show that the functorial action of cartesian products
   preserves identity maps, compositions, homotopies, and equivalences. -}

map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl

map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k (pair a b) = refl

htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)

abstract
  is-equiv-map-prod :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (map-prod f g)
  is-equiv-map-prod f g
    ( pair (pair sf issec-sf) (pair rf isretr-rf))
    ( pair (pair sg issec-sg) (pair rg isretr-rg)) =
    pair
      ( pair
        ( map-prod sf sg)
        ( ( inv-htpy (map-prod-comp sf sg f g)) ∙h
          ( (htpy-map-prod issec-sf issec-sg) ∙h map-prod-id)))
      ( pair
        ( map-prod rf rg)
        ( ( inv-htpy (map-prod-comp f g rf rg)) ∙h
          ( (htpy-map-prod isretr-rf isretr-rg) ∙h map-prod-id)))

equiv-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
equiv-prod (pair f is-equiv-f) (pair g is-equiv-g) =
  pair (map-prod f g) (is-equiv-map-prod f g is-equiv-f is-equiv-g)

prod-Fin : (k l : ℕ) → ((Fin k) × (Fin l)) ≃ Fin (mul-ℕ k l)
prod-Fin zero-ℕ l = left-absorption-prod (Fin l)
prod-Fin (succ-ℕ k) l =
  ( ( coprod-Fin (mul-ℕ k l) l) ∘e
    ( equiv-coprod (prod-Fin k l) left-unit-law-prod)) ∘e
  ( right-distributive-prod-coprod (Fin k) unit (Fin l))

Fin-mul-ℕ : (k l : ℕ) → (Fin (mul-ℕ k l)) ≃ ((Fin k) × (Fin l))
Fin-mul-ℕ k l = inv-equiv (prod-Fin k l)

--------------------------------------------------------------------------------
