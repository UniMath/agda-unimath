{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.10-contractible-types where

import foundations.09-equivalences
open foundations.09-equivalences public

--------------------------------------------------------------------------------

-- Section 10 Contractible types

--------------------------------------------------------------------------------

-- Section 10.1 Contractible types

{- Definition 10.1.1 -}

is-contr :
  {l : Level} → UU l → UU l
is-contr A = Σ A (λ a → (x : A) → Id a x)

abstract
  center :
    {l : Level} {A : UU l} → is-contr A → A
  center (pair c is-contr-A) = c
  
-- We make sure that the contraction is coherent in a straightforward way
eq-is-contr' :
  {l : Level} {A : UU l} → is-contr A → (x y : A) → Id x y
eq-is-contr' (pair c C) x y = (inv (C x)) ∙ (C y)

eq-is-contr :
  {l : Level} {A : UU l} → is-contr A → {x y : A} → Id x y
eq-is-contr (pair c C) {x} {y} = (inv (C x)) ∙ (C y)

abstract
  contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    (const A A (center is-contr-A) ~ id)
  contraction (pair c C) x = eq-is-contr (pair c C)
  
  coh-contraction :
    {l : Level} {A : UU l} (is-contr-A : is-contr A) →
    Id (contraction is-contr-A (center is-contr-A)) refl
  coh-contraction (pair c C) = left-inv (C c)

{- Remark 10.1.2 -}

{- Remark 10.1.3 -}

{- Theorem 10.1.4 -}

--------------------------------------------------------------------------------

-- Section 10.2 Singleton induction

-- We show that contractible types satisfy an induction principle akin to the induction principle of the unit type: singleton induction. This can be helpful to give short proofs of many facts.

{- Definition 10.2.1 -}

ev-pt :
  {l1 l2 : Level} {A : UU l1} (a : A) (B : A → UU l2) → ((x : A) → B x) → B a
ev-pt a B f = f a

is-singleton :
  (l : Level) {i : Level} (A : UU i) → A → UU (lsuc l ⊔ i)
is-singleton l A a = (B : A → UU l) → sec (ev-pt a B)

ind-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) →
  ({l : Level} → is-singleton l A a) → (B : A → UU l2) →
  B a → (x : A) → B x
ind-is-singleton a is-sing-A B = pr1 (is-sing-A B)

comp-is-singleton :
  {l1 l2 : Level} {A : UU l1} (a : A) (H : {l : Level} → is-singleton l A a) →
  (B : A → UU l2) → (ev-pt a B ∘ ind-is-singleton a H B) ~ id
comp-is-singleton a H B = pr2 (H B)

{- Theorem 10.2.3 -}

abstract
  ind-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    B a → (x : A) → B x
  ind-singleton-is-contr a is-contr-A B b x =
    tr B ((inv (contraction is-contr-A a)) ∙ (contraction is-contr-A x)) b
  
  comp-singleton-is-contr :
    {i j : Level} {A : UU i} (a : A) (is-contr-A : is-contr A) (B : A → UU j) →
    ((ev-pt a B) ∘ (ind-singleton-is-contr a is-contr-A B)) ~ id
  comp-singleton-is-contr a is-contr-A B b =
    ap (λ ω → tr B ω b) (left-inv (contraction is-contr-A a))

is-singleton-is-contr :
  {l1 l2 : Level} {A : UU l1} (a : A) → is-contr A → is-singleton l2 A a
is-singleton-is-contr a is-contr-A B =
  pair
    ( ind-singleton-is-contr a is-contr-A B)
    ( comp-singleton-is-contr a is-contr-A B)

abstract
  is-contr-ind-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} (P : A → UU l) → P a → (x : A) → P x) → is-contr A
  is-contr-ind-singleton A a S = pair a (S (λ x → Id a x) refl)

abstract
  is-contr-is-singleton :
    {i : Level} (A : UU i) (a : A) →
    ({l : Level} → is-singleton l A a) → is-contr A
  is-contr-is-singleton A a S = is-contr-ind-singleton A a (λ P → pr1 (S P))

abstract
  is-singleton-unit : {l : Level} → is-singleton l unit star
  is-singleton-unit B = pair ind-unit (λ b → refl)

is-contr-unit : is-contr unit
is-contr-unit = is-contr-is-singleton unit star (is-singleton-unit)

abstract
  is-singleton-total-path :
    {i l : Level} (A : UU i) (a : A) →
    is-singleton l (Σ A (λ x → Id a x)) (pair a refl)
  is-singleton-total-path A a B = pair (ind-Σ ∘ (ind-Id a _)) (λ b → refl)

abstract
  is-contr-total-path :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id a x))
  is-contr-total-path {A = A} a =
    is-contr-is-singleton _ _ (is-singleton-total-path A a)

--------------------------------------------------------------------------------

-- Section 10.3 Contractible maps

{- Definition 10.3.1 -}

fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib f b = Σ _ (λ x → Id (f x) b)

fib' :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (b : B) → UU (i ⊔ j)
fib' f b = Σ _ (λ x → Id b (f x))

{- Definition 10.3.2 -}

Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib f y → UU (i ⊔ j)
Eq-fib f y s t =
  Σ (Id (pr1 s) (pr1 t)) (λ α → Id ((ap f α) ∙ (pr2 t)) (pr2 s))

{- Proposition 10.3.3 -}

reflexive-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  (s : fib f y) → Eq-fib f y s s
reflexive-Eq-fib f y s = pair refl refl

Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → (Id s t) → Eq-fib f y s t
Eq-fib-eq f y {s} refl = reflexive-Eq-fib f y s

eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t → Id s t
eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

issec-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((Eq-fib-eq f y {s} {t}) ∘ (eq-Eq-fib f y {s} {t})) ~ id
issec-eq-Eq-fib f y {pair x p} {pair .x .p} (pair refl refl) = refl

isretr-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → ((eq-Eq-fib f y {s} {t}) ∘ (Eq-fib-eq f y {s} {t})) ~ id
isretr-eq-Eq-fib f y {pair x p} {.(pair x p)} refl = refl

abstract
  is-equiv-Eq-fib-eq :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (Eq-fib-eq f y {s} {t})
  is-equiv-Eq-fib-eq f y {s} {t} =
    is-equiv-has-inverse
      ( eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)
      ( isretr-eq-Eq-fib f y)

equiv-Eq-fib-eq :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Id s t ≃ Eq-fib f y s t
equiv-Eq-fib-eq f y {s} {t} = pair (Eq-fib-eq f y) (is-equiv-Eq-fib-eq f y)

abstract
  is-equiv-eq-Eq-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
    {s t : fib f y} → is-equiv (eq-Eq-fib f y {s} {t})
  is-equiv-eq-Eq-fib f y {s} {t} =
    is-equiv-has-inverse
      ( Eq-fib-eq f y)
      ( isretr-eq-Eq-fib f y)
      ( issec-eq-Eq-fib f y)

equiv-eq-Eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  {s t : fib f y} → Eq-fib f y s t ≃ Id s t
equiv-eq-Eq-fib f y {s} {t} = pair (eq-Eq-fib f y) (is-equiv-eq-Eq-fib f y)

{- Definition 10.3.4 -}

is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-contr-map f = (y : _) → is-contr (fib f y)

{- Theorem 10.3.5 -}

-- Our goal is to show that contractible maps are equivalences.
-- First we construct the inverse of a contractible map.
map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-contr-map f → B → A
map-inv-is-contr-map is-contr-f y = pr1 (center (is-contr-f y))

-- Then we show that the inverse is a section.
issec-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → (f ∘ (map-inv-is-contr-map is-contr-f)) ~ id
issec-map-inv-is-contr-map is-contr-f y = pr2 (center (is-contr-f y))

-- Then we show that the inverse is also a retraction.
isretr-map-inv-is-contr-map :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B}
  (is-contr-f : is-contr-map f) → ((map-inv-is-contr-map is-contr-f) ∘ f) ~ id
isretr-map-inv-is-contr-map {_} {_} {A} {B} {f} is-contr-f x =
  ap ( pr1 {B = λ z → Id (f z) (f x)})
     ( ( inv
         ( contraction
           ( is-contr-f (f x))
           ( pair
             ( map-inv-is-contr-map is-contr-f (f x))
             ( issec-map-inv-is-contr-map is-contr-f (f x))))) ∙
       ( contraction (is-contr-f (f x)) (pair x refl)))

-- Finally we put it all together to show that contractible maps are equivalences.

abstract
  is-equiv-is-contr-map :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-contr-map f → is-equiv f
  is-equiv-is-contr-map is-contr-f =
    is-equiv-has-inverse
      ( map-inv-is-contr-map is-contr-f)
      ( issec-map-inv-is-contr-map is-contr-f)
      ( isretr-map-inv-is-contr-map is-contr-f)

--------------------------------------------------------------------------------

-- Section 10.4 Equivalences are contractible maps

{- Definition 10.4.1 -}

coherence-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  (G : (f ∘ g) ~ id) (H : (g ∘ f) ~ id) → UU (l1 ⊔ l2)
coherence-is-coherently-invertible f g G H = (G ·r f) ~ (f ·l H)

is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
is-coherently-invertible {l1} {l2} {A} {B} f =
  Σ ( B → A)
    ( λ g → Σ ((f ∘ g) ~ id)
      ( λ G → Σ ((g ∘ f) ~ id)
        (λ H → ((G ·r f) ~ (f ·l H)))))

inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-coherently-invertible f → B → A
inv-is-coherently-invertible = pr1

issec-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (f ∘ inv-is-coherently-invertible H) ~ id
issec-inv-is-coherently-invertible H = pr1 (pr2 H)

isretr-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) → (inv-is-coherently-invertible H ∘ f) ~ id
isretr-inv-is-coherently-invertible H = pr1 (pr2 (pr2 H))

coh-inv-is-coherently-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  (H : is-coherently-invertible f) →
  coherence-is-coherently-invertible f
    ( inv-is-coherently-invertible H)
    ( issec-inv-is-coherently-invertible H)
    ( isretr-inv-is-coherently-invertible H)
coh-inv-is-coherently-invertible H = pr2 (pr2 (pr2 H))

{- Proposition 10.4.2 -}

abstract
  center-fib-is-coherently-invertible :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-coherently-invertible f → (y : B) → fib f y
  center-fib-is-coherently-invertible {i} {j} {A} {B} {f} H y =
    pair
      ( inv-is-coherently-invertible H y)
      ( issec-inv-is-coherently-invertible H y)

  contraction-fib-is-coherently-invertible :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
    Id (center-fib-is-coherently-invertible H y) t
  contraction-fib-is-coherently-invertible {f = f} H y (pair x refl) =
    eq-Eq-fib f y
      ( pair 
        ( isretr-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x))))

is-contr-map-is-coherently-invertible : 
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
  is-coherently-invertible f → is-contr-map f
is-contr-map-is-coherently-invertible H y =
  pair
    ( center-fib-is-coherently-invertible H y)
    ( contraction-fib-is-coherently-invertible H y)
      
{- Definition 10.4.3 -}

htpy-nat :
  {i j : Level} {A : UU i} {B : UU j} {f g : A → B} (H : f ~ g)
  {x y : A} (p : Id x y) →
  Id ((H x) ∙ (ap g p)) ((ap f p) ∙ (H y))
htpy-nat H refl = right-unit

{- Definition 10.4.4 -}

left-unwhisk :
  {i : Level} {A : UU i} {x y z : A} (p : Id x y) {q r : Id y z} →
  Id (p ∙ q) (p ∙ r) → Id q r
left-unwhisk refl s = (inv left-unit) ∙ (s ∙ left-unit)

right-unwhisk :
  {i : Level} {A : UU i} {x y z : A} {p q : Id x y}
  (r : Id y z) → Id (p ∙ r) (q ∙ r) → Id p q
right-unwhisk refl s = (inv right-unit) ∙ (s ∙ right-unit)

htpy-red :
  {i : Level} {A : UU i} {f : A → A} (H : f ~ id) →
  (x : A) → Id (H (f x)) (ap f (H x))
htpy-red {_} {A} {f} H x =
  right-unwhisk (H x)
    ( ( ap (concat (H (f x)) x) (inv (ap-id (H x)))) ∙
      ( htpy-nat H (H x)))

{- Lemma 10.4.5 -}

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : has-inverse f)
  where
  
  inv-has-inverse : B → A
  inv-has-inverse = pr1 H
  
  issec-inv-has-inverse : (f ∘ inv-has-inverse) ~ id
  issec-inv-has-inverse y =
    ( inv (pr1 (pr2 H) (f (inv-has-inverse y)))) ∙
    ( ap f (pr2 (pr2 H) (inv-has-inverse y)) ∙ (pr1 (pr2 H) y))
  
  isretr-inv-has-inverse : (inv-has-inverse ∘ f) ~ id
  isretr-inv-has-inverse = pr2 (pr2 H)
  
  coherence-inv-has-inverse :
    (issec-inv-has-inverse ·r f) ~ (f ·l isretr-inv-has-inverse)
  coherence-inv-has-inverse x =
    inv
      ( inv-con
        ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
        ( ap f (pr2 (pr2 H) x))
        ( (ap f (pr2 (pr2 H) (inv-has-inverse (f x)))) ∙ (pr1 (pr2 H) (f x)))
        ( sq-top-whisk
          ( pr1 (pr2 H) (f (inv-has-inverse (f x))))
          ( ap f (pr2 (pr2 H) x))
          ( (ap (f ∘ (inv-has-inverse ∘ f)) (pr2 (pr2 H) x)))
          ( ( ap-comp f (inv-has-inverse ∘ f) (pr2 (pr2 H) x)) ∙
            ( inv (ap (ap f) (htpy-red (pr2 (pr2 H)) x))))
          ( pr1 (pr2 H) (f x))
          ( htpy-nat (htpy-right-whisk (pr1 (pr2 H)) f) (pr2 (pr2 H) x))))

  is-coherently-invertible-has-inverse : is-coherently-invertible f
  is-coherently-invertible-has-inverse =
    pair
      ( inv-has-inverse)
      ( pair
        ( issec-inv-has-inverse)
        ( pair
          ( isretr-inv-has-inverse)
          ( coherence-inv-has-inverse)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv H) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv H ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

{- Theorem 10.4.6 -}

abstract
  is-contr-map-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} →
    is-equiv f → is-contr-map f
  is-contr-map-is-equiv =
    is-contr-map-is-coherently-invertible ∘
      ( is-coherently-invertible-has-inverse ∘
        has-inverse-is-equiv)

{- Corollary 10.4.7 -}

abstract
  is-contr-total-path' :
    {i : Level} {A : UU i} (a : A) → is-contr (Σ A (λ x → Id x a))
  is-contr-total-path' a = is-contr-map-is-equiv is-equiv-id a

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 10.1

-- In this exercise we are asked to show that the identity types of a contractible type are again contractible. In the terminology of Lecture 8: we are showing that contractible types are propositions.

contraction-is-prop-is-contr :
  {i : Level} {A : UU i} (H : is-contr A) {x y : A} →
  (p : Id x y) → Id (eq-is-contr H) p
contraction-is-prop-is-contr (pair c C) {x} refl = left-inv (C x)

abstract
  is-prop-is-contr : {i : Level} {A : UU i} → is-contr A →
    (x y : A) → is-contr (Id x y)
  is-prop-is-contr {i} {A} is-contr-A x y =
    pair
      ( eq-is-contr is-contr-A)
      ( contraction-is-prop-is-contr is-contr-A)

-- Exercise 10.2

-- In this exercise we are showing that contractible types are closed under retracts.

abstract
  is-contr-retract-of : {i j : Level} {A : UU i} (B : UU j) →
    A retract-of B → is-contr B → is-contr A
  is-contr-retract-of B (pair i (pair r isretr)) is-contr-B =
    pair
      ( r (center is-contr-B))
      ( λ x → (ap r (contraction is-contr-B (i x))) ∙ (isretr x))

-- Exercise 10.3

-- In this exercise we are showing that a type is contractible if and only if the constant map to the unit type is an equivalence. This can be used to derive a '3-for-2 property' for contractible types, which may come in handy sometimes.

abstract
  is-equiv-terminal-map-is-contr :
    {i : Level} {A : UU i} → is-contr A → is-equiv (terminal-map {A = A})
  is-equiv-terminal-map-is-contr {i} {A} is-contr-A =
    pair
      ( pair (ind-unit (center is-contr-A)) (ind-unit refl))
      ( pair (const unit A (center is-contr-A)) (contraction is-contr-A))

abstract
  is-contr-is-equiv-const :
    {i : Level} {A : UU i} → is-equiv (terminal-map {A = A}) → is-contr A
  is-contr-is-equiv-const (pair (pair g issec) (pair h isretr)) =
    pair (h star) isretr

abstract
  is-contr-is-equiv :
    {i j : Level} {A : UU i} (B : UU j) (f : A → B) →
    is-equiv f → is-contr B → is-contr A
  is-contr-is-equiv B f is-equiv-f is-contr-B =
    is-contr-is-equiv-const
      ( is-equiv-comp'
        ( terminal-map)
        ( f)
        ( is-equiv-f)
        ( is-equiv-terminal-map-is-contr is-contr-B))

abstract
  is-contr-equiv :
    {i j : Level} {A : UU i} (B : UU j) (e : A ≃ B) → is-contr B → is-contr A
  is-contr-equiv B (pair e is-equiv-e) is-contr-B =
    is-contr-is-equiv B e is-equiv-e is-contr-B

abstract
  is-contr-is-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-contr A → is-contr B
  is-contr-is-equiv' A f is-equiv-f is-contr-A =
    is-contr-is-equiv A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-contr-A)

abstract
  is-contr-equiv' :
    {i j : Level} (A : UU i) {B : UU j} (e : A ≃ B) → is-contr A → is-contr B
  is-contr-equiv' A (pair e is-equiv-e) is-contr-A =
    is-contr-is-equiv' A e is-equiv-e is-contr-A

abstract
  is-equiv-is-contr :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-contr A → is-contr B → is-equiv f
  is-equiv-is-contr {i} {j} {A} {B} f is-contr-A is-contr-B =
    is-equiv-has-inverse
      ( const B A (center is-contr-A))
      ( ind-singleton-is-contr _ is-contr-B _
        ( inv (contraction is-contr-B (f (center is-contr-A)))))
      ( contraction is-contr-A)

equiv-is-contr :
  {i j : Level} {A : UU i} {B : UU j} →
  is-contr A → is-contr B → A ≃ B
equiv-is-contr is-contr-A is-contr-B =
  pair
    ( λ a → center is-contr-B)
    ( is-equiv-is-contr _ is-contr-A is-contr-B)

map-equiv-Fin-one-ℕ : Fin one-ℕ → unit
map-equiv-Fin-one-ℕ (inr star) = star

inv-map-equiv-Fin-one-ℕ : unit → Fin one-ℕ
inv-map-equiv-Fin-one-ℕ star = inr star

issec-inv-map-equiv-Fin-one-ℕ :
  ( map-equiv-Fin-one-ℕ ∘ inv-map-equiv-Fin-one-ℕ) ~ id
issec-inv-map-equiv-Fin-one-ℕ star = refl

isretr-inv-map-equiv-Fin-one-ℕ :
  ( inv-map-equiv-Fin-one-ℕ ∘ map-equiv-Fin-one-ℕ) ~ id
isretr-inv-map-equiv-Fin-one-ℕ (inr star) = refl

is-equiv-map-equiv-Fin-one-ℕ : is-equiv map-equiv-Fin-one-ℕ
is-equiv-map-equiv-Fin-one-ℕ =
  is-equiv-has-inverse
    inv-map-equiv-Fin-one-ℕ
    issec-inv-map-equiv-Fin-one-ℕ
    isretr-inv-map-equiv-Fin-one-ℕ

equiv-Fin-one-ℕ : Fin one-ℕ ≃ unit
equiv-Fin-one-ℕ = pair map-equiv-Fin-one-ℕ is-equiv-map-equiv-Fin-one-ℕ

is-contr-Fin-one-ℕ : is-contr (Fin one-ℕ)
is-contr-Fin-one-ℕ = is-contr-equiv unit equiv-Fin-one-ℕ is-contr-unit

-- Exercise 10.4

is-not-contractible : {l : Level} → UU l → UU l
is-not-contractible X = ¬ (is-contr X)

is-not-contractible-is-empty :
  {l : Level} {X : UU l} → is-empty X → is-not-contractible X
is-not-contractible-is-empty H C = H (center C)

is-not-contractible-empty : is-not-contractible empty
is-not-contractible-empty = is-not-contractible-is-empty id

is-not-contractible-Fin :
  (k : ℕ) → is-not-one-ℕ k → is-not-contractible (Fin k)
is-not-contractible-Fin zero-ℕ f = is-not-contractible-empty
is-not-contractible-Fin (succ-ℕ zero-ℕ) f C = f refl
is-not-contractible-Fin (succ-ℕ (succ-ℕ k)) f C =
  Eq-Fin-eq (eq-is-contr' C neg-two-Fin neg-one-Fin)

-- Exercise 10.5

-- In this exercise we show that if a cartesian product is contractible, then so are its factors. We make use of the fact that contractible types are closed under retracts, just because that is a useful property to practice with. Other proofs are possible too.

abstract
  is-contr-left-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr A
  is-contr-left-factor-prod A B is-contr-AB =
    is-contr-retract-of
      ( A × B)
      ( pair
        ( λ x → pair x (pr2 (center is-contr-AB)))
        ( pair pr1 (λ x → refl)))
      ( is-contr-AB)

abstract
  is-contr-right-factor-prod :
    {i j : Level} (A : UU i) (B : UU j) → is-contr (A × B) → is-contr B
  is-contr-right-factor-prod A B is-contr-AB =
    is-contr-left-factor-prod B A
      ( is-contr-equiv
        ( A × B)
        ( equiv-swap-prod B A)
        ( is-contr-AB))

abstract
  is-contr-prod :
    {i j : Level} {A : UU i} {B : UU j} →
    is-contr A → is-contr B → is-contr (A × B)
  is-contr-prod {A = A} {B = B} (pair a C) (pair b D) =
    pair (pair a b) α
    where
    α : (z : A × B) → Id (pair a b) z
    α (pair x y) = eq-pair (C x) (D y)

-- Exercise 10.6

-- In this exercise we will show that if the base type in a Σ-type is contractible, then the Σ-type is equivalent to the fiber at the center of contraction. This can be seen as a left unit law for Σ-types. We will derive a right unit law for Σ-types in Lecture 7 (not because it is unduable here, but it is useful to have some knowledge of fiberwise equivalences).

map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  B a → Σ A B
map-inv-left-unit-law-Σ-is-contr C a = pair a

map-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} → is-contr A → (a : A) →
  Σ A B → B a
map-left-unit-law-Σ-is-contr {B = B} C a =
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → B x → B a)
      ( id))

issec-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-inv-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
issec-map-inv-left-unit-law-Σ-is-contr {B = B} C a b =
  ap ( λ (f : B a → B a) → f b)
     ( comp-singleton-is-contr a C (λ x → B x → B a) id)

isretr-map-inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  ( ( map-inv-left-unit-law-Σ-is-contr {B = B} C a) ∘
    ( map-left-unit-law-Σ-is-contr {B = B} C a)) ~ id
isretr-map-inv-left-unit-law-Σ-is-contr {B = B} C a = 
  ind-Σ
    ( ind-singleton-is-contr a C
      ( λ x → (y : B x) →
        Id ( ( ( map-inv-left-unit-law-Σ-is-contr C a) ∘
               ( map-left-unit-law-Σ-is-contr C a))
             ( pair x y))
           ( id (pair x y)))
      ( λ y → ap
        ( map-inv-left-unit-law-Σ-is-contr C a)
        ( ap ( λ f → f y)
             ( comp-singleton-is-contr a C (λ x → B x → B a) id))))

abstract
  is-equiv-map-left-unit-law-Σ-is-contr :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
    is-equiv (map-left-unit-law-Σ-is-contr {B = B} C a)
  is-equiv-map-left-unit-law-Σ-is-contr C a =
    is-equiv-has-inverse
      ( map-inv-left-unit-law-Σ-is-contr C a)
      ( issec-map-inv-left-unit-law-Σ-is-contr C a)
      ( isretr-map-inv-left-unit-law-Σ-is-contr C a)

left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  Σ A B ≃ B a
left-unit-law-Σ-is-contr C a =
  pair
    ( map-left-unit-law-Σ-is-contr C a)
    ( is-equiv-map-left-unit-law-Σ-is-contr C a)

left-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (C : is-contr A) → (A × B) ≃ B
left-unit-law-prod-is-contr C =
  left-unit-law-Σ-is-contr C (center C)

abstract
  is-equiv-map-inv-left-unit-law-Σ-is-contr :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
    is-equiv (map-inv-left-unit-law-Σ-is-contr {B = B} C a)
  is-equiv-map-inv-left-unit-law-Σ-is-contr C a =
    is-equiv-has-inverse
      ( map-left-unit-law-Σ-is-contr C a)
      ( isretr-map-inv-left-unit-law-Σ-is-contr C a)
      ( issec-map-inv-left-unit-law-Σ-is-contr C a)

inv-left-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (C : is-contr A) (a : A) →
  B a ≃ Σ A B
inv-left-unit-law-Σ-is-contr C a =
  pair
    ( map-inv-left-unit-law-Σ-is-contr C a)
    ( is-equiv-map-inv-left-unit-law-Σ-is-contr C a)

-- Exercise 10.7

-- Exercise 10.7 (a)

map-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  fib (pr1 {B = B}) a → B a
map-fib-pr1 B a (pair (pair x y) p) = tr B p y

map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j)
  (a : A) → B a → fib (pr1 {B = B}) a
map-inv-fib-pr1 B a b = pair (pair a b) refl

issec-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-inv-fib-pr1 B a) ∘ (map-fib-pr1 B a)) ~ id
issec-map-inv-fib-pr1 B a (pair (pair .a y) refl) = refl

isretr-map-inv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  ((map-fib-pr1 B a) ∘ (map-inv-fib-pr1 B a)) ~ id
isretr-map-inv-fib-pr1 B a b = refl

abstract
  is-equiv-map-fib-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (map-fib-pr1 B a)
  is-equiv-map-fib-pr1 B a =
    is-equiv-has-inverse
      ( map-inv-fib-pr1 B a)
      ( isretr-map-inv-fib-pr1 B a)
      ( issec-map-inv-fib-pr1 B a)

equiv-fib-pr1 :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) → fib (pr1 {B = B}) a ≃ B a
equiv-fib-pr1 {B = B} a =
  pair (map-fib-pr1 B a) (is-equiv-map-fib-pr1 B a)

abstract
  is-equiv-map-inv-fib-pr1 :
    {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
    is-equiv (map-inv-fib-pr1 B a)
  is-equiv-map-inv-fib-pr1 B a =
    is-equiv-has-inverse
      ( map-fib-pr1 B a)
      ( issec-map-inv-fib-pr1 B a)
      ( isretr-map-inv-fib-pr1 B a)

inv-equiv-fib-pr1 :
  {i j : Level} {A : UU i} (B : A → UU j) (a : A) →
  B a ≃ fib (pr1 {B = B}) a
inv-equiv-fib-pr1 B a =
  pair (map-inv-fib-pr1 B a) (is-equiv-map-inv-fib-pr1 B a)

-- Exercise 10.7 (b)

abstract
  is-equiv-pr1-is-contr :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((a : A) → is-contr (B a)) → is-equiv (pr1 {B = B})
  is-equiv-pr1-is-contr {B = B} is-contr-B =
    is-equiv-is-contr-map
      ( λ x → is-contr-equiv
        ( B x)
        ( equiv-fib-pr1 x)
        ( is-contr-B x))

equiv-pr1 :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
equiv-pr1 is-contr-B = pair pr1 (is-equiv-pr1-is-contr is-contr-B)

right-unit-law-Σ-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((a : A) → is-contr (B a)) → (Σ A B) ≃ A
right-unit-law-Σ-is-contr = equiv-pr1

right-unit-law-prod-is-contr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-contr B → (A × B) ≃ A
right-unit-law-prod-is-contr {l1} {l2} {A} {B} H =
  right-unit-law-Σ-is-contr (λ a → H)

abstract
  is-contr-is-equiv-pr1 :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    (is-equiv (pr1 {B = B})) → ((a : A) → is-contr (B a))
  is-contr-is-equiv-pr1 {B = B} is-equiv-pr1-B a =
    is-contr-equiv'
      ( fib pr1 a)
      ( equiv-fib-pr1 a)
      ( is-contr-map-is-equiv is-equiv-pr1-B a)

-- Exercise 10.7 (c)

map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  ((x : A) → B x) → (A → Σ A B)
map-section b a = pair a (b a)

htpy-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  (pr1 ∘ map-section b) ~ id
htpy-map-section b a = refl

is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → is-equiv (map-section b)
is-equiv-map-section b C =
  is-equiv-right-factor
    ( id)
    ( pr1)
    ( map-section b)
    ( htpy-map-section b)
    ( is-equiv-pr1-is-contr C)
    ( is-equiv-id)

equiv-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  ((x : A) → is-contr (B x)) → A ≃ Σ A B
equiv-section b C = pair (map-section b) (is-equiv-map-section b C)

is-contr-fam-is-equiv-map-section :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (b : (x : A) → B x) →
  is-equiv (map-section b) → ((x : A) → is-contr (B x))
is-contr-fam-is-equiv-map-section b H =
  is-contr-is-equiv-pr1
    ( is-equiv-left-factor id pr1
      ( map-section b)
      ( htpy-map-section b)
      ( is-equiv-id)
      ( H))

-- Exercise 10.8

-- In this exercise we show that the domain of a map is equivalent to the total space of its fibers.

map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → (Σ B (fib f)) → A
map-equiv-total-fib f t = pr1 (pr2 t)

triangle-map-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  pr1 ~ (f ∘ (map-equiv-total-fib f))
triangle-map-equiv-total-fib f t = inv (pr2 (pr2 t))

map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A → Σ B (fib f)
map-inv-equiv-total-fib f x = pair (f x) (pair x refl)

isretr-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-inv-equiv-total-fib f) ∘ (map-equiv-total-fib f)) ~ id
isretr-map-inv-equiv-total-fib f (pair .(f x) (pair x refl)) = refl

issec-map-inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
  ((map-equiv-total-fib f) ∘ (map-inv-equiv-total-fib f)) ~ id
issec-map-inv-equiv-total-fib f x = refl

abstract
  is-equiv-map-equiv-total-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-equiv (map-equiv-total-fib f)
  is-equiv-map-equiv-total-fib f =
    is-equiv-has-inverse
      ( map-inv-equiv-total-fib f)
      ( issec-map-inv-equiv-total-fib f)
      ( isretr-map-inv-equiv-total-fib f)

  is-equiv-map-inv-equiv-total-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    is-equiv (map-inv-equiv-total-fib f)
  is-equiv-map-inv-equiv-total-fib f =
    is-equiv-has-inverse
      ( map-equiv-total-fib f)
      ( isretr-map-inv-equiv-total-fib f)
      ( issec-map-inv-equiv-total-fib f)

equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B ) → Σ B (fib f) ≃ A
equiv-total-fib f =
  pair (map-equiv-total-fib f) (is-equiv-map-equiv-total-fib f)

inv-equiv-total-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → A ≃ Σ B (fib f)
inv-equiv-total-fib f =
  pair (map-inv-equiv-total-fib f) (is-equiv-map-inv-equiv-total-fib f)
