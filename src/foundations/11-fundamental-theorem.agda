{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.11-fundamental-theorem where

open import foundations.10-contractible-types public

--------------------------------------------------------------------------------

-- Section 11.1 Families of equivalences

{- Any family of maps induces a map on the total spaces. -}

tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → ( Σ A B → Σ A C)
tot f t = pair (pr1 t) (f (pr1 t) (pr2 t))

{- We show that for any family of maps, the fiber of the induced map on total
   spaces are equivalent to the fibers of the maps in the family. -}
   
fib-ftr-fib-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (tot f) t → fib (f (pr1 t)) (pr2 t)
fib-ftr-fib-tot f .(pair x (f x y)) (pair (pair x y) refl) = pair y refl

fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  fib (f (pr1 t)) (pr2 t) → fib (tot f) t
fib-tot-fib-ftr F (pair a .(F a y)) (pair y refl) = pair (pair a y) refl

issec-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-ftr-fib-tot f t) ∘ (fib-tot-fib-ftr f t)) ~ id
issec-fib-tot-fib-ftr f (pair x .(f x y)) (pair y refl) = refl

isretr-fib-tot-fib-ftr :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  (f : (x : A) → B x → C x) → (t : Σ A C) →
  ((fib-tot-fib-ftr f t) ∘ (fib-ftr-fib-tot f t)) ~ id
isretr-fib-tot-fib-ftr f .(pair x (f x y)) (pair (pair x y) refl) = refl

abstract
  is-equiv-fib-ftr-fib-tot :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → (t : Σ A C) →
    is-equiv (fib-ftr-fib-tot f t)
  is-equiv-fib-ftr-fib-tot f t =
    is-equiv-has-inverse
      ( fib-tot-fib-ftr f t)
      ( issec-fib-tot-fib-ftr f t)
      ( isretr-fib-tot-fib-ftr f t)

abstract
  is-equiv-fib-tot-fib-ftr :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → (t : Σ A C) →
    is-equiv (fib-tot-fib-ftr f t)
  is-equiv-fib-tot-fib-ftr f t =
    is-equiv-has-inverse
      ( fib-ftr-fib-tot f t)
      ( isretr-fib-tot-fib-ftr f t)
      ( issec-fib-tot-fib-ftr f t)

{- Now that we have shown that the fibers of the induced map on total spaces
   are equivalent to the fibers of the maps in the family, it follows that
   the induced map on total spaces is an equivalence if and only if each map
   in the family is an equivalence. -}

is-fiberwise-equiv :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x → C x) → UU (i ⊔ (j ⊔ k))
is-fiberwise-equiv f = (x : _) → is-equiv (f x)

abstract
  is-equiv-tot-is-fiberwise-equiv :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    {f : (x : A) → B x → C x} → is-fiberwise-equiv f →
    is-equiv (tot f )
  is-equiv-tot-is-fiberwise-equiv {f = f} H =
    is-equiv-is-contr-map
      ( λ t → is-contr-is-equiv _
        ( fib-ftr-fib-tot f t)
        ( is-equiv-fib-ftr-fib-tot f t)
        ( is-contr-map-is-equiv (H _) (pr2 t)))

abstract
  is-fiberwise-equiv-is-equiv-tot :
    {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
    (f : (x : A) → B x → C x) → is-equiv (tot f) →
    is-fiberwise-equiv f
  is-fiberwise-equiv-is-equiv-tot {A = A} {B} {C} f is-equiv-tot-f x =
    is-equiv-is-contr-map
      ( λ z → is-contr-is-equiv'
        ( fib (tot f) (pair x z))
        ( fib-ftr-fib-tot f (pair x z))
        ( is-equiv-fib-ftr-fib-tot f (pair x z))
        ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

equiv-tot :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k} →
  ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
equiv-tot e =
  pair
    ( tot (λ x → map-equiv (e x)))
    ( is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x)))

{- In the second part of this section we show that any equivalence f on base 
   types also induces an equivalence on total spaces. -}

map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  Σ A (λ x → C (f x)) → Σ B C
map-Σ-map-base f C s = pair (f (pr1 s)) (pr2 s)

{- The proof is similar to the previous part: we show that the fibers of f
   and Σ-kap-base-map f C are equivalent. -}

fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib f (pr1 t) → fib (map-Σ-map-base f C) t
fib-map-Σ-map-base-fib f C (pair .(f x) z) (pair x refl) =
  pair (pair x z) refl

fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → fib (map-Σ-map-base f C) t → fib f (pr1 t)
fib-fib-map-Σ-map-base f C .(pair (f x) z) (pair (pair x z) refl) =
  pair x refl

issec-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-map-Σ-map-base-fib f C t) ∘ (fib-fib-map-Σ-map-base f C t)) ~ id
issec-fib-fib-map-Σ-map-base f C .(pair (f x) z) (pair (pair x z) refl) =
  refl

isretr-fib-fib-map-Σ-map-base :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) →
  ( (fib-fib-map-Σ-map-base f C t) ∘ (fib-map-Σ-map-base-fib f C t)) ~ id
isretr-fib-fib-map-Σ-map-base f C (pair .(f x) z) (pair x refl) = refl

abstract
  is-equiv-fib-map-Σ-map-base-fib :
    { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
    ( t : Σ B C) → is-equiv (fib-map-Σ-map-base-fib f C t)
  is-equiv-fib-map-Σ-map-base-fib f C t =
    is-equiv-has-inverse
      ( fib-fib-map-Σ-map-base f C t)
      ( issec-fib-fib-map-Σ-map-base f C t)
      ( isretr-fib-fib-map-Σ-map-base f C t)

equiv-fib-map-Σ-map-base-fib :
  { l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ( t : Σ B C) → (fib f (pr1 t)) ≃ (fib (map-Σ-map-base f C) t)
equiv-fib-map-Σ-map-base-fib f C t =
  pair ( fib-map-Σ-map-base-fib f C t)
       ( is-equiv-fib-map-Σ-map-base-fib f C t)

abstract
  is-contr-map-map-Σ-map-base :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
    is-contr-map f → is-contr-map (map-Σ-map-base f C)
  is-contr-map-map-Σ-map-base C f is-contr-f (pair y z) =
    is-contr-is-equiv'
      ( fib f y)
      ( fib-map-Σ-map-base-fib f C (pair y z))
      ( is-equiv-fib-map-Σ-map-base-fib f C (pair y z))
      ( is-contr-f y)

abstract
  is-equiv-map-Σ-map-base :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (f : A → B) →
    is-equiv f → is-equiv (map-Σ-map-base f C)
  is-equiv-map-Σ-map-base C f is-equiv-f =
    is-equiv-is-contr-map
      ( is-contr-map-map-Σ-map-base C f (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ (map-equiv e)) ≃ Σ B C
equiv-Σ-equiv-base C (pair f is-equiv-f) =
  pair (map-Σ-map-base f C) (is-equiv-map-Σ-map-base C f is-equiv-f)

{- Now we combine the two parts of this section. -}

map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  Σ A C → Σ B D
map-Σ D f g t = pair (f (pr1 t)) (g (pr1 t) (pr2 t))

{- A special case of toto is the functoriality of the cartesian product. -}

{- triangle -}

triangle-map-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
  (map-Σ D f g) ~ ((map-Σ-map-base f D) ∘ (tot g))
triangle-map-Σ D f g t = refl

abstract
  is-equiv-map-Σ :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
    (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
    is-equiv f → (is-fiberwise-equiv g) →
    is-equiv (map-Σ D f g)
  is-equiv-map-Σ
    D f g is-equiv-f is-fiberwise-equiv-g =
    is-equiv-comp
      ( map-Σ D f g)
      ( map-Σ-map-base f D)
      ( tot g)
      ( triangle-map-Σ D f g)
      ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
      ( is-equiv-map-Σ-map-base D f is-equiv-f)

equiv-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4) (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) →
  Σ A C ≃ Σ B D
equiv-Σ D e g =
  pair
    ( map-Σ D (map-equiv e) (λ x → map-equiv (g x)))
    ( is-equiv-map-Σ D
      ( map-equiv e)
      ( λ x → map-equiv (g x))
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x)))

abstract
  is-fiberwise-equiv-is-equiv-map-Σ :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
    (D : B → UU l4) (f : A → B) (g : (x : A) → C x → D (f x)) →
    is-equiv f → is-equiv (map-Σ D f g) → is-fiberwise-equiv g
  is-fiberwise-equiv-is-equiv-map-Σ
    D f g is-equiv-f is-equiv-map-Σ-fg =
    is-fiberwise-equiv-is-equiv-tot g
      ( is-equiv-right-factor
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-equiv-map-Σ-map-base D f is-equiv-f)
        ( is-equiv-map-Σ-fg))

--------------------------------------------------------------------------------

-- Section 11.2 The fundamental theorem

-- The general form of the fundamental theorem of identity types

abstract
  fundamental-theorem-id :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
  fundamental-theorem-id {A = A} a b is-contr-AB f =
    is-fiberwise-equiv-is-equiv-tot f
      ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

abstract
  fundamental-theorem-id' :
    {i j : Level} {A : UU i} {B : A → UU j}
    (a : A) (b : B a) (f : (x : A) → Id a x → B x) →
    is-fiberwise-equiv f → is-contr (Σ A B)
  fundamental-theorem-id' {A = A} {B = B} a b f is-fiberwise-equiv-f =
    is-contr-is-equiv'
      ( Σ A (Id a))
      ( tot f)
      ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
      ( is-contr-total-path a)

-- The canonical form of the fundamental theorem of identity types

abstract 
  fundamental-theorem-id-J :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
  fundamental-theorem-id-J {i} {j} {A} {B} a b is-contr-AB =
    fundamental-theorem-id a b is-contr-AB (ind-Id a (λ x p → B x) b)

-- The converse of the fundamental theorem of identity types

abstract
  fundamental-theorem-id-J' :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
  fundamental-theorem-id-J' {i} {j} {A} {B} a b H =
    is-contr-is-equiv'
      ( Σ A (Id a))
      ( tot (ind-Id a (λ x p → B x) b))
      ( is-equiv-tot-is-fiberwise-equiv H)
      ( is-contr-total-path a)

-- We characterize the identity type of the natural numbers.

center-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m)
center-total-Eq-ℕ m = pair m (refl-Eq-ℕ m)

map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
map-total-Eq-ℕ m (pair n e) = pair (succ-ℕ n) e

contraction-total-Eq-ℕ :
  (m : ℕ) (x : Σ ℕ (Eq-ℕ m)) → Id (center-total-Eq-ℕ m) x
contraction-total-Eq-ℕ zero-ℕ (pair zero-ℕ star) = refl
contraction-total-Eq-ℕ (succ-ℕ m) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (contraction-total-Eq-ℕ m (pair n e))

is-contr-total-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
is-contr-total-Eq-ℕ m =
  pair (center-total-Eq-ℕ m) (contraction-total-Eq-ℕ m)

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id m
    ( refl-Eq-ℕ m)
    ( is-contr-total-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)

-- As an application we show that equivalences are embeddings.
is-emb :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) → UU (i ⊔ j)
is-emb f = (x y : _) → is-equiv (ap f {x} {y})

_↪_ :
  {i j : Level} → UU i → UU j → UU (i ⊔ j)
A ↪ B = Σ (A → B) is-emb

map-emb :
  {i j : Level} {A : UU i} {B : UU j} → A ↪ B → A → B
map-emb f = pr1 f

is-emb-map-emb :
  { i j : Level} {A : UU i} {B : UU j} (f : A ↪ B) → is-emb (map-emb f)
is-emb-map-emb f = pr2 f

equiv-ap-emb :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ↪ B) {x y : A} →
  Id x y ≃ Id (map-emb e x) (map-emb e y)
equiv-ap-emb e {x} {y} = pair (ap (map-emb e)) (is-emb-map-emb e x y)

is-injective-is-emb : {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-emb f → is-injective f
is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

is-injective-emb :
  {i j : Level} {A : UU i} {B : UU j} (e : A ↪ B) → is-injective (map-emb e)
is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

is-emb-is-equiv :
  {i j : Level} {A : UU i} {B : UU j} {f : A → B} → is-equiv f → is-emb f
is-emb-is-equiv {i} {j} {A} {B} {f} is-equiv-f x =
  fundamental-theorem-id x refl
    ( is-contr-equiv
      ( fib f (f x))
      ( equiv-tot (λ y → equiv-inv (f x) (f y)))
      ( is-contr-map-is-equiv is-equiv-f (f x)))
    ( λ y p → ap f p)

emb-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) → (A ↪ B)
emb-equiv e =
  pair (map-equiv e) (is-emb-is-equiv (is-equiv-map-equiv e))

emb-id :
  {i : Level} {A : UU i} → (A ↪ A)
emb-id {i} {A} = emb-equiv equiv-id

is-emb-id : {l : Level} {A : UU l} → is-emb (id {A = A})
is-emb-id = is-emb-map-emb emb-id

equiv-ap :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x y : A) →
  (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
equiv-ap e x y =
  pair
    ( ap (map-equiv e) {x} {y})
    ( is-emb-is-equiv (is-equiv-map-equiv e) x y)

-- Section 11.3 Identity systems

IND-identity-system :
  {i j : Level} (k : Level) {A : UU i} (B : A → UU j) (a : A) (b : B a) → UU _
IND-identity-system k {A} B a b =
  ( P : (x : A) (y : B x) → UU k) →
    sec (λ (h : (x : A) (y : B x) → P x y) → h a b)

fam-Σ :
  {i j k : Level} {A : UU i} {B : A → UU j} (C : (x : A) → B x → UU k) →
  Σ A B → UU k
fam-Σ C (pair x y) = C x y

abstract
  ind-identity-system :
    {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) (P : (x : A) → B x → UU k) →
    P a b → (x : A) (y : B x) → P x y
  ind-identity-system a b is-contr-AB P p x y =
    tr ( fam-Σ P)
       ( eq-is-contr is-contr-AB)
       ( p)

  comp-identity-system :
    {i j k : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) →
    (P : (x : A) → B x → UU k) (p : P a b) →
    Id (ind-identity-system a b is-contr-AB P p a b) p
  comp-identity-system a b is-contr-AB P p =
    ap ( λ t → tr (fam-Σ P) t p)
       ( eq-is-contr'
         ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
         ( eq-is-contr is-contr-AB)
         ( refl))

  Ind-identity-system :
    {i j : Level} (k : Level) {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    (is-contr-AB : is-contr (Σ A B)) →
    IND-identity-system k B a b
  Ind-identity-system k a b is-contr-AB P =
    pair
      ( ind-identity-system a b is-contr-AB P)
      ( comp-identity-system a b is-contr-AB P)
  
contraction-total-space-IND-identity-system :
  {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
  IND-identity-system (i ⊔ j) B a b →
  (t : Σ A B) → Id (pair a b) t
contraction-total-space-IND-identity-system a b ind (pair x y) =
  pr1 (ind (λ x' y' → Id (pair a b) (pair x' y'))) refl x y

abstract
  is-contr-total-space-IND-identity-system :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    IND-identity-system (i ⊔ j) B a b → is-contr (Σ A B)
  is-contr-total-space-IND-identity-system a b ind =
    pair
      ( pair a b)
      ( contraction-total-space-IND-identity-system a b ind)

abstract
  fundamental-theorem-id-IND-identity-system :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) (b : B a) →
    IND-identity-system (i ⊔ j) B a b →
    (f : (x : A) → Id a x → B x) → (x : A) → is-equiv (f x)
  fundamental-theorem-id-IND-identity-system a b ind f =
    fundamental-theorem-id a b (is-contr-total-space-IND-identity-system a b ind) f

--------------------------------------------------------------------------------

{- Raising universe levels -}

issec-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : raise l A) →
  Id (map-raise (map-inv-raise x)) x
issec-map-inv-raise (map-raise x) = refl

isretr-map-inv-raise :
  {l l1 : Level} {A : UU l1} (x : A) → Id (map-inv-raise {l} (map-raise x)) x
isretr-map-inv-raise x = refl

is-equiv-map-raise :
  (l : Level) {l1 : Level} (A : UU l1) → is-equiv (map-raise {l} {l1} {A})
is-equiv-map-raise l A =
  is-equiv-has-inverse
    map-inv-raise
    ( issec-map-inv-raise)
    ( isretr-map-inv-raise {l})

equiv-raise : (l : Level) {l1 : Level} (A : UU l1) → A ≃ raise l A
equiv-raise l A = pair map-raise (is-equiv-map-raise l A)

equiv-raise-unit : (l : Level) → unit ≃ raise-unit l
equiv-raise-unit l = equiv-raise l unit

equiv-raise-empty : (l : Level) → empty ≃ raise-empty l
equiv-raise-empty l = equiv-raise l empty

Raise :
  (l : Level) {l1 : Level} (A : UU l1) → Σ (UU (l1 ⊔ l)) (λ X → A ≃ X)
Raise l A = pair (raise l A) (equiv-raise l A)

--------------------------------------------------------------------------------

-- Section 11.4 Disjointness of coproducts

-- The identity types of coproducts

abstract
  is-contr-total-Eq-coprod-inl :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
    is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
  is-contr-total-Eq-coprod-inl A B x =
    is-contr-equiv
      ( coprod
        ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
        ( Σ B (λ y → Eq-coprod A B (inl x) (inr y))))
      ( right-distributive-Σ-coprod A B (Eq-coprod A B (inl x)))
      ( is-contr-equiv'
        ( coprod
          ( Σ A (Id x))
          ( Σ B (λ y → empty)))
        ( equiv-coprod
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( equiv-tot (λ y → equiv-raise _ empty)))
        ( is-contr-equiv
          ( coprod (Σ A (Id x)) empty)
          ( equiv-coprod equiv-id (right-absorption-Σ B))
          ( is-contr-equiv'
            ( Σ A (Id x))
            ( inv-right-unit-law-coprod (Σ A (Id x)))
            ( is-contr-total-path x))))

abstract
  is-contr-total-Eq-coprod-inr :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
    is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
  is-contr-total-Eq-coprod-inr A B x =
    is-contr-equiv
      ( coprod
        ( Σ A (λ y → Eq-coprod A B (inr x) (inl y)))
        ( Σ B (λ y → Eq-coprod A B (inr x) (inr y))))
      ( right-distributive-Σ-coprod A B (Eq-coprod A B (inr x)))
      ( is-contr-equiv'
        ( coprod (Σ A (λ y → empty)) (Σ B (Id x)))
        ( equiv-coprod
          ( equiv-tot (λ y → equiv-raise _ empty))
          ( equiv-tot (λ y → equiv-raise _ (Id x y))))
        ( is-contr-equiv
          ( coprod empty (Σ B (Id x)))
          ( equiv-coprod (right-absorption-Σ A) equiv-id)
          ( is-contr-equiv'
            ( Σ B (Id x))
            ( inv-left-unit-law-coprod (Σ B (Id x)))
            ( is-contr-total-path x))))

abstract
  is-equiv-Eq-eq-coprod-inl :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : A) →
    is-fiberwise-equiv (Eq-eq-coprod A B (inl x))
  is-equiv-Eq-eq-coprod-inl A B x =
    fundamental-theorem-id
      ( inl x)
      ( reflexive-Eq-coprod A B (inl x))
      ( is-contr-total-Eq-coprod-inl A B x)
      ( Eq-eq-coprod A B (inl x))

abstract
  is-equiv-Eq-eq-coprod-inr :
    {l1 l2 : Level} (A : UU l1) (B : UU l2) (x : B) →
    is-fiberwise-equiv (Eq-eq-coprod A B (inr x))
  is-equiv-Eq-eq-coprod-inr A B x =
    fundamental-theorem-id
      ( inr x)
      ( reflexive-Eq-coprod A B (inr x))
      ( is-contr-total-Eq-coprod-inr A B x)
      ( Eq-eq-coprod A B (inr x))

abstract
  is-equiv-Eq-eq-coprod :
    {l1 l2 : Level} (A : UU l1) (B : UU l2)
    (s : coprod A B) → is-fiberwise-equiv (Eq-eq-coprod A B s)
  is-equiv-Eq-eq-coprod A B (inl x) = is-equiv-Eq-eq-coprod-inl A B x
  is-equiv-Eq-eq-coprod A B (inr x) = is-equiv-Eq-eq-coprod-inr A B x

equiv-Eq-eq-coprod :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) (x y : coprod A B) →
  Id x y ≃ Eq-coprod A B x y
equiv-Eq-eq-coprod A B x y =
  pair (Eq-eq-coprod A B x y) (is-equiv-Eq-eq-coprod A B x y)

map-compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
map-compute-eq-coprod-inl-inl x x' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x'))) ∘
    ( Eq-eq-coprod _ _ (inl x) (inl x')) 

abstract
  is-equiv-map-compute-eq-coprod-inl-inl :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl {B = B} x x')
  is-equiv-map-compute-eq-coprod-inl-inl x x' =
    is-equiv-comp
      ( map-compute-eq-coprod-inl-inl x x')
      ( map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))
      ( Eq-eq-coprod _ _ (inl x) (inl x'))
      ( refl-htpy)
      ( is-equiv-Eq-eq-coprod _ _ (inl x) (inl x'))
      ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id x x')))

compute-eq-coprod-inl-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
compute-eq-coprod-inl-inl x x' =
  pair
    ( map-compute-eq-coprod-inl-inl x x')
    ( is-equiv-map-compute-eq-coprod-inl-inl x x')

map-compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → Id (inl x) (inr y') → empty
map-compute-eq-coprod-inl-inr x y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
    ( Eq-eq-coprod _ _ (inl x) (inr y'))

abstract
  is-equiv-map-compute-eq-coprod-inl-inr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
  is-equiv-map-compute-eq-coprod-inl-inr x y' =
    is-equiv-comp
      ( map-compute-eq-coprod-inl-inr x y')
      ( map-inv-is-equiv (is-equiv-map-raise _ empty))
      ( Eq-eq-coprod _ _ (inl x) (inr y'))
      ( refl-htpy)
      ( is-equiv-Eq-eq-coprod _ _ (inl x) (inr y'))
      ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))
  
compute-eq-coprod-inl-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
compute-eq-coprod-inl-inr x y' =
  pair
    ( map-compute-eq-coprod-inl-inr x y')
    ( is-equiv-map-compute-eq-coprod-inl-inr x y')

map-compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
map-compute-eq-coprod-inr-inl y x' =
   ( map-inv-is-equiv (is-equiv-map-raise _ empty)) ∘
     ( Eq-eq-coprod _ _ (inr y) (inl x'))

abstract
  is-equiv-map-compute-eq-coprod-inr-inl :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
  is-equiv-map-compute-eq-coprod-inr-inl y x' =
    is-equiv-comp
      ( map-compute-eq-coprod-inr-inl y x')
      ( map-inv-is-equiv (is-equiv-map-raise _ empty))
      ( Eq-eq-coprod _ _ (inr y) (inl x'))
      ( refl-htpy)
      ( is-equiv-Eq-eq-coprod _ _ (inr y) (inl x'))
      ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ empty))

compute-eq-coprod-inr-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
compute-eq-coprod-inr-inl y x' =
  pair
    ( map-compute-eq-coprod-inr-inl y x')
    ( is-equiv-map-compute-eq-coprod-inr-inl y x')

map-compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
map-compute-eq-coprod-inr-inr y y' =
  ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y'))) ∘
    ( Eq-eq-coprod _ _ (inr y) (inr y'))

abstract
  is-equiv-map-compute-eq-coprod-inr-inr :
    {l1 l2 : Level} {A : UU l1} {B : UU l2}
    (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr {A = A} y y')
  is-equiv-map-compute-eq-coprod-inr-inr y y' =
    is-equiv-comp
      ( map-compute-eq-coprod-inr-inr y y')
      ( map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))
      ( Eq-eq-coprod _ _ (inr y) (inr y'))
      ( refl-htpy)
      ( is-equiv-Eq-eq-coprod _ _ (inr y) (inr y'))
      ( is-equiv-map-inv-is-equiv (is-equiv-map-raise _ (Id y y')))

compute-eq-coprod-inr-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
compute-eq-coprod-inr-inr y y' =
  pair
    ( map-compute-eq-coprod-inr-inr y y')
    ( is-equiv-map-compute-eq-coprod-inr-inr y y')

--------------------------------------------------------------------------------

-- Section 11.6 The structure identity principle

-- Theorem 11.6.2

swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
  Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) =
  pair (pair a c) (pair b d)

htpy-swap-total-Eq-structure :
  {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
  (D : (x : A) → B x → C x → UU l4) →
  ( ( swap-total-Eq-structure B C D) ∘
    ( swap-total-Eq-structure C B (λ x z y → D x y z))) ~ id
htpy-swap-total-Eq-structure B C D (pair (pair a b) (pair c d)) = refl

abstract
  is-equiv-swap-total-Eq-structure :
    {l1 l2 l3 l4 : Level} {A : UU l1} (B : A → UU l2) (C : A → UU l3)
    (D : (x : A) → B x → C x → UU l4) →
    is-equiv (swap-total-Eq-structure B C D)
  is-equiv-swap-total-Eq-structure B C D =
    is-equiv-has-inverse
      ( swap-total-Eq-structure C B (λ x z y → D x y z))
      ( htpy-swap-total-Eq-structure B C D)
      ( htpy-swap-total-Eq-structure C B (λ x z y → D x y z))

abstract
  is-contr-Σ :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-contr A → ((x : A) → is-contr (B x)) → is-contr (Σ A B)
  is-contr-Σ {A = A} {B = B} is-contr-A is-contr-B =
    is-contr-equiv
      ( B (center is-contr-A))
      ( left-unit-law-Σ-is-contr is-contr-A (center is-contr-A))
      ( is-contr-B (center is-contr-A))

abstract
  is-contr-Σ' :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-contr A → (a : A) → is-contr (B a) → is-contr (Σ A B)
  is-contr-Σ' {A = A} {B} is-contr-A a is-contr-B =
    is-contr-equiv
      ( B a)
      ( left-unit-law-Σ-is-contr is-contr-A a)
      ( is-contr-B)

abstract
  is-contr-total-Eq-structure :
    { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
    ( D : (x : A) → B x → C x → UU l4) →
    ( is-contr-AC : is-contr (Σ A C)) →
    ( t : Σ A C) →
    is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
  is-contr-total-Eq-structure
    {A = A} {B = B} {C = C} D is-contr-AC t is-contr-BD =
    is-contr-is-equiv
      ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
      ( swap-total-Eq-structure B C D)
      ( is-equiv-swap-total-Eq-structure B C D)
      ( is-contr-Σ' is-contr-AC t is-contr-BD)

-- Example 11.6.3

-- Characterizing the identity type of a fiber as the fiber of the action on
-- paths

fib-ap-eq-fib-fiberwise :
  {i j : Level} {A : UU i} {B : UU j}
  (f : A → B) {b : B} (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
  (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
  (Id (ap f p) ((pr2 s) ∙ (inv (pr2 t))))
fib-ap-eq-fib-fiberwise f (pair .x' p) (pair x' refl) refl =
  inv ∘ (concat right-unit refl)

abstract
  is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B} (s t : fib f b) →
    is-fiberwise-equiv (fib-ap-eq-fib-fiberwise f s t)
  is-fiberwise-equiv-fib-ap-eq-fib-fiberwise
    f (pair x y) (pair .x refl) refl =
    is-equiv-comp
      ( fib-ap-eq-fib-fiberwise f (pair x y) (pair x refl) refl)
      ( inv)
      ( concat right-unit refl)
      ( refl-htpy)
      ( is-equiv-concat right-unit refl)
      ( is-equiv-inv (y ∙ refl) refl)

fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
  (s t : fib f b) → Id s t →
  fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
fib-ap-eq-fib f s .s refl = pair refl (inv (right-inv (pr2 s)))

triangle-fib-ap-eq-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B)
  {b : B} (s t : fib f b) →
  ( fib-ap-eq-fib f s t) ~
  ( (tot (fib-ap-eq-fib-fiberwise f s t)) ∘ (pair-eq-Σ {s = s} {t}))
triangle-fib-ap-eq-fib f (pair x refl) .(pair x refl) refl = refl

abstract
  is-equiv-fib-ap-eq-fib :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) {b : B}
    (s t : fib f b) → is-equiv (fib-ap-eq-fib f s t)
  is-equiv-fib-ap-eq-fib f s t =
    is-equiv-comp
      ( fib-ap-eq-fib f s t)
      ( tot (fib-ap-eq-fib-fiberwise f s t))
      ( pair-eq-Σ {s = s} {t})
      ( triangle-fib-ap-eq-fib f s t)
      ( is-equiv-pair-eq-Σ s t)
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise f s t))

eq-fib-fib-ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
  (q : Id (f x) (f y)) →
  Id (pair x q) (pair y (refl {x = f y})) → fib (ap f {x = x} {y = y}) q
eq-fib-fib-ap f x y q = (tr (fib (ap f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

abstract
  is-equiv-eq-fib-fib-ap :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x y : A)
    (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap f x y q)
  is-equiv-eq-fib-fib-ap f x y q =
    is-equiv-comp
      ( eq-fib-fib-ap f x y q)
      ( tr (fib (ap f)) right-unit)
      ( fib-ap-eq-fib f (pair x q) (pair y refl))
      ( refl-htpy)
      ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
      ( is-equiv-tr (fib (ap f)) right-unit)

-- Comparing fib and fib'

fib'-fib :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (y : B) →
  fib f y → fib' f y
fib'-fib f y t = tot (λ x → inv) t

abstract
  is-equiv-fib'-fib :
    {i j : Level} {A : UU i} {B : UU j}
    (f : A → B) → is-fiberwise-equiv (fib'-fib f)
  is-equiv-fib'-fib f y =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-inv (f x) y)

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 11.1

abstract
  is-emb-ex-falso :
    {i : Level} (A : UU i) → is-emb (ex-falso {A = A})
  is-emb-ex-falso A ()

abstract
  is-emb-inl :
    {i j : Level} (A : UU i) (B : UU j) → is-emb (inl {A = A} {B = B})
  is-emb-inl A B x =
    fundamental-theorem-id x refl
      ( is-contr-is-equiv
        ( Σ A (λ y → Eq-coprod A B (inl x) (inl y)))
        ( tot (λ y → Eq-eq-coprod A B (inl x) (inl y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-Eq-eq-coprod A B (inl x) (inl y)))
        ( is-contr-equiv'
          ( Σ A (Id x))
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( is-contr-total-path x)))
      ( λ y → ap inl)

emb-inl :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ↪ coprod A B
emb-inl {l1} {l2} {A} {B} = pair inl (is-emb-inl A B)

abstract
  is-emb-inr :
    {i j : Level} (A : UU i) (B : UU j) → is-emb (inr {A = A} {B = B})
  is-emb-inr A B x =
    fundamental-theorem-id x refl
      ( is-contr-is-equiv
        ( Σ B (λ y → Eq-coprod A B (inr x) (inr y)))
        ( tot (λ y → Eq-eq-coprod A B (inr x) (inr y)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ y → is-equiv-Eq-eq-coprod A B (inr x) (inr y)))
        ( is-contr-equiv'
          ( Σ B (Id x))
          ( equiv-tot (λ y → equiv-raise _ (Id x y)))
          ( is-contr-total-path x)))
      ( λ y → ap inr)

emb-inr :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → B ↪ coprod A B
emb-inr {l1} {l2} {A} {B} = pair inr (is-emb-inr A B)

is-empty-right-summand-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-equiv (inl {A = A} {B = B}) →
  is-empty B
is-empty-right-summand-is-equiv {A = A} {B} H b =
  map-inv-raise
    ( Eq-eq-coprod A B
      ( inl (pr1 (center (is-contr-map-is-equiv H (inr b)))))
      ( inr b)
      ( pr2 (center (is-contr-map-is-equiv H (inr b)))))

is-empty-left-summand-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → is-equiv (inr {A = A} {B = B}) →
  is-empty A
is-empty-left-summand-is-equiv {A = A} {B} H a =
  map-inv-raise
    ( Eq-eq-coprod A B
      ( inr (pr1 (center (is-contr-map-is-equiv H (inl a)))))
      ( inl a)
      ( pr2 (center (is-contr-map-is-equiv H (inl a)))))

-- Exercise 11.2

-- Exercise 11.2

eq-transpose-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) (x : A) (y : B) →
  (Id (map-equiv e x) y) ≃ (Id x (map-inv-equiv e y))
eq-transpose-equiv e x y =
  ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
  ( equiv-concat'
    ( map-equiv e x)
    ( inv (issec-map-inv-equiv e y)))

map-eq-transpose-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {x : A} {y : B} →
  Id (map-equiv e x) y → Id x (map-inv-equiv e y)
map-eq-transpose-equiv e {x} {y} = map-equiv (eq-transpose-equiv e x y)

inv-map-eq-transpose-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {x : A} {y : B} →
  Id x (map-inv-equiv e y) → Id (map-equiv e x) y
inv-map-eq-transpose-equiv e {x} {y} = map-inv-equiv (eq-transpose-equiv e x y)

triangle-eq-transpose-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {x : A} {y : B}
  (p : Id (map-equiv e x) y) →
  Id ( ( ap (map-equiv e) (map-eq-transpose-equiv e p)) ∙
       ( issec-map-inv-equiv e y))
     ( p)
triangle-eq-transpose-equiv e {x} {y} p =
  ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
       ( issec-map-inv-equiv
         ( equiv-ap e x (map-inv-equiv e y))
         ( p ∙ inv (issec-map-inv-equiv e y)))) ∙
  ( ( assoc p (inv (issec-map-inv-equiv e y)) (issec-map-inv-equiv e y)) ∙
    ( ( ap (concat p y) (left-inv (issec-map-inv-equiv e y))) ∙ right-unit))

map-eq-transpose-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {a : A} {b : B} →
  Id b (map-equiv e a) → Id (map-inv-equiv e b) a
map-eq-transpose-equiv' e p = inv (map-eq-transpose-equiv e (inv p))

inv-map-eq-transpose-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {a : A} {b : B} →
  Id (map-inv-equiv e b) a → Id b (map-equiv e a)
inv-map-eq-transpose-equiv' e p =
  inv (inv-map-eq-transpose-equiv e (inv p))

triangle-eq-transpose-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) {x : A} {y : B} →
  (p : Id y (map-equiv e x)) →
  Id ( (issec-map-inv-equiv e y) ∙ p)
     ( ap (map-equiv e) (map-eq-transpose-equiv' e p))
triangle-eq-transpose-equiv' e {x} {y} p =
  map-inv-equiv
    ( equiv-ap
      ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
      ( (issec-map-inv-equiv e y) ∙ p)
      ( ap (map-equiv e) (map-eq-transpose-equiv' e p)))
    ( ( distributive-inv-concat (issec-map-inv-equiv e y) p) ∙
      ( ( inv
          ( con-inv
            ( ap (map-equiv e) (inv (map-eq-transpose-equiv' e p)))
            ( issec-map-inv-equiv e y)
            ( inv p)
            ( ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
                   ( ap ( ap (map-equiv e))
                        ( inv-inv
                          ( map-inv-equiv
                            ( equiv-ap e x (map-inv-equiv e y))
                            ( ( inv p) ∙
                              ( inv (issec-map-inv-equiv e y))))))) ∙
              ( triangle-eq-transpose-equiv e (inv p))))) ∙
        ( ap-inv (map-equiv e) (map-eq-transpose-equiv' e p))))

-- Exercise 11.3

abstract
  is-equiv-top-is-equiv-left-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    is-equiv i → is-equiv f → is-equiv g → is-equiv h
  is-equiv-top-is-equiv-left-square f g h i H is-equiv-i is-equiv-f is-equiv-g =
    is-equiv-right-factor (i ∘ f) g h H is-equiv-g
      ( is-equiv-comp' i f is-equiv-f is-equiv-i)

abstract
  is-emb-htpy :
    {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
    is-emb g → is-emb f
  is-emb-htpy f g H is-emb-g x y =
    is-equiv-top-is-equiv-left-square
      ( ap g)
      ( concat' (f x) (H y))
      ( ap f)
      ( concat (H x) (g y))
      ( htpy-nat H)
      ( is-equiv-concat (H x) (g y))
      ( is-emb-g x y)
      ( is-equiv-concat' (f x) (H y))

abstract
  is-emb-htpy' :
    {i j : Level} {A : UU i} {B : UU j} (f g : A → B) → (f ~ g) →
    is-emb f → is-emb g
  is-emb-htpy' f g H is-emb-f =
    is-emb-htpy g f (inv-htpy H) is-emb-f

-- Exercise 11.4

abstract
  is-emb-comp :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
    is-emb h → is-emb f
  is-emb-comp f g h H is-emb-g is-emb-h =
    is-emb-htpy f (g ∘ h) H
      ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
        ( is-emb-h x y)
        ( is-emb-g (h x) (h y)))

abstract
  is-emb-comp' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (g : B → X) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
  is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

  comp-emb :
    {i j k : Level} {A : UU i} {B : UU j} {C : UU k} →
    (B ↪ C) → (A ↪ B) → (A ↪ C)
  comp-emb (pair g H) (pair f K) = pair (g ∘ f) (is-emb-comp' g f H K)

abstract
  is-emb-right-factor :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
    is-emb f → is-emb h
  is-emb-right-factor f g h H is-emb-g is-emb-f x y =
    is-equiv-right-factor
      ( ap (g ∘ h))
      ( ap g)
      ( ap h)
      ( ap-comp g h)
      ( is-emb-g (h x) (h y))
      ( is-emb-htpy (g ∘ h) f (inv-htpy H) is-emb-f x y)

abstract
  is-emb-triangle-is-equiv :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
    is-equiv e → is-emb g → is-emb f
  is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
    is-emb-comp f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

abstract
  is-emb-triangle-is-equiv' :
    {i j k : Level} {A : UU i} {B : UU j} {X : UU k}
    (f : A → X) (g : B → X) (e : A → B) (H : f ~ (g ∘ e)) →
    is-equiv e → is-emb f → is-emb g
  is-emb-triangle-is-equiv' f g e H is-equiv-e is-emb-f =
    is-emb-triangle-is-equiv g f
      ( map-inv-is-equiv is-equiv-e)
      ( triangle-section f g e H
        ( pair
          ( map-inv-is-equiv is-equiv-e)
          ( issec-map-inv-is-equiv is-equiv-e)))
      ( is-equiv-map-inv-is-equiv is-equiv-e)
      ( is-emb-f)

-- Exercise 11.5

-- Exercise 11.6

is-emb-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {f : A → C} {g : B → C} → is-emb f → is-emb g → ((a : A) (b : B) →
  ¬ (Id (f a) (g b))) → is-emb (ind-coprod (λ x → C) f g)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inl a') =
  is-equiv-left-factor
    ( ap f)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inl)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
    ( H a a')
    ( is-emb-inl A B a a')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inl a) (inr b') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inl a') =
  is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
is-emb-coprod {A = A} {B} {C} {f} {g} H K L (inr b) (inr b') =
  is-equiv-left-factor
    ( ap g)
    ( ap (ind-coprod (λ x → C) f g))
    ( ap inr)
    ( λ p → ap-comp (ind-coprod (λ x → C) f g) inr p)
    ( K b b')
    ( is-emb-inr A B b b')

-- Exercise 11.7

-- Exercise 11.8

tot-htpy :
  {i j k : Level} {A : UU i} {B : A → UU j} {C : A → UU k}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-Σ refl (H x y)

tot-id :
  {i j : Level} {A : UU i} (B : A → UU j) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B (pair x y) = refl

tot-comp :
  {i j j' j'' : Level}
  {A : UU i} {B : A → UU j} {B' : A → UU j'} {B'' : A → UU j''}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
tot-comp f g (pair x y) = refl

-- Exercise 11.9

abstract
  fundamental-theorem-id-retr :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A) →
    (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
    is-fiberwise-equiv i
  fundamental-theorem-id-retr {_} {_} {A} {B} a i R =
    is-fiberwise-equiv-is-equiv-tot i
      ( is-equiv-is-contr (tot i)
        ( is-contr-retract-of (Σ _ (λ y → Id a y))
          ( pair (tot i)
            ( pair (tot λ x → pr1 (R x))
              ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
                ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
          ( is-contr-total-path a))
        ( is-contr-total-path a))

abstract
  is-equiv-sec-is-equiv :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) (sec-f : sec f) →
    is-equiv (pr1 sec-f) → is-equiv f
  is-equiv-sec-is-equiv {A = A} {B = B} f (pair g issec-g) is-equiv-sec-f =
    let h : A → B
        h = map-inv-is-equiv is-equiv-sec-f
    in
    is-equiv-htpy h
      ( ( htpy-left-whisk f (inv-htpy (issec-map-inv-is-equiv is-equiv-sec-f))) ∙h
        ( htpy-right-whisk issec-g h))
      ( is-equiv-map-inv-is-equiv is-equiv-sec-f)

abstract
  fundamental-theorem-id-sec :
    {i j : Level} {A : UU i} {B : A → UU j} (a : A)
    (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
    is-fiberwise-equiv f
  fundamental-theorem-id-sec {A = A} {B = B} a f sec-f x =
    let i : (x : A) → B x → Id a x
        i = λ x → pr1 (sec-f x)
        retr-i : (x : A) → retr (i x)
        retr-i = λ x → pair (f x) (pr2 (sec-f x))
        is-fiberwise-equiv-i : is-fiberwise-equiv i
        is-fiberwise-equiv-i = fundamental-theorem-id-retr a i retr-i
    in is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)

-- Exercise 11.10

abstract
  is-emb-sec-ap :
    {i j : Level} {A : UU i} {B : UU j} (f : A → B) →
    ((x y : A) → sec (ap f {x = x} {y = y})) → is-emb f
  is-emb-sec-ap f sec-ap-f x y =
    fundamental-theorem-id-sec x (λ y → ap f {y = y}) (sec-ap-f x) y

-- Exercise 11.11

is-path-split :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-path-split {A = A} {B = B} f =
  sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

abstract
  is-path-split-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv f → is-path-split f
  is-path-split-is-equiv f is-equiv-f =
    pair (pr1 is-equiv-f) (λ x y → pr1 (is-emb-is-equiv is-equiv-f x y))

abstract
  is-coherently-invertible-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-path-split f → is-coherently-invertible f
  is-coherently-invertible-is-path-split {A = A} {B = B} f
    ( pair (pair g issec-g) sec-ap-f) =
    let φ : ((x : A) → fib (ap f) (issec-g (f x))) →
                Σ ((g ∘ f) ~ id)
                ( λ H → (htpy-right-whisk issec-g f) ~ (htpy-left-whisk f H))
        φ =  ( tot (λ H' → inv-htpy)) ∘
               ( λ s → pair (λ x → pr1 (s x)) (λ x → pr2 (s x)))
    in
    pair g
      ( pair issec-g
        ( φ (λ x → pair
          ( pr1 (sec-ap-f (g (f x)) x) (issec-g (f x)))
          ( pr2 (sec-ap-f (g (f x)) x) (issec-g (f x))))))

abstract
  is-equiv-is-coherently-invertible :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    (f : A → B) → is-coherently-invertible f → is-equiv f
  is-equiv-is-coherently-invertible f (pair g (pair G (pair H K))) =
    is-equiv-has-inverse g G H

abstract
  is-equiv-is-path-split :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-path-split f → is-equiv f
  is-equiv-is-path-split f =
    ( is-equiv-is-coherently-invertible f) ∘
    ( is-coherently-invertible-is-path-split f)

abstract
  is-coherently-invertible-is-equiv :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-equiv f → is-coherently-invertible f
  is-coherently-invertible-is-equiv f =
    ( is-coherently-invertible-is-path-split f) ∘ (is-path-split-is-equiv f)

-- Exercise 11.12

abstract
  is-equiv-top-is-equiv-bottom-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv f) → (is-equiv g) → (is-equiv i) → (is-equiv h)
  is-equiv-top-is-equiv-bottom-square
    f g h i H is-equiv-f is-equiv-g is-equiv-i =
    is-equiv-right-factor (i ∘ f) g h H is-equiv-g
      ( is-equiv-comp' i f is-equiv-f is-equiv-i)

abstract
  is-equiv-bottom-is-equiv-top-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv f) → (is-equiv g) → (is-equiv h) → (is-equiv i)
  is-equiv-bottom-is-equiv-top-square
    f g h i H is-equiv-f is-equiv-g is-equiv-h = 
    is-equiv-left-factor' i f
      ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g) is-equiv-f

abstract
  is-equiv-left-is-equiv-right-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv h) → (is-equiv i) → (is-equiv g) → (is-equiv f)
  is-equiv-left-is-equiv-right-square
    f g h i H is-equiv-h is-equiv-i is-equiv-g =
    is-equiv-right-factor' i f is-equiv-i
      ( is-equiv-comp (i ∘ f) g h H is-equiv-h is-equiv-g)

abstract
  is-equiv-right-is-equiv-left-square :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
    (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h)) →
    (is-equiv h) → (is-equiv i) → (is-equiv f) → (is-equiv g)
  is-equiv-right-is-equiv-left-square
    f g h i H is-equiv-h is-equiv-i is-equiv-f =
    is-equiv-left-factor (i ∘ f) g h H
      ( is-equiv-comp' i f is-equiv-f is-equiv-i)
      ( is-equiv-h)

fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  (x : X) → (fib f x) → (fib g x)
fib-triangle f g h H .(f a) (pair a refl) = pair (h a) (inv (H a))

fib-triangle' :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (g : B → X) (h : A → B) (x : X) → (fib (g ∘ h) x) → fib g x
fib-triangle' g h x = fib-triangle (g ∘ h) g h refl-htpy x

square-tot-fib-triangle :
  {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
  (h ∘ (map-equiv-total-fib f)) ~
  ((map-equiv-total-fib g) ∘ (tot (fib-triangle f g h H)))
square-tot-fib-triangle f g h H (pair .(f a) (pair a refl)) = refl

abstract
  is-fiberwise-equiv-is-equiv-triangle :
    {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    (E : is-equiv h) → is-fiberwise-equiv (fib-triangle f g h H)
  is-fiberwise-equiv-is-equiv-triangle f g h H E =
    is-fiberwise-equiv-is-equiv-tot
      ( fib-triangle f g h H)
      ( is-equiv-top-is-equiv-bottom-square
        ( map-equiv-total-fib f)
        ( map-equiv-total-fib g)
        ( tot (fib-triangle f g h H))
        ( h)
        ( square-tot-fib-triangle f g h H)
        ( is-equiv-map-equiv-total-fib f)
        ( is-equiv-map-equiv-total-fib g)
        ( E))

abstract
  is-equiv-triangle-is-fiberwise-equiv :
    {i j k : Level} {X : UU i} {A : UU j} {B : UU k}
    (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
    (E : is-fiberwise-equiv (fib-triangle f g h H)) → is-equiv h
  is-equiv-triangle-is-fiberwise-equiv f g h H E =
    is-equiv-bottom-is-equiv-top-square
      ( map-equiv-total-fib f)
      ( map-equiv-total-fib g)
      ( tot (fib-triangle f g h H))
      ( h)
      ( square-tot-fib-triangle f g h H)
      ( is-equiv-map-equiv-total-fib f)
      ( is-equiv-map-equiv-total-fib g)
      ( is-equiv-tot-is-fiberwise-equiv E)

