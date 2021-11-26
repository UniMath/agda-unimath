{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.11-fundamental-theorem where

open import foundations.10-contractible-types public

--------------------------------------------------------------------------------

-- Section 11.1 Families of equivalences

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  {- Any family of maps induces a map on the total spaces. -}
  
  tot : Σ A B → Σ A C
  pr1 (tot t) = pr1 t
  pr2 (tot t) = f (pr1 t) (pr2 t)

  {- We show that for any family of maps, the fiber of the induced map on total
     spaces are equivalent to the fibers of the maps in the family. -}
   
  fib-ftr-fib-tot : (t : Σ A C) → fib tot t → fib (f (pr1 t)) (pr2 t)
  pr1 (fib-ftr-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = y
  pr2 (fib-ftr-fib-tot .(tot (pair x y)) (pair (pair x y) refl)) = refl

  fib-tot-fib-ftr : (t : Σ A C) → fib (f (pr1 t)) (pr2 t) → fib tot t
  pr1 (pr1 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl))) = a
  pr2 (pr1 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl))) = y
  pr2 (fib-tot-fib-ftr (pair a .(f a y)) (pair y refl)) = refl

  issec-fib-tot-fib-ftr :
    (t : Σ A C) → (fib-ftr-fib-tot t ∘ fib-tot-fib-ftr t) ~ id
  issec-fib-tot-fib-ftr (pair x .(f x y)) (pair y refl) = refl

  isretr-fib-tot-fib-ftr :
    (t : Σ A C) → (fib-tot-fib-ftr t ∘ fib-ftr-fib-tot t) ~ id
  isretr-fib-tot-fib-ftr .(pair x (f x y)) (pair (pair x y) refl) = refl

  abstract
    is-equiv-fib-ftr-fib-tot : (t : Σ A C) → is-equiv (fib-ftr-fib-tot t)
    is-equiv-fib-ftr-fib-tot t =
      is-equiv-has-inverse
        ( fib-tot-fib-ftr t)
        ( issec-fib-tot-fib-ftr t)
        ( isretr-fib-tot-fib-ftr t)

  abstract
    is-equiv-fib-tot-fib-ftr : (t : Σ A C) → is-equiv (fib-tot-fib-ftr t)
    is-equiv-fib-tot-fib-ftr t =
      is-equiv-has-inverse
        ( fib-ftr-fib-tot t)
        ( isretr-fib-tot-fib-ftr t)
        ( issec-fib-tot-fib-ftr t)

  {- Now that we have shown that the fibers of the induced map on total spaces
     are equivalent to the fibers of the maps in the family, it follows that
     the induced map on total spaces is an equivalence if and only if each map
     in the family is an equivalence. -}

  is-fiberwise-equiv : UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv = (x : A) → is-equiv (f x)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-equiv-tot-is-fiberwise-equiv : is-fiberwise-equiv f → is-equiv (tot f )
    is-equiv-tot-is-fiberwise-equiv H =
      is-equiv-is-contr-map
        ( λ t →
          is-contr-is-equiv
            ( fib (f (pr1 t)) (pr2 t))
            ( fib-ftr-fib-tot f t)
            ( is-equiv-fib-ftr-fib-tot f t)
            ( is-contr-map-is-equiv (H (pr1 t)) (pr2 t)))

  abstract
    is-fiberwise-equiv-is-equiv-tot : is-equiv (tot f) → is-fiberwise-equiv f
    is-fiberwise-equiv-is-equiv-tot is-equiv-tot-f x =
      is-equiv-is-contr-map
        ( λ z →
          is-contr-is-equiv'
            ( fib (tot f) (pair x z))
            ( fib-ftr-fib-tot f (pair x z))
            ( is-equiv-fib-ftr-fib-tot f (pair x z))
            ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  equiv-tot : ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
  pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
  pr2 (equiv-tot e) =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))

{- In the second part of this section we show that any equivalence f on base 
   types also induces an equivalence on total spaces. -}

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  map-Σ-map-base : Σ A (λ x → C (f x)) → Σ B C
  pr1 (map-Σ-map-base s) = f (pr1 s)
  pr2 (map-Σ-map-base s) = pr2 s

  {- The proof is similar to the previous part: we show that the fibers of f
     and Σ-kap-base-map f C are equivalent. -}

  fib-map-Σ-map-base-fib :
    (t : Σ B C) → fib f (pr1 t) → fib map-Σ-map-base t
  pr1 (pr1 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl))) = x
  pr2 (pr1 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl))) = z
  pr2 (fib-map-Σ-map-base-fib (pair .(f x) z) (pair x refl)) = refl

  fib-fib-map-Σ-map-base :
    (t : Σ B C) → fib map-Σ-map-base t → fib f (pr1 t)
  pr1
    ( fib-fib-map-Σ-map-base
      .(map-Σ-map-base (pair x z)) (pair (pair x z) refl)) = x
  pr2
    ( fib-fib-map-Σ-map-base
      .(map-Σ-map-base (pair x z)) (pair (pair x z) refl)) = refl
  
  issec-fib-fib-map-Σ-map-base :
    (t : Σ B C) → (fib-map-Σ-map-base-fib t ∘ fib-fib-map-Σ-map-base t) ~ id
  issec-fib-fib-map-Σ-map-base .(pair (f x) z) (pair (pair x z) refl) = refl

  isretr-fib-fib-map-Σ-map-base :
    (t : Σ B C) → (fib-fib-map-Σ-map-base t ∘ fib-map-Σ-map-base-fib t) ~ id
  isretr-fib-fib-map-Σ-map-base (pair .(f x) z) (pair x refl) = refl

  abstract
    is-equiv-fib-map-Σ-map-base-fib :
      (t : Σ B C) → is-equiv (fib-map-Σ-map-base-fib t)
    is-equiv-fib-map-Σ-map-base-fib t =
      is-equiv-has-inverse
        ( fib-fib-map-Σ-map-base t)
        ( issec-fib-fib-map-Σ-map-base t)
        ( isretr-fib-fib-map-Σ-map-base t)

  equiv-fib-map-Σ-map-base-fib :
    (t : Σ B C) → fib f (pr1 t) ≃ fib map-Σ-map-base t
  pr1 (equiv-fib-map-Σ-map-base-fib t) = fib-map-Σ-map-base-fib t
  pr2 (equiv-fib-map-Σ-map-base-fib t) = is-equiv-fib-map-Σ-map-base-fib t

  abstract
    is-contr-map-map-Σ-map-base : is-contr-map f → is-contr-map map-Σ-map-base
    is-contr-map-map-Σ-map-base is-contr-f (pair y z) =
      is-contr-is-equiv'
        ( fib f y)
        ( fib-map-Σ-map-base-fib (pair y z))
        ( is-equiv-fib-map-Σ-map-base-fib (pair y z))
        ( is-contr-f y)

  abstract
    is-equiv-map-Σ-map-base : is-equiv f → is-equiv map-Σ-map-base
    is-equiv-map-Σ-map-base is-equiv-f =
      is-equiv-is-contr-map
        ( is-contr-map-map-Σ-map-base (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ (map-equiv e)) ≃ Σ B C
pr1 (equiv-Σ-equiv-base C (pair f is-equiv-f)) = map-Σ-map-base f C
pr2 (equiv-Σ-equiv-base C (pair f is-equiv-f)) =
  is-equiv-map-Σ-map-base f C is-equiv-f

{- Now we combine the two parts of this section. -}

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where
  
  map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
  pr1 (map-Σ f g t) = f (pr1 t)
  pr2 (map-Σ f g t) = g (pr1 t) (pr2 t)

  triangle-map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) →
    (map-Σ f g) ~ (map-Σ-map-base f D ∘ tot g)
  triangle-map-Σ f g t = refl

  abstract
    is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-fiberwise-equiv g → is-equiv (map-Σ f g)
    is-equiv-map-Σ f g is-equiv-f is-fiberwise-equiv-g =
      is-equiv-comp
        ( map-Σ f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ f g)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
        ( is-equiv-map-Σ-map-base f D is-equiv-f)

  equiv-Σ :
    (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) → Σ A C ≃ Σ B D
  pr1 (equiv-Σ e g) = map-Σ (map-equiv e) (λ x → map-equiv (g x))
  pr2 (equiv-Σ e g) =
    is-equiv-map-Σ
      ( map-equiv e)
      ( λ x → map-equiv (g x))
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x))

  abstract
    is-fiberwise-equiv-is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-equiv (map-Σ f g) → is-fiberwise-equiv g
    is-fiberwise-equiv-is-equiv-map-Σ f g H K =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-right-factor
          ( map-Σ f g)
          ( map-Σ-map-base f D)
          ( tot g)
          ( triangle-map-Σ f g)
          ( is-equiv-map-Σ-map-base f D H)
          ( K))

--------------------------------------------------------------------------------

-- Section 11.2 The fundamental theorem

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  -- The general form of the fundamental theorem of identity types
  
  abstract
    fundamental-theorem-id :
      is-contr (Σ A B) → (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f
    fundamental-theorem-id is-contr-AB f =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot f) (is-contr-total-path a) is-contr-AB)

  abstract
    fundamental-theorem-id' :
      (f : (x : A) → Id a x → B x) → is-fiberwise-equiv f → is-contr (Σ A B)
    fundamental-theorem-id' f is-fiberwise-equiv-f =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot f)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-f)
        ( is-contr-total-path a)

  -- The canonical form of the fundamental theorem of identity types
  
  abstract 
    fundamental-theorem-id-J :
      is-contr (Σ A B) → is-fiberwise-equiv (ind-Id a (λ x p → B x) b)
    fundamental-theorem-id-J is-contr-AB =
      fundamental-theorem-id is-contr-AB (ind-Id a (λ x p → B x) b)

  -- The converse of the fundamental theorem of identity types
  
  abstract
    fundamental-theorem-id-J' :
      (is-fiberwise-equiv (ind-Id a (λ x p → B x) b)) → is-contr (Σ A B)
    fundamental-theorem-id-J' H =
      is-contr-is-equiv'
        ( Σ A (Id a))
        ( tot (ind-Id a (λ x p → B x) b))
        ( is-equiv-tot-is-fiberwise-equiv H)
        ( is-contr-total-path a)

-- We characterize the identity type of the natural numbers.

map-total-Eq-ℕ :
  (m : ℕ) → Σ ℕ (Eq-ℕ m) → Σ ℕ (Eq-ℕ (succ-ℕ m))
pr1 (map-total-Eq-ℕ m (pair n e)) = succ-ℕ n
pr2 (map-total-Eq-ℕ m (pair n e)) = e

is-contr-total-Eq-ℕ :
  (m : ℕ) → is-contr (Σ ℕ (Eq-ℕ m))
pr1 (pr1 (is-contr-total-Eq-ℕ m)) = m
pr2 (pr1 (is-contr-total-Eq-ℕ m)) = refl-Eq-ℕ m
pr2 (is-contr-total-Eq-ℕ zero-ℕ) (pair zero-ℕ star) = refl
pr2 (is-contr-total-Eq-ℕ (succ-ℕ m)) (pair (succ-ℕ n) e) =
  ap (map-total-Eq-ℕ m) (pr2 (is-contr-total-Eq-ℕ m) (pair n e))

is-equiv-Eq-eq-ℕ :
  {m n : ℕ} → is-equiv (Eq-eq-ℕ {m} {n})
is-equiv-Eq-eq-ℕ {m} {n} =
  fundamental-theorem-id m
    ( refl-Eq-ℕ m)
    ( is-contr-total-Eq-ℕ m)
    ( λ y → Eq-eq-ℕ {m} {y})
    ( n)

-- As an application we show that equivalences are embeddings.

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb : (A → B) → UU (l1 ⊔ l2)
  is-emb f = (x y : A) → is-equiv (ap f {x} {y})

_↪_ :
  {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↪ B = Σ (A → B) is-emb

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-emb : A ↪ B → A → B
  map-emb f = pr1 f

  is-emb-map-emb : (f : A ↪ B) → is-emb (map-emb f)
  is-emb-map-emb f = pr2 f

  equiv-ap-emb : (e : A ↪ B) {x y : A} → Id x y ≃ Id (map-emb e x) (map-emb e y)
  pr1 (equiv-ap-emb e {x} {y}) = ap (map-emb e)
  pr2 (equiv-ap-emb e {x} {y}) = is-emb-map-emb e x y

  is-injective-is-emb : {f : A → B} → is-emb f → is-injective f
  is-injective-is-emb is-emb-f {x} {y} = map-inv-is-equiv (is-emb-f x y)

  is-injective-emb : (e : A ↪ B) → is-injective (map-emb e)
  is-injective-emb e {x} {y} = map-inv-is-equiv (is-emb-map-emb e x y)

  is-emb-is-equiv : {f : A → B} → is-equiv f → is-emb f
  is-emb-is-equiv {f} is-equiv-f x =
    fundamental-theorem-id x refl
      ( is-contr-equiv
        ( fib f (f x))
        ( equiv-tot (λ y → equiv-inv (f x) (f y)))
        ( is-contr-map-is-equiv is-equiv-f (f x)))
      ( λ y p → ap f p)

  emb-equiv : (A ≃ B) → (A ↪ B)
  pr1 (emb-equiv e) = map-equiv e
  pr2 (emb-equiv e) = is-emb-is-equiv (is-equiv-map-equiv e)

  equiv-ap :
    (e : A ≃ B) (x y : A) → (Id x y) ≃ (Id (map-equiv e x) (map-equiv e y))
  pr1 (equiv-ap e x y) = ap (map-equiv e) {x} {y}
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y

module _
  {l : Level} {A : UU l}
  where

  emb-id : A ↪ A
  emb-id = emb-equiv equiv-id

  is-emb-id : is-emb (id {A = A})
  is-emb-id = is-emb-map-emb emb-id

-- Section 11.3 Identity systems

module _
  {l1 l2 : Level} (l : Level) {A : UU l1} (B : A → UU l2) (a : A) (b : B a)
  where

  IND-identity-system : UU (l1 ⊔ l2 ⊔ lsuc l)
  IND-identity-system =
    ( P : (x : A) (y : B x) → UU l) →
      sec (λ (h : (x : A) (y : B x) → P x y) → h a b)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  fam-Σ : ((x : A) → B x → UU l3) → Σ A B → UU l3
  fam-Σ C (pair x y) = C x y

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A) (b : B a)
  where

  abstract
    Ind-identity-system :
      (is-contr-AB : is-contr (Σ A B)) →
      {l : Level} → IND-identity-system l B a b
    pr1 (Ind-identity-system is-contr-AB P) p x y =
      tr ( fam-Σ P)
         ( eq-is-contr is-contr-AB)
         ( p)
    pr2 (Ind-identity-system is-contr-AB P) p =
      ap ( λ t → tr (fam-Σ P) t p)
         ( eq-is-contr'
           ( is-prop-is-contr is-contr-AB (pair a b) (pair a b))
           ( eq-is-contr is-contr-AB)
           ( refl))

  abstract
    is-contr-total-space-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) → is-contr (Σ A B)
    pr1 (pr1 (is-contr-total-space-IND-identity-system ind)) = a
    pr2 (pr1 (is-contr-total-space-IND-identity-system ind)) = b
    pr2 (is-contr-total-space-IND-identity-system ind) (pair x y) =
      pr1 (ind (λ x' y' → Id (pair a b) (pair x' y'))) refl x y

  abstract
    fundamental-theorem-id-IND-identity-system :
      ({l : Level} → IND-identity-system l B a b) →
      (f : (x : A) → Id a x → B x) → (x : A) → is-equiv (f x)
    fundamental-theorem-id-IND-identity-system ind f =
      fundamental-theorem-id a b
        ( is-contr-total-space-IND-identity-system ind)
        ( f)

--------------------------------------------------------------------------------

-- Section 11.4 Disjointness of coproducts

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  -- The identity types of coproducts
  
  abstract
    is-contr-total-Eq-coprod-inl :
      (x : A) → is-contr (Σ (coprod A B) (Eq-coprod A B (inl x)))
    is-contr-total-Eq-coprod-inl x =
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
      (x : B) → is-contr (Σ (coprod A B) (Eq-coprod A B (inr x)))
    is-contr-total-Eq-coprod-inr x =
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
      (x : A) → is-fiberwise-equiv (Eq-eq-coprod A B (inl x))
    is-equiv-Eq-eq-coprod-inl x =
      fundamental-theorem-id
        ( inl x)
        ( reflexive-Eq-coprod A B (inl x))
        ( is-contr-total-Eq-coprod-inl x)
        ( Eq-eq-coprod A B (inl x))

  abstract
    is-equiv-Eq-eq-coprod-inr :
      (x : B) → is-fiberwise-equiv (Eq-eq-coprod A B (inr x))
    is-equiv-Eq-eq-coprod-inr x =
      fundamental-theorem-id
        ( inr x)
        ( reflexive-Eq-coprod A B (inr x))
        ( is-contr-total-Eq-coprod-inr x)
        ( Eq-eq-coprod A B (inr x))

  abstract
    is-equiv-Eq-eq-coprod :
      (s : coprod A B) → is-fiberwise-equiv (Eq-eq-coprod A B s)
    is-equiv-Eq-eq-coprod (inl x) = is-equiv-Eq-eq-coprod-inl x
    is-equiv-Eq-eq-coprod (inr x) = is-equiv-Eq-eq-coprod-inr x

  equiv-Eq-eq-coprod : (x y : coprod A B) → Id x y ≃ Eq-coprod A B x y
  pr1 (equiv-Eq-eq-coprod x y) = Eq-eq-coprod A B x y
  pr2 (equiv-Eq-eq-coprod x y) = is-equiv-Eq-eq-coprod x y

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-compute-eq-coprod-inl-inl :
    (x x' : A) → Id (inl {B = B} x) (inl {B = B} x') → Id x x'
  map-compute-eq-coprod-inl-inl x x' =
    map-inv-raise ∘ Eq-eq-coprod A B (inl x) (inl x')

  abstract
    is-equiv-map-compute-eq-coprod-inl-inl :
      (x x' : A) → is-equiv (map-compute-eq-coprod-inl-inl x x')
    is-equiv-map-compute-eq-coprod-inl-inl x x' =
      is-equiv-comp
        ( map-compute-eq-coprod-inl-inl x x')
        ( map-inv-raise)
        ( Eq-eq-coprod A B (inl x) (inl x'))
        ( refl-htpy)
        ( is-equiv-Eq-eq-coprod A B (inl x) (inl x'))
        ( is-equiv-map-inv-is-equiv is-equiv-map-raise)

  compute-eq-coprod-inl-inl :
    (x x' : A) → (Id (inl {B = B} x) (inl x')) ≃ (Id x x')
  pr1 (compute-eq-coprod-inl-inl x x') = map-compute-eq-coprod-inl-inl x x'
  pr2 (compute-eq-coprod-inl-inl x x') =
    is-equiv-map-compute-eq-coprod-inl-inl x x'

  map-compute-eq-coprod-inl-inr :
    (x : A) (y' : B) → Id (inl x) (inr y') → empty
  map-compute-eq-coprod-inl-inr x y' =
    map-inv-raise ∘ Eq-eq-coprod A B (inl x) (inr y')

  abstract
    is-equiv-map-compute-eq-coprod-inl-inr :
      (x : A) (y' : B) → is-equiv (map-compute-eq-coprod-inl-inr x y')
    is-equiv-map-compute-eq-coprod-inl-inr x y' =
      is-equiv-comp
        ( map-compute-eq-coprod-inl-inr x y')
        ( map-inv-raise)
        ( Eq-eq-coprod A B (inl x) (inr y'))
        ( refl-htpy)
        ( is-equiv-Eq-eq-coprod A B (inl x) (inr y'))
        ( is-equiv-map-inv-is-equiv is-equiv-map-raise)
  
  compute-eq-coprod-inl-inr :
    (x : A) (y' : B) → (Id (inl x) (inr y')) ≃ empty
  pr1 (compute-eq-coprod-inl-inr x y') = map-compute-eq-coprod-inl-inr x y'
  pr2 (compute-eq-coprod-inl-inr x y') =
    is-equiv-map-compute-eq-coprod-inl-inr x y'

  map-compute-eq-coprod-inr-inl :
    (y : B) (x' : A) → (Id (inr {A = A} y) (inl x')) → empty
  map-compute-eq-coprod-inr-inl y x' =
    map-inv-raise ∘ Eq-eq-coprod A B (inr y) (inl x')

  abstract
    is-equiv-map-compute-eq-coprod-inr-inl :
      (y : B) (x' : A) → is-equiv (map-compute-eq-coprod-inr-inl y x')
    is-equiv-map-compute-eq-coprod-inr-inl y x' =
      is-equiv-comp
        ( map-compute-eq-coprod-inr-inl y x')
        ( map-inv-raise)
        ( Eq-eq-coprod A B (inr y) (inl x'))
        ( refl-htpy)
        ( is-equiv-Eq-eq-coprod A B (inr y) (inl x'))
        ( is-equiv-map-inv-is-equiv is-equiv-map-raise)

  compute-eq-coprod-inr-inl :
    (y : B) (x' : A) → (Id (inr y) (inl x')) ≃ empty
  pr1 (compute-eq-coprod-inr-inl y x') = map-compute-eq-coprod-inr-inl y x'
  pr2 (compute-eq-coprod-inr-inl y x') =
    is-equiv-map-compute-eq-coprod-inr-inl y x'

  map-compute-eq-coprod-inr-inr :
    (y y' : B) → (Id (inr {A = A} y) (inr y')) → Id y y'
  map-compute-eq-coprod-inr-inr y y' =
    map-inv-raise ∘ Eq-eq-coprod A B (inr y) (inr y')

  abstract
    is-equiv-map-compute-eq-coprod-inr-inr :
      (y y' : B) → is-equiv (map-compute-eq-coprod-inr-inr y y')
    is-equiv-map-compute-eq-coprod-inr-inr y y' =
      is-equiv-comp
        ( map-compute-eq-coprod-inr-inr y y')
        ( map-inv-raise)
        ( Eq-eq-coprod A B (inr y) (inr y'))
        ( refl-htpy)
        ( is-equiv-Eq-eq-coprod A B (inr y) (inr y'))
        ( is-equiv-map-inv-is-equiv is-equiv-map-raise)

  compute-eq-coprod-inr-inr :
    (y y' : B) → (Id (inr {A = A} y) (inr y')) ≃ (Id y y')
  pr1 (compute-eq-coprod-inr-inr y y') = map-compute-eq-coprod-inr-inr y y'
  pr2 (compute-eq-coprod-inr-inr y y') =
    is-equiv-map-compute-eq-coprod-inr-inr y y'

--------------------------------------------------------------------------------

-- Section 11.6 The structure identity principle

-- Theorem 11.6.2

module _
  { l1 l2 l3 l4 : Level} { A : UU l1} {B : A → UU l2} {C : A → UU l3}
  ( D : (x : A) → B x → C x → UU l4)
  where
    
  map-swap-total-Eq-structure :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) →
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 (pr1 (map-swap-total-Eq-structure (pair (pair a b) (pair c d)))) = a
  pr2 (pr1 (map-swap-total-Eq-structure (pair (pair a b) (pair c d)))) = c
  pr1 (pr2 (map-swap-total-Eq-structure (pair (pair a b) (pair c d)))) = b
  pr2 (pr2 (map-swap-total-Eq-structure (pair (pair a b) (pair c d)))) = d

  map-inv-swap-total-Eq-structure :
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t)))
  pr1 (pr1 (map-inv-swap-total-Eq-structure (pair (pair a c) (pair b d)))) = a
  pr2 (pr1 (map-inv-swap-total-Eq-structure (pair (pair a c) (pair b d)))) = b
  pr1 (pr2 (map-inv-swap-total-Eq-structure (pair (pair a c) (pair b d)))) = c
  pr2 (pr2 (map-inv-swap-total-Eq-structure (pair (pair a c) (pair b d)))) = d
  
  issec-map-inv-swap-total-Eq-structure :
    ( map-swap-total-Eq-structure ∘ map-inv-swap-total-Eq-structure) ~ id
  issec-map-inv-swap-total-Eq-structure (pair (pair a c) (pair b d)) = refl

  isretr-map-inv-swap-total-Eq-structure :
    ( map-inv-swap-total-Eq-structure ∘ map-swap-total-Eq-structure) ~ id
  isretr-map-inv-swap-total-Eq-structure (pair (pair a b) (pair c d)) = refl

  abstract
    is-equiv-map-swap-total-Eq-structure : is-equiv map-swap-total-Eq-structure
    is-equiv-map-swap-total-Eq-structure =
      is-equiv-has-inverse
        map-inv-swap-total-Eq-structure
        issec-map-inv-swap-total-Eq-structure
        isretr-map-inv-swap-total-Eq-structure

  swap-total-Eq-structure :
    Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))) ≃
    Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t)))
  pr1 swap-total-Eq-structure = map-swap-total-Eq-structure
  pr2 swap-total-Eq-structure = is-equiv-map-swap-total-Eq-structure
  
  abstract
    is-contr-total-Eq-structure :
      (is-contr-AC : is-contr (Σ A C)) (t : Σ A C) →
      is-contr (Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))) →
      is-contr (Σ (Σ A B) (λ t → Σ (C (pr1 t)) (D (pr1 t) (pr2 t))))
    is-contr-total-Eq-structure is-contr-AC t is-contr-BD =
      is-contr-equiv
        ( Σ (Σ A C) (λ t → Σ (B (pr1 t)) (λ y → D (pr1 t) y (pr2 t))))
        ( swap-total-Eq-structure)
        ( is-contr-Σ is-contr-AC t is-contr-BD)

-- Example 11.6.3

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  -- Characterizing the identity type of a fiber as the fiber of the action on
  -- paths

  fib-ap-eq-fib-fiberwise :
    (s t : fib f b) (p : Id (pr1 s) (pr1 t)) →
    (Id (tr (λ (a : A) → Id (f a) b) p (pr2 s)) (pr2 t)) →
    (Id (ap f p) ((pr2 s) ∙ (inv (pr2 t))))
  fib-ap-eq-fib-fiberwise (pair .x' p) (pair x' refl) refl =
    inv ∘ (concat right-unit refl)

  abstract
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise :
      (s t : fib f b) → is-fiberwise-equiv (fib-ap-eq-fib-fiberwise s t)
    is-fiberwise-equiv-fib-ap-eq-fib-fiberwise (pair x y) (pair .x refl) refl =
      is-equiv-comp
        ( fib-ap-eq-fib-fiberwise (pair x y) (pair x refl) refl)
        ( inv)
        ( concat right-unit refl)
        ( refl-htpy)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fib-ap-eq-fib :
    (s t : fib f b) → Id s t →
    fib (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (fib-ap-eq-fib s .s refl) = refl
  pr2 (fib-ap-eq-fib s .s refl) = inv (right-inv (pr2 s))

  triangle-fib-ap-eq-fib :
    (s t : fib f b) →
    ( fib-ap-eq-fib s t) ~
    ( (tot (fib-ap-eq-fib-fiberwise s t)) ∘ (pair-eq-Σ {s = s} {t}))
  triangle-fib-ap-eq-fib (pair x refl) .(pair x refl) refl = refl

  abstract
    is-equiv-fib-ap-eq-fib : (s t : fib f b) → is-equiv (fib-ap-eq-fib s t)
    is-equiv-fib-ap-eq-fib s t =
      is-equiv-comp
        ( fib-ap-eq-fib s t)
        ( tot (fib-ap-eq-fib-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fib-ap-eq-fib s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fib-ap-eq-fib-fiberwise s t))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x y : A)
  where
  
  eq-fib-fib-ap :
    (q : Id (f x) (f y)) → Id (pair x q) (pair y refl) → fib (ap f {x} {y}) q
  eq-fib-fib-ap q =
    (tr (fib (ap f)) right-unit) ∘ (fib-ap-eq-fib f (pair x q) (pair y refl))

  abstract
    is-equiv-eq-fib-fib-ap :
      (q : Id (f x) (f y)) → is-equiv (eq-fib-fib-ap q)
    is-equiv-eq-fib-fib-ap q =
      is-equiv-comp
        ( eq-fib-fib-ap q)
        ( tr (fib (ap f)) right-unit)
        ( fib-ap-eq-fib f (pair x q) (pair y refl))
        ( refl-htpy)
        ( is-equiv-fib-ap-eq-fib f (pair x q) (pair y refl))
        ( is-equiv-tr (fib (ap f)) right-unit)

{-
-- Comparing fib and fib'

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (y : B)
  where

  fib'-fib : fib f y → fib' f y
  fib'-fib = tot (λ x → inv)

  abstract
    is-equiv-fib'-fib : is-equiv fib'-fib
    is-equiv-fib'-fib =
      is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-inv (f x) y)
-}

--------------------------------------------------------------------------------

-- Exercises

-- Exercise 11.1

abstract
  is-emb-ex-falso :
    {l : Level} (A : UU l) → is-emb (ex-falso {A = A})
  is-emb-ex-falso A ()

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where
  
  abstract
    is-emb-inl : is-emb (inl {A = A} {B = B})
    is-emb-inl x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ A (Id x))
          ( equiv-tot (compute-eq-coprod-inl-inl x))
          ( is-contr-total-path x))
        ( λ y → ap inl)

  emb-inl : A ↪ coprod A B
  pr1 emb-inl = inl
  pr2 emb-inl = is-emb-inl

  abstract
    is-emb-inr : is-emb (inr {A = A} {B = B})
    is-emb-inr x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( Σ B (Id x))
          ( equiv-tot (compute-eq-coprod-inr-inr x))
          ( is-contr-total-path x))
        ( λ y → ap inr)

  emb-inr : B ↪ coprod A B
  pr1 emb-inr = inr
  pr2 emb-inr = is-emb-inr

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-empty-right-summand-is-equiv : is-equiv (inl {A = A} {B = B}) → is-empty B
  is-empty-right-summand-is-equiv H b =
    map-inv-raise
      ( Eq-eq-coprod A B
        ( inl (pr1 (center (is-contr-map-is-equiv H (inr b)))))
        ( inr b)
        ( pr2 (center (is-contr-map-is-equiv H (inr b)))))

  is-empty-left-summand-is-equiv : is-equiv (inr {A = A} {B = B}) → is-empty A
  is-empty-left-summand-is-equiv H a =
    map-inv-raise
      ( Eq-eq-coprod A B
        ( inr (pr1 (center (is-contr-map-is-equiv H (inl a)))))
        ( inl a)
        ( pr2 (center (is-contr-map-is-equiv H (inl a)))))

-- Exercise 11.2

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  eq-transpose-equiv :
    (x : A) (y : B) → (Id (map-equiv e x) y) ≃ (Id x (map-inv-equiv e y))
  eq-transpose-equiv x y =
    ( inv-equiv (equiv-ap e x (map-inv-equiv e y))) ∘e
    ( equiv-concat'
      ( map-equiv e x)
      ( inv (issec-map-inv-equiv e y)))

  map-eq-transpose-equiv :
    {x : A} {y : B} → Id (map-equiv e x) y → Id x (map-inv-equiv e y)
  map-eq-transpose-equiv {x} {y} = map-equiv (eq-transpose-equiv x y)

  inv-map-eq-transpose-equiv :
    {x : A} {y : B} → Id x (map-inv-equiv e y) → Id (map-equiv e x) y
  inv-map-eq-transpose-equiv {x} {y} = map-inv-equiv (eq-transpose-equiv x y)

  triangle-eq-transpose-equiv :
    {x : A} {y : B} (p : Id (map-equiv e x) y) →
    Id ( ( ap (map-equiv e) (map-eq-transpose-equiv p)) ∙
         ( issec-map-inv-equiv e y))
       ( p)
  triangle-eq-transpose-equiv {x} {y} p =
    ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
         ( issec-map-inv-equiv
           ( equiv-ap e x (map-inv-equiv e y))
           ( p ∙ inv (issec-map-inv-equiv e y)))) ∙
    ( ( assoc p (inv (issec-map-inv-equiv e y)) (issec-map-inv-equiv e y)) ∙
      ( ( ap (concat p y) (left-inv (issec-map-inv-equiv e y))) ∙ right-unit))
  
  map-eq-transpose-equiv' :
    {a : A} {b : B} → Id b (map-equiv e a) → Id (map-inv-equiv e b) a
  map-eq-transpose-equiv' p = inv (map-eq-transpose-equiv (inv p))

  inv-map-eq-transpose-equiv' :
    {a : A} {b : B} → Id (map-inv-equiv e b) a → Id b (map-equiv e a)
  inv-map-eq-transpose-equiv' p =
    inv (inv-map-eq-transpose-equiv (inv p))

  triangle-eq-transpose-equiv' :
    {x : A} {y : B} (p : Id y (map-equiv e x)) →
    Id ( (issec-map-inv-equiv e y) ∙ p)
      ( ap (map-equiv e) (map-eq-transpose-equiv' p))
  triangle-eq-transpose-equiv' {x} {y} p =
    map-inv-equiv
      ( equiv-ap
        ( equiv-inv (map-equiv e (map-inv-equiv e y)) (map-equiv e x))
        ( (issec-map-inv-equiv e y) ∙ p)
        ( ap (map-equiv e) (map-eq-transpose-equiv' p)))
      ( ( distributive-inv-concat (issec-map-inv-equiv e y) p) ∙
        ( ( inv
            ( con-inv
              ( ap (map-equiv e) (inv (map-eq-transpose-equiv' p)))
              ( issec-map-inv-equiv e y)
              ( inv p)
              ( ( ap ( concat' (map-equiv e x) (issec-map-inv-equiv e y))
                     ( ap ( ap (map-equiv e))
                          ( inv-inv
                            ( map-inv-equiv
                              ( equiv-ap e x (map-inv-equiv e y))
                              ( ( inv p) ∙
                                ( inv (issec-map-inv-equiv e y))))))) ∙
                ( triangle-eq-transpose-equiv (inv p))))) ∙
          ( ap-inv (map-equiv e) (map-eq-transpose-equiv' p))))

-- Exercise 11.3

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where

  abstract
    is-emb-htpy : is-emb g → is-emb f
    is-emb-htpy is-emb-g x y =
      is-equiv-top-is-equiv-left-square
        ( ap g)
        ( concat' (f x) (H y))
        ( ap f)
        ( concat (H x) (g y))
        ( htpy-nat H)
        ( is-equiv-concat (H x) (g y))
        ( is-emb-g x y)
        ( is-equiv-concat' (f x) (H y))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f g : A → B) (H : f ~ g)
  where
  
  abstract
    is-emb-htpy' : is-emb f → is-emb g
    is-emb-htpy' is-emb-f =
      is-emb-htpy g f (inv-htpy H) is-emb-f

-- Exercise 11.4

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-comp :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
      is-emb h → is-emb f
    is-emb-comp f g h H is-emb-g is-emb-h =
      is-emb-htpy f (g ∘ h) H
        ( λ x y → is-equiv-comp (ap (g ∘ h)) (ap g) (ap h) (ap-comp g h)
          ( is-emb-h x y)
          ( is-emb-g (h x) (h y)))

  abstract
    is-emb-comp' :
      (g : B → C) (h : A → B) → is-emb g → is-emb h → is-emb (g ∘ h)
    is-emb-comp' g h = is-emb-comp (g ∘ h) g h refl-htpy

    comp-emb :
      (B ↪ C) → (A ↪ B) → (A ↪ C)
    pr1 (comp-emb (pair g H) (pair f K)) = g ∘ f
    pr2 (comp-emb (pair g H) (pair f K)) = is-emb-comp' g f H K

  abstract
    is-emb-right-factor :
      (f : A → C) (g : B → C) (h : A → B) (H : f ~ (g ∘ h)) → is-emb g →
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
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
      is-equiv e → is-emb g → is-emb f
    is-emb-triangle-is-equiv f g e H is-equiv-e is-emb-g =
      is-emb-comp f g e H is-emb-g (is-emb-is-equiv is-equiv-e)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  abstract
    is-emb-triangle-is-equiv' :
      (f : A → C) (g : B → C) (e : A → B) (H : f ~ (g ∘ e)) →
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

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {f : A → C} {g : B → C}
  where

  is-emb-coprod :
    is-emb f → is-emb g → ((a : A) (b : B) → ¬ (Id (f a) (g b))) →
    is-emb (ind-coprod (λ x → C) f g)
  is-emb-coprod H K L (inl a) (inl a') =
    is-equiv-left-factor
      ( ap f)
      ( ap (ind-coprod (λ x → C) f g))
      ( ap inl)
      ( λ p → ap-comp (ind-coprod (λ x → C) f g) inl p)
      ( H a a')
      ( is-emb-inl A B a a')
  is-emb-coprod H K L (inl a) (inr b') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a b')
  is-emb-coprod H K L (inr b) (inl a') =
    is-equiv-is-empty (ap (ind-coprod (λ x → C) f g)) (L a' b ∘ inv)
  is-emb-coprod H K L (inr b) (inr b') =
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

module _
  {i j : Level} {A : UU i} {B : A → UU j} (a : A)
  where

  abstract
    fundamental-theorem-id-retr :
      (i : (x : A) → B x → Id a x) → (R : (x : A) → retr (i x)) →
      is-fiberwise-equiv i
    fundamental-theorem-id-retr i R =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-is-contr (tot i)
          ( is-contr-retract-of (Σ _ (λ y → Id a y))
            ( pair (tot i)
              ( pair (tot λ x → pr1 (R x))
                ( ( inv-htpy (tot-comp i (λ x → pr1 (R x)))) ∙h
                  ( ( tot-htpy λ x → pr2 (R x)) ∙h (tot-id B)))))
            ( is-contr-total-path a))
          ( is-contr-total-path a))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-sec-is-equiv : (sec-f : sec f) → is-equiv (pr1 sec-f) → is-equiv f
    is-equiv-sec-is-equiv (pair g issec-g) is-equiv-sec-f =
      is-equiv-htpy h
        ( ( htpy-left-whisk f
            ( inv-htpy (issec-map-inv-is-equiv is-equiv-sec-f))) ∙h
          ( htpy-right-whisk issec-g h))
        ( is-equiv-map-inv-is-equiv is-equiv-sec-f)
      where
      h : A → B
      h = map-inv-is-equiv is-equiv-sec-f

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (a : A)
  where

  abstract
    fundamental-theorem-id-sec :
      (f : (x : A) → Id a x → B x) → ((x : A) → sec (f x)) →
      is-fiberwise-equiv f
    fundamental-theorem-id-sec f sec-f x =
      is-equiv-sec-is-equiv (f x) (sec-f x) (is-fiberwise-equiv-i x)
      where
        i : (x : A) → B x → Id a x
        i = λ x → pr1 (sec-f x)
        retr-i : (x : A) → retr (i x)
        pr1 (retr-i x) = f x
        pr2 (retr-i x) = pr2 (sec-f x)
        is-fiberwise-equiv-i : is-fiberwise-equiv i
        is-fiberwise-equiv-i = fundamental-theorem-id-retr a i retr-i

-- Exercise 11.10

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where
  
  abstract
    is-emb-sec-ap :
      ((x y : A) → sec (ap f {x = x} {y = y})) → is-emb f
    is-emb-sec-ap sec-ap-f x y =
      fundamental-theorem-id-sec x (λ y → ap f {y = y}) (sec-ap-f x) y

-- Exercise 11.11

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-path-split : UU (l1 ⊔ l2)
  is-path-split = sec f × ((x y : A) → sec (ap f {x = x} {y = y}))

  abstract
    is-path-split-is-equiv : is-equiv f → is-path-split
    pr1 (is-path-split-is-equiv is-equiv-f) = pr1 is-equiv-f
    pr2 (is-path-split-is-equiv is-equiv-f) x y =
      pr1 (is-emb-is-equiv is-equiv-f x y)

  abstract
    is-coherently-invertible-is-path-split :
      is-path-split → is-coherently-invertible f
    pr1
      ( is-coherently-invertible-is-path-split
        ( pair (pair g issec-g) sec-ap-f)) = g
    pr1
      ( pr2
        ( is-coherently-invertible-is-path-split
          ( pair (pair g issec-g) sec-ap-f))) = issec-g
    pr1
      ( pr2
        ( pr2
          ( is-coherently-invertible-is-path-split
            ( pair (pair g issec-g) sec-ap-f)))) x =
      pr1 (sec-ap-f (g (f x)) x) (issec-g (f x))
    pr2
      ( pr2
        ( pr2
          ( is-coherently-invertible-is-path-split
            ( pair (pair g issec-g) sec-ap-f)))) x =
      inv (pr2 (sec-ap-f (g (f x)) x) (issec-g (f x)))
         
  abstract
    is-equiv-is-coherently-invertible :
      is-coherently-invertible f → is-equiv f
    is-equiv-is-coherently-invertible (pair g (pair G (pair H K))) =
      is-equiv-has-inverse g G H

  abstract
    is-equiv-is-path-split : is-path-split → is-equiv f
    is-equiv-is-path-split =
      is-equiv-is-coherently-invertible ∘ is-coherently-invertible-is-path-split

  abstract
    is-coherently-invertible-is-equiv :
      is-equiv f → is-coherently-invertible f
    is-coherently-invertible-is-equiv =
      is-coherently-invertible-is-path-split ∘ is-path-split-is-equiv

-- Exercise 11.12

module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where
  
  fib-triangle :
    (x : X) → (fib f x) → (fib g x)
  pr1 (fib-triangle .(f a) (pair a refl)) = h a
  pr2 (fib-triangle .(f a) (pair a refl)) = inv (H a)

  square-tot-fib-triangle :
    (h ∘ (map-equiv-total-fib f)) ~ (map-equiv-total-fib g ∘ tot fib-triangle)
  square-tot-fib-triangle (pair .(f a) (pair a refl)) = refl

  abstract
    is-fiberwise-equiv-is-equiv-triangle :
      (E : is-equiv h) → is-fiberwise-equiv fib-triangle
    is-fiberwise-equiv-is-equiv-triangle E =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fib f)
          ( map-equiv-total-fib g)
          ( tot fib-triangle)
          ( h)
          ( square-tot-fib-triangle)
          ( is-equiv-map-equiv-total-fib f)
          ( is-equiv-map-equiv-total-fib g)
          ( E))

  abstract
    is-equiv-triangle-is-fiberwise-equiv :
      is-fiberwise-equiv fib-triangle → is-equiv h
    is-equiv-triangle-is-fiberwise-equiv E =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fib f)
        ( map-equiv-total-fib g)
        ( tot fib-triangle)
        ( h)
        ( square-tot-fib-triangle)
        ( is-equiv-map-equiv-total-fib f)
        ( is-equiv-map-equiv-total-fib g)
        ( is-equiv-tot-is-fiberwise-equiv E)

{-
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (g : B → X) (h : A → B)
  where

  fib-triangle' : (x : X) → (fib (g ∘ h) x) → fib g x
  fib-triangle' x = fib-triangle (g ∘ h) g h refl-htpy x
-}
