{-# OPTIONS --without-K --exact-split #-}

module foundations.pointed-maps where

open import foundations.24-pushouts public

-- The universe of pointed types

UU-pt : (l : Level) → UU (lsuc l)
UU-pt l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : UU-pt l)
  where
  
  type-UU-pt : UU l
  type-UU-pt = pr1 A
  
  pt-UU-pt : type-UU-pt
  pt-UU-pt = pr2 A

-- Pointed families

pointed-fam :
  {l1 : Level} (l : Level) (A : UU-pt l1) → UU (lsuc l ⊔ l1)
pointed-fam l A = Σ (type-UU-pt A → UU l) (λ P → P (pt-UU-pt A))

module _
  {l1 l2 : Level} (A : UU-pt l1) (B : pointed-fam l2 A)
  where
  
  fam-pointed-fam : type-UU-pt A → UU l2
  fam-pointed-fam = pr1 B

  pt-pointed-fam : fam-pointed-fam (pt-UU-pt A)
  pt-pointed-fam = pr2 B

  -- Pointed Π-types

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    Σ ( (x : type-UU-pt A) → fam-pointed-fam x)
      ( λ f → Id (f (pt-UU-pt A)) pt-pointed-fam)

  function-pointed-Π : pointed-Π → (x : type-UU-pt A) → fam-pointed-fam x
  function-pointed-Π f = pr1 f

  preserves-point-function-pointed-Π :
    (f : pointed-Π) → Id (function-pointed-Π f (pt-UU-pt A)) pt-pointed-fam
  preserves-point-function-pointed-Π f = pr2 f

module _
  {l1 l2 : Level} (A : UU-pt l1) (B : pointed-fam l2 A) (f : pointed-Π A B)
  where

  -- Pointed homotopies

  pointed-htpy : (g : pointed-Π A B) → UU (l1 ⊔ l2)
  pointed-htpy g =
    pointed-Π A
      ( pair
        ( λ x →
          Id ( function-pointed-Π A B f x)
             ( function-pointed-Π A B g x))
        ( ( preserves-point-function-pointed-Π A B f) ∙
          ( inv (preserves-point-function-pointed-Π A B g))))

  refl-pointed-htpy : pointed-htpy f
  refl-pointed-htpy =
    pair refl-htpy (inv (right-inv (preserves-point-function-pointed-Π A B f)))

  pointed-htpy-eq :
    (g : pointed-Π A B) → Id f g → pointed-htpy g
  pointed-htpy-eq .f refl = refl-pointed-htpy

  is-contr-total-pointed-htpy : is-contr (Σ (pointed-Π A B) pointed-htpy)
  is-contr-total-pointed-htpy =
    is-contr-total-Eq-structure
      ( λ g β (H : function-pointed-Π A B f ~ g) →
          Id ( H (pt-UU-pt A))
             ( (preserves-point-function-pointed-Π A B f) ∙ (inv β)))
      ( is-contr-total-htpy (function-pointed-Π A B f))
      ( pair (function-pointed-Π A B f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( Id (function-pointed-Π A B f (pt-UU-pt A)) (pt-pointed-fam A B))
            ( λ β → Id β (preserves-point-function-pointed-Π A B f)))
        ( equiv-tot
          ( λ β →
            equiv-con-inv refl β (preserves-point-function-pointed-Π A B f)))
        ( is-contr-total-path' (preserves-point-function-pointed-Π A B f)))

  is-equiv-pointed-htpy-eq :
    (g : pointed-Π A B) → is-equiv (pointed-htpy-eq g)
  is-equiv-pointed-htpy-eq =
    fundamental-theorem-id f
      ( refl-pointed-htpy)
      ( is-contr-total-pointed-htpy)
      ( pointed-htpy-eq)

  eq-pointed-htpy :
    (g : pointed-Π A B) → (pointed-htpy g) → Id f g
  eq-pointed-htpy g = map-inv-is-equiv (is-equiv-pointed-htpy-eq g)

-- Pointed maps

module _
  {l1 l2 : Level}
  where
  
  _→*_ : UU-pt l1 → UU-pt l2 → UU (l1 ⊔ l2)
  A →* B = pointed-Π A (pair (λ x → type-UU-pt B) (pt-UU-pt B))

  [_→*_] : UU-pt l1 → UU-pt l2 → UU-pt (l1 ⊔ l2)
  [ A →* B ] =
    pair
      ( A →* B)
      ( pair
        ( const (type-UU-pt A) (type-UU-pt B) (pt-UU-pt B))
        ( refl))

module _
  {l1 l2 : Level} (A : UU-pt l1) (B : UU-pt l2)
  where
  
  map-pointed-map : A →* B → type-UU-pt A → type-UU-pt B
  map-pointed-map f = pr1 f

  preserves-point-map-pointed-map :
    (f : A →* B) → Id (map-pointed-map f (pt-UU-pt A)) (pt-UU-pt B)
  preserves-point-map-pointed-map f = pr2 f

-- Loop spaces

module _
  {l : Level} (A : UU-pt l)
  where
  
  type-Ω : UU l
  type-Ω = Id (pt-UU-pt A) (pt-UU-pt A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : UU-pt l
  Ω = pair type-Ω refl-Ω

-- Iterated loop spaces

module _
  {l : Level}
  where

  iterated-loop-space : ℕ → UU-pt l → UU-pt l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
  
  Ω² : UU-pt l → UU-pt l
  Ω² A = iterated-loop-space two-ℕ A
  
  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = Id (refl {x = a}) (refl {x = a})
  
  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl
  
  Ω³ : UU-pt l → UU-pt l
  Ω³ A = iterated-loop-space three-ℕ A
  
  type-Ω³ : {A : UU l} (a : A) → UU l
  type-Ω³ a = Id (refl-Ω² {a = a}) (refl-Ω² {a = a})
  
  refl-Ω³ : {A : UU l} {a : A} → type-Ω³ a
  refl-Ω³ = refl

-- Pointed equivalences

_≃*_ : {l1 l2 : Level} (A : UU-pt l1) (B : UU-pt l2) → UU (l1 ⊔ l2)
A ≃* B =
  Σ ( type-UU-pt A ≃ type-UU-pt B)
    ( λ e → Id (map-equiv e (pt-UU-pt A)) (pt-UU-pt B))

module _
  {l1 l2 : Level} (A : UU-pt l1) (B : UU-pt l2) (e : A ≃* B)
  where

  equiv-pointed-equiv : type-UU-pt A ≃ type-UU-pt B
  equiv-pointed-equiv = pr1 e

  map-equiv-pointed-equiv : type-UU-pt A → type-UU-pt B
  map-equiv-pointed-equiv = map-equiv equiv-pointed-equiv

  preserves-point-equiv-pointed-equiv :
    Id (map-equiv-pointed-equiv (pt-UU-pt A)) (pt-UU-pt B)
  preserves-point-equiv-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →* B
  pointed-map-pointed-equiv =
    pair map-equiv-pointed-equiv preserves-point-equiv-pointed-equiv

-- We characterize the identity type of the universe of pointed types

module _
  {l1 : Level} (A : UU-pt l1)
  where
  
  id-pointed-equiv : A ≃* A
  id-pointed-equiv = pair equiv-id refl

  pointed-equiv-eq : (B : UU-pt l1) → Id A B → A ≃* B
  pointed-equiv-eq .A refl = id-pointed-equiv

  is-contr-total-pointed-equiv : is-contr (Σ (UU-pt l1) (λ B → A ≃* B))
  is-contr-total-pointed-equiv =
    is-contr-total-Eq-structure
      ( λ X x (e : type-UU-pt A ≃ X) → Id (map-equiv e (pt-UU-pt A)) x)
      ( is-contr-total-equiv (type-UU-pt A))
      ( pair (type-UU-pt A) equiv-id)
      ( is-contr-total-path (pt-UU-pt A))

  is-equiv-pointed-equiv-eq :
    (B : UU-pt l1) → is-equiv (pointed-equiv-eq B)
  is-equiv-pointed-equiv-eq =
    fundamental-theorem-id A
      ( id-pointed-equiv)
      ( is-contr-total-pointed-equiv)
      ( pointed-equiv-eq)

  equiv-pointed-equiv-eq :
    (B : UU-pt l1) → Id A B ≃ (A ≃* B)
  equiv-pointed-equiv-eq B =
    pair (pointed-equiv-eq B) (is-equiv-pointed-equiv-eq B)

  eq-pointed-equiv : (B : UU-pt l1) → A ≃* B → Id A B
  eq-pointed-equiv B =
    map-inv-is-equiv (is-equiv-pointed-equiv-eq B)

-- We compute transport of type-Ω

module _
  {l1 : Level} {A : UU l1} {x y : A} (p : Id x y)
  where

  equiv-tr-type-Ω : type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω  = equiv-concat (inv p) y ∘e equiv-concat' x p

  tr-type-Ω : type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω = map-equiv equiv-tr-type-Ω

  is-equiv-tr-type-Ω : is-equiv tr-type-Ω
  is-equiv-tr-type-Ω = is-equiv-map-equiv equiv-tr-type-Ω

  preserves-point-tr-Ω : Id (tr-type-Ω refl) refl
  preserves-point-tr-Ω = left-inv p

  equiv-tr-Ω : Ω (pair A x) ≃* Ω (pair A y)
  equiv-tr-Ω = pair equiv-tr-type-Ω preserves-point-tr-Ω

-- We show that Ω is a functor

module _
  {l1 l2 : Level} (A : UU-pt l1) (B : UU-pt l2) (f : A →* B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) p)
  
  preserves-refl-map-Ω : Id (map-Ω refl) refl
  preserves-refl-map-Ω = left-inv (preserves-point-map-pointed-map A B f)

  pointed-map-Ω : Ω A →* Ω B
  pointed-map-Ω = pair map-Ω preserves-refl-map-Ω


