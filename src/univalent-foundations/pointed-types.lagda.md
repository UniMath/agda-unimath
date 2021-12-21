---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-foundations.pointed-types where

open import univalent-foundations.17-univalence public

-- The universe of pointed types

Pointed-Type : (l : Level) → UU (lsuc l)
Pointed-Type l = Σ (UU l) (λ X → X)

module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Pointed-Type : UU l
  type-Pointed-Type = pr1 A
  
  pt-Pointed-Type : type-Pointed-Type
  pt-Pointed-Type = pr2 A

-- Pointed families

Pointed-Fam :
  {l1 : Level} (l : Level) (A : Pointed-Type l1) → UU (lsuc l ⊔ l1)
Pointed-Fam l A = Σ (type-Pointed-Type A → UU l) (λ P → P (pt-Pointed-Type A))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where
  
  fam-Pointed-Fam : type-Pointed-Type A → UU l2
  fam-Pointed-Fam = pr1 B

  pt-Pointed-Fam : fam-Pointed-Fam (pt-Pointed-Type A)
  pt-Pointed-Fam = pr2 B

  -- Pointed Π-types

  pointed-Π : UU (l1 ⊔ l2)
  pointed-Π =
    Σ ( (x : type-Pointed-Type A) → fam-Pointed-Fam x)
      ( λ f → Id (f (pt-Pointed-Type A)) pt-Pointed-Fam)

  function-pointed-Π : pointed-Π → (x : type-Pointed-Type A) → fam-Pointed-Fam x
  function-pointed-Π f = pr1 f

  preserves-point-function-pointed-Π :
    (f : pointed-Π) →
    Id (function-pointed-Π f (pt-Pointed-Type A)) pt-Pointed-Fam
  preserves-point-function-pointed-Π f = pr2 f

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  (f : pointed-Π A B)
  where

  -- Pointed homotopies

  htpy-pointed-Π : (g : pointed-Π A B) → UU (l1 ⊔ l2)
  htpy-pointed-Π g =
    pointed-Π A
      ( pair
        ( λ x →
          Id ( function-pointed-Π A B f x)
             ( function-pointed-Π A B g x))
        ( ( preserves-point-function-pointed-Π A B f) ∙
          ( inv (preserves-point-function-pointed-Π A B g))))

  refl-htpy-pointed-Π : htpy-pointed-Π f
  refl-htpy-pointed-Π =
    pair refl-htpy (inv (right-inv (preserves-point-function-pointed-Π A B f)))

  htpy-eq-pointed-Π :
    (g : pointed-Π A B) → Id f g → htpy-pointed-Π g
  htpy-eq-pointed-Π .f refl = refl-htpy-pointed-Π

  is-contr-total-htpy-pointed-Π : is-contr (Σ (pointed-Π A B) htpy-pointed-Π)
  is-contr-total-htpy-pointed-Π =
    is-contr-total-Eq-structure
      ( λ g β (H : function-pointed-Π A B f ~ g) →
          Id ( H (pt-Pointed-Type A))
             ( (preserves-point-function-pointed-Π A B f) ∙ (inv β)))
      ( is-contr-total-htpy (function-pointed-Π A B f))
      ( pair (function-pointed-Π A B f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( Id ( function-pointed-Π A B f (pt-Pointed-Type A))
                 ( pt-Pointed-Fam A B))
            ( λ β → Id β (preserves-point-function-pointed-Π A B f)))
        ( equiv-tot
          ( λ β →
            equiv-con-inv refl β (preserves-point-function-pointed-Π A B f)))
        ( is-contr-total-path' (preserves-point-function-pointed-Π A B f)))

  is-equiv-htpy-eq-pointed-Π :
    (g : pointed-Π A B) → is-equiv (htpy-eq-pointed-Π g)
  is-equiv-htpy-eq-pointed-Π =
    fundamental-theorem-id f
      ( refl-htpy-pointed-Π)
      ( is-contr-total-htpy-pointed-Π)
      ( htpy-eq-pointed-Π)

  eq-htpy-pointed-Π :
    (g : pointed-Π A B) → (htpy-pointed-Π g) → Id f g
  eq-htpy-pointed-Π g = map-inv-is-equiv (is-equiv-htpy-eq-pointed-Π g)

-- Pointed maps

module _
  {l1 l2 : Level}
  where

  constant-Pointed-Fam :
    (A : Pointed-Type l1) → Pointed-Type l2 → Pointed-Fam l2 A
  constant-Pointed-Fam A B =
    pair (λ x → type-Pointed-Type B) (pt-Pointed-Type B)
  
  _→*_ : Pointed-Type l1 → Pointed-Type l2 → UU (l1 ⊔ l2)
  A →* B = pointed-Π A (constant-Pointed-Fam A B)

  [_→*_] : Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
  [ A →* B ] =
    pair
      ( A →* B)
      ( pair
        ( const (type-Pointed-Type A) (type-Pointed-Type B) (pt-Pointed-Type B))
        ( refl))

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where
  
  map-pointed-map : A →* B → type-Pointed-Type A → type-Pointed-Type B
  map-pointed-map f = pr1 f

  preserves-point-map-pointed-map :
    (f : A →* B) →
    Id (map-pointed-map f (pt-Pointed-Type A)) (pt-Pointed-Type B)
  preserves-point-map-pointed-map f = pr2 f

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Fam l3 B) (f : A →* B)
  where

  precomp-Pointed-Fam : Pointed-Fam l3 A
  precomp-Pointed-Fam =
    pair
      ( fam-Pointed-Fam B C ∘ map-pointed-map A B f)
      ( tr
        ( fam-Pointed-Fam B C)
        ( inv (preserves-point-map-pointed-map A B f))
        ( pt-Pointed-Fam B C))

  precomp-pointed-Π : pointed-Π B C → pointed-Π A precomp-Pointed-Fam
  precomp-pointed-Π g =
    pair
      ( λ x → function-pointed-Π B C g (map-pointed-map A B f x))
      ( ( inv
          ( apd
            ( function-pointed-Π B C g)
            ( inv (preserves-point-map-pointed-map A B f)))) ∙
        ( ap
          ( tr
            ( fam-Pointed-Fam B C)
            ( inv (preserves-point-map-pointed-map A B f)))
          ( preserves-point-function-pointed-Π B C g)))

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Type l3)
  where

  precomp-pointed-map : A →* B → B →* C → A →* C
  precomp-pointed-map f g =
    pair
      ( map-pointed-map B C g ∘ map-pointed-map A B f)
      ( ( ap (map-pointed-map B C g) (preserves-point-map-pointed-map A B f)) ∙
        ( preserves-point-map-pointed-map B C g))

  comp-pointed-map : B →* C → A →* B → A →* C
  comp-pointed-map g f = precomp-pointed-map f g

module _
  {l1 : Level} {A : Pointed-Type l1}
  where

  id-pointed-map : A →* A
  id-pointed-map = pair id refl

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  -- Pointed homotopies of pointed maps

  htpy-pointed-map : (g : A →* B) → UU (l1 ⊔ l2)
  htpy-pointed-map = htpy-pointed-Π A (constant-Pointed-Fam A B) f

  refl-htpy-pointed-map : htpy-pointed-map f
  refl-htpy-pointed-map = refl-htpy-pointed-Π A (constant-Pointed-Fam A B) f

  htpy-eq-pointed-map :
    (g : A →* B) → Id f g → htpy-pointed-map g
  htpy-eq-pointed-map = htpy-eq-pointed-Π A (constant-Pointed-Fam A B) f

  is-contr-total-htpy-pointed-map : is-contr (Σ (A →* B) htpy-pointed-map)
  is-contr-total-htpy-pointed-map =
    is-contr-total-htpy-pointed-Π A (constant-Pointed-Fam A B) f

  is-equiv-htpy-eq-pointed-map :
    (g : A →* B) → is-equiv (htpy-eq-pointed-map g)
  is-equiv-htpy-eq-pointed-map =
    is-equiv-htpy-eq-pointed-Π A (constant-Pointed-Fam A B) f

  eq-htpy-pointed-map :
    (g : A →* B) → (htpy-pointed-map g) → Id f g
  eq-htpy-pointed-map = eq-htpy-pointed-Π A (constant-Pointed-Fam A B) f

-- The category laws for pointed maps

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  left-unit-law-comp-pointed-map :
    htpy-pointed-map A B (comp-pointed-map A B B id-pointed-map f) f
  left-unit-law-comp-pointed-map =
    pair
      ( refl-htpy)
      ( ( inv (right-inv (pr2 f))) ∙
        ( ap
          ( concat' (map-pointed-map A B f (pt-Pointed-Type A)) (inv (pr2 f)))
          ( ( inv (ap-id (pr2 f))) ∙
            ( inv right-unit))))

  right-unit-law-comp-pointed-map :
    htpy-pointed-map A B (comp-pointed-map A A B f id-pointed-map) f
  right-unit-law-comp-pointed-map =
    pair
      ( refl-htpy)
      ( inv (right-inv (pr2 f)))

module _
  {l1 l2 l3 l4 : Level}
  where

  assoc-comp-pointed-map :
    (A : Pointed-Type l1) (B : Pointed-Type l2)
    (C : Pointed-Type l3) (D : Pointed-Type l4)
    (h : C →* D) (g : B →* C) (f : A →* B) →
    htpy-pointed-map A D
      ( comp-pointed-map A B D (comp-pointed-map B C D h g) f)
      ( comp-pointed-map A C D h (comp-pointed-map A B C g f))
  assoc-comp-pointed-map
    (pair A a) (pair B .(f a)) (pair C .(g (f a))) (pair D .(h (g (f a))))
    (pair h refl) (pair g refl) (pair f refl) =
    pair refl-htpy refl

  inv-assoc-comp-pointed-map :
    (A : Pointed-Type l1) (B : Pointed-Type l2)
    (C : Pointed-Type l3) (D : Pointed-Type l4)
    (h : C →* D) (g : B →* C) (f : A →* B) →
    htpy-pointed-map A D
      ( comp-pointed-map A C D h (comp-pointed-map A B C g f))
      ( comp-pointed-map A B D (comp-pointed-map B C D h g) f)
  inv-assoc-comp-pointed-map
    (pair A a) (pair B .(f a)) (pair C .(g (f a))) (pair D .(h (g (f a))))
    (pair h refl) (pair g refl) (pair f refl) =
    pair refl-htpy refl

-- Groupoid structure of homotopies of pointed maps

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Fam l2 A)
  where

  concat-htpy-pointed-Π :
    (f g h : pointed-Π A B) →
    htpy-pointed-Π A B f g → htpy-pointed-Π A B g h → htpy-pointed-Π A B f h
  concat-htpy-pointed-Π f g h G H =
    pair
      ( pr1 G ∙h pr1 H)
      ( ( ap-binary (λ p q → p ∙ q) (pr2 G) (pr2 H)) ∙
        ( ( assoc (pr2 f) (inv (pr2 g)) (pr2 g ∙ inv (pr2 h))) ∙
          ( ap
            ( concat (pr2 f) (function-pointed-Π A B h (pt-Pointed-Type A)))
            ( ( inv (assoc (inv (pr2 g)) (pr2 g) (inv (pr2 h)))) ∙
              ( ap
                ( concat' (pt-Pointed-Fam A B) (inv (pr2 h)))
                ( left-inv (pr2 g)))))))

  inv-htpy-pointed-Π :
    (f g : pointed-Π A B) → htpy-pointed-Π A B f g → htpy-pointed-Π A B g f
  inv-htpy-pointed-Π f g H =
    pair
      ( inv-htpy (pr1 H))
      ( ( ap inv (pr2 H)) ∙
        ( ( distributive-inv-concat (pr2 f) (inv (pr2 g))) ∙
          ( ap
            ( concat'
              ( function-pointed-Π A B g (pt-Pointed-Type A))
              ( inv (pr2 f)))
            ( inv-inv (pr2 g)))))

module _
  {l1 l2 l3 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  (C : Pointed-Type l3)
  where

  left-whisker-htpy-pointed-map :
    (g : B →* C) (f1 f2 : A →* B) (H : htpy-pointed-map A B f1 f2) →
    htpy-pointed-map A C
      ( comp-pointed-map A B C g f1)
      ( comp-pointed-map A B C g f2)
  left-whisker-htpy-pointed-map g f1 f2 H =
    pair
      ( map-pointed-map B C g ·l (pr1 H))
      ( ( ( ( ap (ap (pr1 g)) (pr2 H)) ∙
            ( ap-concat (pr1 g) (pr2 f1) (inv (pr2 f2)))) ∙
          ( ap
            ( concat
              ( ap (pr1 g) (pr2 f1))
              ( map-pointed-map B C g
                ( map-pointed-map A B f2 (pt-Pointed-Type A))))
            ( ( ( ( ap-inv (pr1 g) (pr2 f2)) ∙
                  ( ap
                    ( concat'
                      ( pr1 g (pt-Pointed-Fam A (constant-Pointed-Fam A B)))
                      ( inv (ap (pr1 g) (pr2 f2)))))
                  ( inv (right-inv (pr2 g)))) ∙
                ( assoc
                  ( pr2 g)
                  ( inv (pr2 g))
                  ( inv (ap (pr1 g) (pr2 f2))))) ∙
              ( ap
                ( concat
                  ( pr2 g)
                  ( map-pointed-map B C g
                    ( map-pointed-map A B f2 (pt-Pointed-Type A))))
                ( inv
                  ( distributive-inv-concat
                    ( ap (pr1 g) (pr2 f2))
                    ( pr2 g))))))) ∙
        ( inv
          ( assoc
            ( ap (pr1 g) (pr2 f1))
            ( pr2 g)
            ( inv (ap (pr1 g) (pr2 f2) ∙ pr2 g)))))

module _
  {l1 l2 l3 : Level} 
  where

  right-whisker-htpy-pointed-map :
    (A : Pointed-Type l1) (B : Pointed-Type l2) (C : Pointed-Type l3)
    (g1 g2 : B →* C) (H : htpy-pointed-map B C g1 g2) (f : A →* B) →
    htpy-pointed-map A C
      ( comp-pointed-map A B C g1 f)
      ( comp-pointed-map A B C g2 f)
  right-whisker-htpy-pointed-map (pair A a) (pair B .(f a)) (pair C c)
    g1 g2 H (pair f refl) = 
    pair (pr1 H ·r f) (pr2 H)
  
module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2)
  where

  concat-htpy-pointed-map :
    (f g h : A →* B) → htpy-pointed-map A B f g → htpy-pointed-map A B g h →
    htpy-pointed-map A B f h
  concat-htpy-pointed-map = concat-htpy-pointed-Π A (constant-Pointed-Fam A B)

-- Pointed equivalences

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  sec-pointed-map : UU (l1 ⊔ l2)
  sec-pointed-map =
    Σ ( B →* A)
      ( λ g →
        htpy-pointed-map B B
          ( comp-pointed-map B A B f g)
          ( id-pointed-map))

  retr-pointed-map : UU (l1 ⊔ l2)
  retr-pointed-map =
    Σ ( B →* A)
      ( λ g →
        htpy-pointed-map A A
          ( comp-pointed-map A B A g f)
          ( id-pointed-map))

  is-iso-pointed-map : UU (l1 ⊔ l2)
  is-iso-pointed-map = sec-pointed-map × retr-pointed-map

  is-equiv-pointed-map : UU (l1 ⊔ l2)
  is-equiv-pointed-map = is-equiv (map-pointed-map A B f)

  is-contr-sec-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr sec-pointed-map
  is-contr-sec-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (map-pointed-map A B f ∘ g) ~ id) →
          Id { A = Id { A = type-Pointed-Type B}
                      ( map-pointed-map A B f (g (pt-Pointed-Type B)))
                      ( pt-Pointed-Type B)}
             ( G (pt-Pointed-Type B))
             ( ( ( ap (map-pointed-map A B f) p) ∙
                 ( preserves-point-map-pointed-map A B f)) ∙
               ( refl)))
      ( is-contr-sec-is-equiv H)
      ( pair (map-inv-is-equiv H) (issec-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fib
          ( ap (map-pointed-map A B f))
          ( ( issec-map-inv-is-equiv H (pt-Pointed-Type B)) ∙
            ( inv (preserves-point-map-pointed-map A B f))))
        ( equiv-tot
          ( λ p →
            ( ( equiv-con-inv
                ( ap (map-pointed-map A B f) p)
                ( preserves-point-map-pointed-map A B f)
                ( issec-map-inv-is-equiv H (pt-Pointed-Type B))) ∘e
              ( equiv-inv
                ( issec-map-inv-is-equiv H (pt-Pointed-Type B))
                ( ( ap (map-pointed-map A B f) p) ∙
                  ( preserves-point-map-pointed-map A B f)))) ∘e
            ( equiv-concat'
              ( issec-map-inv-is-equiv H (pt-Pointed-Type B))
              ( right-unit))))
        ( is-contr-map-is-equiv
          ( is-emb-is-equiv H
            ( map-inv-is-equiv H (pt-Pointed-Type B))
            ( pt-Pointed-Type A))
          ( ( issec-map-inv-is-equiv H (pt-Pointed-Type B)) ∙
            ( inv (preserves-point-map-pointed-map A B f)))))

  is-contr-retr-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr retr-pointed-map
  is-contr-retr-is-equiv-pointed-map H =
    is-contr-total-Eq-structure
      ( λ g p (G : (g ∘ map-pointed-map A B f) ~ id) →
        Id {A = Id { A = type-Pointed-Type A}
                   ( g (map-pointed-map A B f (pt-Pointed-Type A)))
                   ( pt-Pointed-Type A)}
           ( G (pt-Pointed-Type A))
           ( ( ( ap g (preserves-point-map-pointed-map A B f)) ∙
               ( p)) ∙
             ( refl)))
      ( is-contr-retr-is-equiv H)
      ( pair (map-inv-is-equiv H) (isretr-map-inv-is-equiv H))
      ( is-contr-equiv
        ( fib
          ( λ p →
            ( ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f)) ∙
              ( p)) ∙
            ( refl))
          ( isretr-map-inv-is-equiv H (pt-Pointed-Type A)))
        ( equiv-tot (λ p → equiv-inv _ _))
        ( is-contr-map-is-equiv
          ( is-equiv-comp'
            ( λ q → q ∙ refl)
            ( λ p →
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f)) ∙
              ( p))
            ( is-equiv-concat
              ( ap
                ( map-inv-is-equiv H)
                ( preserves-point-map-pointed-map A B f))
              ( pt-Pointed-Type A))
            ( is-equiv-concat'
              ( map-inv-is-equiv H (map-pointed-map A B f (pt-Pointed-Type A)))
              ( refl)))
          ( isretr-map-inv-is-equiv H (pt-Pointed-Type A))))

  is-contr-is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map → is-contr is-iso-pointed-map
  is-contr-is-iso-is-equiv-pointed-map H =
    is-contr-prod
      ( is-contr-sec-is-equiv-pointed-map H)
      ( is-contr-retr-is-equiv-pointed-map H)

  is-iso-is-equiv-pointed-map :
    is-equiv-pointed-map → is-iso-pointed-map
  is-iso-is-equiv-pointed-map H =
    center (is-contr-is-iso-is-equiv-pointed-map H)

  is-equiv-is-iso-pointed-map :
    is-iso-pointed-map → is-equiv-pointed-map
  is-equiv-is-iso-pointed-map H =
    pair
      ( pair
        ( pr1 (pr1 (pr1 H)))
        ( pr1 (pr2 (pr1 H))))
      ( pair
        ( pr1 (pr1 (pr2 H)))
        ( pr1 (pr2 (pr2 H))))

  is-prop-is-iso-pointed-map : is-prop is-iso-pointed-map
  is-prop-is-iso-pointed-map =
    is-prop-is-proof-irrelevant
      ( λ H →
        is-contr-is-iso-is-equiv-pointed-map (is-equiv-is-iso-pointed-map H))

  equiv-is-iso-is-equiv-pointed-map : is-equiv-pointed-map ≃ is-iso-pointed-map
  equiv-is-iso-is-equiv-pointed-map =
    pair
      ( is-iso-is-equiv-pointed-map)
      ( is-equiv-is-prop
        ( is-subtype-is-equiv (map-pointed-map A B f))
        ( is-prop-is-iso-pointed-map)
        ( is-equiv-is-iso-pointed-map))

_≃*_ :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) → UU (l1 ⊔ l2)
A ≃* B =
  Σ ( type-Pointed-Type A ≃ type-Pointed-Type B)
    ( λ e → Id (map-equiv e (pt-Pointed-Type A)) (pt-Pointed-Type B))

compute-pointed-equiv :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A ≃* B) ≃ Σ (A →* B) (is-equiv-pointed-map A B)
compute-pointed-equiv A B = equiv-right-swap-Σ

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (e : A ≃* B)
  where

  equiv-pointed-equiv : type-Pointed-Type A ≃ type-Pointed-Type B
  equiv-pointed-equiv = pr1 e

  map-equiv-pointed-equiv : type-Pointed-Type A → type-Pointed-Type B
  map-equiv-pointed-equiv = map-equiv equiv-pointed-equiv

  preserves-point-equiv-pointed-equiv :
    Id (map-equiv-pointed-equiv (pt-Pointed-Type A)) (pt-Pointed-Type B)
  preserves-point-equiv-pointed-equiv = pr2 e

  pointed-map-pointed-equiv : A →* B
  pointed-map-pointed-equiv =
    pair map-equiv-pointed-equiv preserves-point-equiv-pointed-equiv

-- We characterize the identity type of the universe of pointed types

module _
  {l1 : Level} (A : Pointed-Type l1)
  where
  
  id-pointed-equiv : A ≃* A
  id-pointed-equiv = pair id-equiv refl

  pointed-equiv-eq : (B : Pointed-Type l1) → Id A B → A ≃* B
  pointed-equiv-eq .A refl = id-pointed-equiv

  is-contr-total-pointed-equiv : is-contr (Σ (Pointed-Type l1) (λ B → A ≃* B))
  is-contr-total-pointed-equiv =
    is-contr-total-Eq-structure
      ( λ X x (e : type-Pointed-Type A ≃ X) →
        Id (map-equiv e (pt-Pointed-Type A)) x)
      ( is-contr-total-equiv (type-Pointed-Type A))
      ( pair (type-Pointed-Type A) id-equiv)
      ( is-contr-total-path (pt-Pointed-Type A))

  is-equiv-pointed-equiv-eq :
    (B : Pointed-Type l1) → is-equiv (pointed-equiv-eq B)
  is-equiv-pointed-equiv-eq =
    fundamental-theorem-id A
      ( id-pointed-equiv)
      ( is-contr-total-pointed-equiv)
      ( pointed-equiv-eq)

  equiv-pointed-equiv-eq :
    (B : Pointed-Type l1) → Id A B ≃ (A ≃* B)
  equiv-pointed-equiv-eq B =
    pair (pointed-equiv-eq B) (is-equiv-pointed-equiv-eq B)

  eq-pointed-equiv : (B : Pointed-Type l1) → A ≃* B → Id A B
  eq-pointed-equiv B =
    map-inv-is-equiv (is-equiv-pointed-equiv-eq B)

-- Precomposing by pointed equivalences

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  is-equiv-is-equiv-precomp-pointed-map :
    ( {l : Level} (C : Pointed-Type l) →
      is-equiv (precomp-pointed-map A B C f)) →
    is-equiv-pointed-map A B f
  is-equiv-is-equiv-precomp-pointed-map H =
    is-equiv-has-inverse
      ( map-pointed-map B A g)
      ( htpy-eq
        ( ap pr1
          ( ap pr1
            ( eq-is-contr
              ( is-contr-map-is-equiv (H B) f)
              { pair
                ( comp-pointed-map B A B f g)
                ( eq-htpy-pointed-map A B
                  ( comp-pointed-map A B B
                    ( comp-pointed-map B A B f g)
                    ( f))
                  ( f)
                  ( concat-htpy-pointed-map A B
                    ( comp-pointed-map A B B
                      ( comp-pointed-map B A B f g)
                      ( f))
                    ( comp-pointed-map A A B f
                      ( comp-pointed-map A B A g f))
                    ( f)
                    ( assoc-comp-pointed-map A B A B f g f)
                    ( concat-htpy-pointed-map A B
                      ( comp-pointed-map A A B f
                        ( comp-pointed-map A B A g f))
                      ( comp-pointed-map A A B f id-pointed-map)
                      ( f)
                      ( left-whisker-htpy-pointed-map A A B f
                        ( comp-pointed-map A B A g f)
                        ( id-pointed-map)
                        ( G))
                      ( right-unit-law-comp-pointed-map A B f))))}
              { pair
                ( id-pointed-map)
                ( eq-htpy-pointed-map A B
                  ( comp-pointed-map A B B id-pointed-map f)
                  ( f)
                  ( left-unit-law-comp-pointed-map A B f))}))))
      ( pr1 G)
    where
    g : B →* A
    g = pr1 (center (is-contr-map-is-equiv (H A) id-pointed-map))
    G : htpy-pointed-map A A (comp-pointed-map A B A g f) id-pointed-map
    G = htpy-eq-pointed-map A A
          ( comp-pointed-map A B A g f)
          ( id-pointed-map)
          ( pr2 (center (is-contr-map-is-equiv (H A) id-pointed-map)))

  is-equiv-precomp-is-equiv-pointed-map :
    is-equiv-pointed-map A B f →
    {l : Level} → (C : Pointed-Type l) → is-equiv (precomp-pointed-map A B C f)
  is-equiv-precomp-is-equiv-pointed-map E C =
    pair
      ( pair
        ( precomp-pointed-map B A C h)
        ( λ k →
          eq-htpy-pointed-map A C
            ( comp-pointed-map A B C (comp-pointed-map B A C k h) f)
            ( k)
            ( concat-htpy-pointed-map A C
              ( comp-pointed-map A B C (comp-pointed-map B A C k h) f)
              ( comp-pointed-map A A C k (comp-pointed-map A B A h f))
              ( k)
              ( assoc-comp-pointed-map A B A C k h f)
              ( concat-htpy-pointed-map A C
                ( comp-pointed-map A A C k (comp-pointed-map A B A h f))
                ( comp-pointed-map A A C k id-pointed-map)
                ( k)
                ( left-whisker-htpy-pointed-map A A C k
                  ( comp-pointed-map A B A h f)
                  ( id-pointed-map)
                  ( H))
                ( right-unit-law-comp-pointed-map A C k)))))
      ( pair
        ( precomp-pointed-map B A C g)
        ( λ k →
          eq-htpy-pointed-map B C
            ( comp-pointed-map B A C (comp-pointed-map A B C k f) g)
            ( k)
            ( concat-htpy-pointed-map B C
              ( comp-pointed-map B A C (comp-pointed-map A B C k f) g)
              ( comp-pointed-map B B C k (comp-pointed-map B A B f g))
              ( k)
              ( assoc-comp-pointed-map B A B C k f g)
              ( concat-htpy-pointed-map B C
                ( comp-pointed-map B B C k (comp-pointed-map B A B f g))
                ( comp-pointed-map B B C k id-pointed-map)
                ( k)
                ( left-whisker-htpy-pointed-map B B C k
                  ( comp-pointed-map B A B f g)
                  ( id-pointed-map)
                  ( G))
                ( right-unit-law-comp-pointed-map B C k)))))
    where
    I : is-iso-pointed-map A B f
    I = is-iso-is-equiv-pointed-map A B f E
    g : B →* A
    g = pr1 (pr1 I)
    G : htpy-pointed-map B B (comp-pointed-map B A B f g) id-pointed-map
    G = pr2 (pr1 I)
    h : B →* A
    h = pr1 (pr2 I)
    H : htpy-pointed-map A A (comp-pointed-map A B A h f) id-pointed-map
    H = pr2 (pr2 I)

-- Postcomposing by pointed equivalences

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  is-equiv-is-equiv-comp-pointed-map :
    ({l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map X A B f)) →
    is-equiv-pointed-map A B f
  is-equiv-is-equiv-comp-pointed-map H =
    is-equiv-has-inverse
      ( map-pointed-map B A g)
      ( pr1 G)
      ( htpy-eq
        ( ap pr1
          ( ap pr1
            ( eq-is-contr
              ( is-contr-map-is-equiv (H A) f)
                { pair
                  ( comp-pointed-map A B A g f)
                  ( eq-htpy-pointed-map A B
                    ( comp-pointed-map A A B f (comp-pointed-map A B A g f))
                    ( f)
                    ( concat-htpy-pointed-map A B
                      ( comp-pointed-map A A B f (comp-pointed-map A B A g f))
                      ( comp-pointed-map A B B (comp-pointed-map B A B f g) f)
                      ( f)
                      ( inv-assoc-comp-pointed-map A B A B f g f)
                      ( concat-htpy-pointed-map A B
                        ( comp-pointed-map A B B (comp-pointed-map B A B f g) f)
                        ( comp-pointed-map A B B id-pointed-map f)
                        ( f)
                        ( right-whisker-htpy-pointed-map A B B
                          ( comp-pointed-map B A B f g)
                          ( id-pointed-map)
                          ( G)
                          ( f))
                        ( left-unit-law-comp-pointed-map A B f))))}
                { pair
                  ( id-pointed-map)
                  ( eq-htpy-pointed-map A B
                    ( comp-pointed-map A A B f id-pointed-map)
                    ( f)
                    ( right-unit-law-comp-pointed-map A B f))}))))
    where
    g : B →* A
    g = pr1 (center (is-contr-map-is-equiv (H B) id-pointed-map))
    G : htpy-pointed-map B B (comp-pointed-map B A B f g) id-pointed-map
    G = htpy-eq-pointed-map B B
          ( comp-pointed-map B A B f g)
          ( id-pointed-map)
          ( pr2 (center (is-contr-map-is-equiv (H B) id-pointed-map)))

  is-equiv-comp-is-equiv-pointed-map :
    is-equiv-pointed-map A B f →
    {l : Level} (X : Pointed-Type l) → is-equiv (comp-pointed-map X A B f)
  is-equiv-comp-is-equiv-pointed-map E X =
    pair
      ( pair
        ( comp-pointed-map X B A g)
        ( λ k →
          eq-htpy-pointed-map X B
            ( comp-pointed-map X A B f (comp-pointed-map X B A g k))
            ( k)
            ( concat-htpy-pointed-map X B
              ( comp-pointed-map X A B f (comp-pointed-map X B A g k))
              ( comp-pointed-map X B B (comp-pointed-map B A B f g) k)
              ( k)
              ( inv-assoc-comp-pointed-map X B A B f g k)
              ( concat-htpy-pointed-map X B
                ( comp-pointed-map X B B (comp-pointed-map B A B f g) k)
                ( comp-pointed-map X B B id-pointed-map k)
                ( k)
                ( right-whisker-htpy-pointed-map X B B
                  ( comp-pointed-map B A B f g)
                  ( id-pointed-map)
                  ( G)
                  ( k))
                ( left-unit-law-comp-pointed-map X B k)))))
      ( pair
        ( comp-pointed-map X B A h)
        ( λ k →
          eq-htpy-pointed-map X A
            ( comp-pointed-map X B A h (comp-pointed-map X A B f k))
            ( k)
            ( concat-htpy-pointed-map X A
              ( comp-pointed-map X B A h (comp-pointed-map X A B f k))
              ( comp-pointed-map X A A (comp-pointed-map A B A h f) k)
              ( k)
              ( inv-assoc-comp-pointed-map X A B A h f k)
              ( concat-htpy-pointed-map X A
                ( comp-pointed-map X A A (comp-pointed-map A B A h f) k)
                ( comp-pointed-map X A A id-pointed-map k)
                ( k)
                ( right-whisker-htpy-pointed-map X A A
                  ( comp-pointed-map A B A h f)
                  ( id-pointed-map)
                  ( H)
                  ( k))
                ( left-unit-law-comp-pointed-map X A k)))))
    where
    I : is-iso-pointed-map A B f
    I = is-iso-is-equiv-pointed-map A B f E
    g : B →* A
    g = pr1 (pr1 I)
    G : htpy-pointed-map B B (comp-pointed-map B A B f g) id-pointed-map
    G = pr2 (pr1 I)
    h : B →* A
    h = pr1 (pr2 I)
    H : htpy-pointed-map A A (comp-pointed-map A B A h f) id-pointed-map
    H = pr2 (pr2 I)

-- Loop spaces

module _
  {l : Level} (A : Pointed-Type l)
  where
  
  type-Ω : UU l
  type-Ω = Id (pt-Pointed-Type A) (pt-Pointed-Type A)

  refl-Ω : type-Ω
  refl-Ω = refl

  Ω : Pointed-Type l
  Ω = pair type-Ω refl-Ω

  -- Wild group structure on loop spaces

  mul-Ω : type-Ω → type-Ω → type-Ω
  mul-Ω x y = x ∙ y

  inv-Ω : type-Ω → type-Ω
  inv-Ω = inv

  associative-mul-Ω :
    (x y z : type-Ω) → Id (mul-Ω (mul-Ω x y) z) (mul-Ω x (mul-Ω y z))
  associative-mul-Ω x y z = assoc x y z

  left-unit-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω refl-Ω x) x
  left-unit-law-mul-Ω x = left-unit

  right-unit-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω x refl-Ω) x
  right-unit-law-mul-Ω x = right-unit

  left-inverse-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω (inv-Ω x) x) refl-Ω
  left-inverse-law-mul-Ω x = left-inv x

  right-inverse-law-mul-Ω :
    (x : type-Ω) → Id (mul-Ω x (inv-Ω x)) refl-Ω
  right-inverse-law-mul-Ω x = right-inv x

-- We compute transport of type-Ω

module _
  {l1 : Level} {A : UU l1} {x y : A} 
  where

  equiv-tr-Ω : Id x y → Ω (pair A x) ≃* Ω (pair A y)
  equiv-tr-Ω refl = pair id-equiv refl
  
  equiv-tr-type-Ω : Id x y → type-Ω (pair A x) ≃ type-Ω (pair A y)
  equiv-tr-type-Ω p =
    equiv-pointed-equiv (Ω (pair A x)) (Ω (pair A y)) (equiv-tr-Ω p)

  tr-type-Ω : Id x y → type-Ω (pair A x) → type-Ω (pair A y)
  tr-type-Ω p = map-equiv (equiv-tr-type-Ω p)

  is-equiv-tr-type-Ω : (p : Id x y) → is-equiv (tr-type-Ω p)
  is-equiv-tr-type-Ω p = is-equiv-map-equiv (equiv-tr-type-Ω p)

  preserves-refl-tr-Ω : (p : Id x y) → Id (tr-type-Ω p refl) refl
  preserves-refl-tr-Ω refl = refl

  preserves-mul-tr-Ω :
    (p : Id x y) (u v : type-Ω (pair A x)) →
    Id ( tr-type-Ω p (mul-Ω (pair A x) u v))
       ( mul-Ω (pair A y) (tr-type-Ω p u) (tr-type-Ω p v))
  preserves-mul-tr-Ω refl u v = refl

  preserves-inv-tr-Ω :
    (p : Id x y) (u : type-Ω (pair A x)) →
    Id ( tr-type-Ω p (inv-Ω (pair A x) u))
       ( inv-Ω (pair A y) (tr-type-Ω p u))
  preserves-inv-tr-Ω refl u = refl

-- We show that Ω is a functor

module _
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) (f : A →* B)
  where

  map-Ω : type-Ω A → type-Ω B
  map-Ω p =
    tr-type-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) p)
  
  preserves-refl-map-Ω : Id (map-Ω refl) refl
  preserves-refl-map-Ω = preserves-refl-tr-Ω (pr2 f)

  pointed-map-Ω : Ω A →* Ω B
  pointed-map-Ω = pair map-Ω preserves-refl-map-Ω

  preserves-mul-map-Ω :
    (x y : type-Ω A) → Id (map-Ω (mul-Ω A x y)) (mul-Ω B (map-Ω x) (map-Ω y))
  preserves-mul-map-Ω x y =
    ( ap
      ( tr-type-Ω (preserves-point-map-pointed-map A B f))
      ( ap-concat (map-pointed-map A B f) x y)) ∙
    ( preserves-mul-tr-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) x)
      ( ap (map-pointed-map A B f) y))

  preserves-inv-map-Ω :
    (x : type-Ω A) → Id (map-Ω (inv-Ω A x)) (inv-Ω B (map-Ω x))
  preserves-inv-map-Ω x =
    ( ap
      ( tr-type-Ω (preserves-point-map-pointed-map A B f))
      ( ap-inv (map-pointed-map A B f) x)) ∙
    ( preserves-inv-tr-Ω
      ( preserves-point-map-pointed-map A B f)
      ( ap (map-pointed-map A B f) x))

-- Iterated loop spaces

module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space zero-ℕ A = A
  iterated-loop-space (succ-ℕ n) A = Ω (iterated-loop-space n A)
  
  Ω² : Pointed-Type l → Pointed-Type l
  Ω² A = iterated-loop-space two-ℕ A
  
  type-Ω² : {A : UU l} (a : A) → UU l
  type-Ω² a = Id (refl {x = a}) (refl {x = a})
  
  refl-Ω² : {A : UU l} {a : A} → type-Ω² a
  refl-Ω² = refl
  
  Ω³ : Pointed-Type l → Pointed-Type l
  Ω³ A = iterated-loop-space three-ℕ A
  
  type-Ω³ : {A : UU l} (a : A) → UU l
  type-Ω³ a = Id (refl-Ω² {a = a}) (refl-Ω² {a = a})
  
  refl-Ω³ : {A : UU l} {a : A} → type-Ω³ a
  refl-Ω³ = refl
```
