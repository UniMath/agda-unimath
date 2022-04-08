# Path algebra

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.path-algebra where

open import foundation.binary-embeddings using (is-binary-emb-is-binary-equiv)
open import foundation.binary-equivalences using (is-binary-equiv)
open import foundation.equivalences using (is-equiv)
open import foundation.identity-types using
  ( Id; refl; inv; _∙_; assoc; square; ap; concat'; concat; right-unit; ap-id;
    ap-binary; is-binary-equiv-concat; left-unit; left-unit-ap-binary;
    right-unit-ap-binary)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

```agda
horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-lleft : Id a b) (p-lbottom : Id b d) (p-rbottom : Id d f) →
  (p-middle : Id c d) (p-ltop : Id a c) (p-rtop : Id c e) (p-rright : Id e f) →
  (s-left : square p-lleft p-lbottom p-ltop p-middle)
  (s-right : square p-middle p-rbottom p-rtop p-rright) →
  square p-lleft (p-lbottom ∙ p-rbottom) (p-ltop ∙ p-rtop) p-rright
horizontal-concat-square {a = a} {f = f}
  p-lleft p-lbottom p-rbottom p-middle p-ltop p-rtop p-rright s-left s-right =
  ( inv (assoc p-lleft p-lbottom p-rbottom)) ∙
  ( ( ap (concat' a p-rbottom) s-left) ∙
    ( ( assoc p-ltop p-middle p-rbottom) ∙
      ( ( ap (concat p-ltop f) s-right) ∙
        ( inv (assoc p-ltop p-rtop p-rright)))))

horizontal-unit-square :
  {l : Level} {A : UU l} {a b : A} (p : Id a b) →
  square p refl refl p
horizontal-unit-square p = right-unit 

left-unit-law-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : Id a b) (p-bottom : Id b d) (p-top : Id a c) (p-right : Id c d) →
  (s : square p-left p-bottom p-top p-right) →
  Id ( horizontal-concat-square
       p-left refl p-bottom p-left refl p-top p-right
       ( horizontal-unit-square p-left)
       ( s))
     ( s)
left-unit-law-horizontal-concat-square refl p-bottom p-top p-right s =
  right-unit ∙ ap-id s

{-
right-unit-law-concat-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : Id a b) (p-bottom : Id b d) (p-top : Id a c) (p-right : Id c d) →
  (s : square p-left p-bottom p-top p-right) →
  Id ( horizontal-concat-square
       p-left p-bottom refl p-right p-top refl p-right
       ( s)
       ( horizontal-unit-square p-right))
     ( s)
right-unit-law-concat-horizontal-concat-square
  p-left p-bottom p-top p-right s = ?
-}

vertical-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-tleft : Id a b) (p-bleft : Id b c) (p-bbottom : Id c f)
  (p-middle : Id b e) (p-ttop : Id a d) (p-tright : Id d e) (p-bright : Id e f)
  (s-top : square p-tleft p-middle p-ttop p-tright)
  (s-bottom : square p-bleft p-bbottom p-middle p-bright) →
  square (p-tleft ∙ p-bleft) p-bbottom p-ttop (p-tright ∙ p-bright)
vertical-concat-square {a = a} {f = f}
  p-tleft p-bleft p-bbottom p-middle p-ttop p-tright p-bright s-top s-bottom =
  ( assoc p-tleft p-bleft p-bbottom) ∙
  ( ( ap (concat p-tleft f) s-bottom) ∙
    ( ( inv (assoc p-tleft p-middle p-bright)) ∙
      ( ( ap (concat' a p-bright) s-top) ∙
        ( assoc p-ttop p-tright p-bright))))
```

## Unit laws for the associator

```agda
unit-law-assoc-011 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc refl p q) refl
unit-law-assoc-011 p q = refl

unit-law-assoc-101 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc p refl q) (ap (concat' x q) right-unit)
unit-law-assoc-101 refl refl = refl

unit-law-assoc-101' :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (inv (assoc p refl q)) (ap (concat' x q) (inv right-unit))
unit-law-assoc-101' refl refl = refl

unit-law-assoc-110 :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (assoc p q refl ∙ ap (concat p z) right-unit) right-unit
unit-law-assoc-110 refl refl = refl

unit-law-assoc-110' :
  {l : Level} {X : UU l} {x y z : X} (p : Id x y) (q : Id y z) →
  Id (inv right-unit ∙ assoc p q refl) (ap (concat p z) (inv right-unit))
unit-law-assoc-110' refl refl = refl

--------------------------------------------------------------------------------

{- Identity types of identity types -}

--------------------------------------------------------------------------------

{- Vertical and horizontal concatenation in identity types of identity types -}

vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} → Id p q → Id q r → Id p r
vertical-concat-Id² α β = α ∙ β

horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  Id p q → Id u v → Id (p ∙ u) (q ∙ v)
horizontal-concat-Id² α β = ap-binary (λ s t → s ∙ t) α β

-- both operations are binary equivalences

is-binary-equiv-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} →
  is-binary-equiv (vertical-concat-Id² {l} {A} {x} {y} {p} {q} {r})
is-binary-equiv-vertical-concat-Id² = is-binary-equiv-concat

is-binary-equiv-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z} →
  is-binary-equiv (horizontal-concat-Id² {l} {A} {x} {y} {z} {p} {q} {u} {v})
is-binary-equiv-horizontal-concat-Id² =
  is-binary-emb-is-binary-equiv is-binary-equiv-concat

-- both operations satisfy unit laws

left-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {β : Id p q} →
  Id (vertical-concat-Id² refl β) β
left-unit-law-vertical-concat-Id² = left-unit

right-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α : Id p q} →
  Id (vertical-concat-Id² α refl) α
right-unit-law-vertical-concat-Id² = right-unit

left-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : Id x y} {u v : Id y z} (γ : Id u v) →
  Id (horizontal-concat-Id² (refl {x = p}) γ) (ap (concat p z) γ)
left-unit-law-horizontal-concat-Id² γ = left-unit-ap-binary (λ s t → s ∙ t) γ

right-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (α : Id p q) {u : Id y z} →
  Id (horizontal-concat-Id² α (refl {x = u})) (ap (concat' x u) α)
right-unit-law-horizontal-concat-Id² α = right-unit-ap-binary (λ s t → s ∙ t) α

--------------------------------------------------------------------------------

{- Three ways to concatenate in triple identity types -}

{- We name the three concatenations of triple identity types x-, y-, and z-
   concatenation, after the standard names for the three axis in 3-dimensional
   space. -}

x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β γ : Id p q} →
  Id α β → Id β γ → Id α γ
x-concat-Id³ σ τ = vertical-concat-Id² σ τ

y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} → Id α β → Id γ δ → Id (α ∙ γ) (β ∙ δ)
y-concat-Id³ σ τ = horizontal-concat-Id² σ τ

z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} →
  Id α β → Id γ δ → Id (horizontal-concat-Id² α γ) (horizontal-concat-Id² β δ)
z-concat-Id³ σ τ = ap-binary (λ s t → horizontal-concat-Id² s t) σ τ

-- All three operations satisfy unit laws

left-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {σ : Id α β} →
  Id (x-concat-Id³ refl σ) σ
left-unit-law-x-concat-Id³ = left-unit-law-vertical-concat-Id²

right-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q} {τ : Id α β} →
  Id (x-concat-Id³ τ refl) τ
right-unit-law-x-concat-Id³ = right-unit-law-vertical-concat-Id²

left-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α : Id p q} {γ δ : Id q r}
  {τ : Id γ δ} → Id (y-concat-Id³ (refl {x = α}) τ) (ap (concat α r) τ)
left-unit-law-y-concat-Id³ {τ = τ} = left-unit-law-horizontal-concat-Id² τ

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q} {γ : Id q r}
  {σ : Id α β} → Id (y-concat-Id³ σ (refl {x = γ})) (ap (concat' p γ) σ)
right-unit-law-y-concat-Id³ {σ = σ} = right-unit-law-horizontal-concat-Id² σ

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α : Id p q} {γ δ : Id u v} (τ : Id γ δ) →
  Id (z-concat-Id³ (refl {x = α}) τ) (ap (horizontal-concat-Id² α) τ)
left-unit-law-z-concat-Id³ τ =
  left-unit-ap-binary (λ s t → horizontal-concat-Id² s t) τ

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ : Id u v} (σ : Id α β) →
  Id (z-concat-Id³ σ (refl {x = γ})) (ap (λ ω → horizontal-concat-Id² ω γ) σ)
right-unit-law-z-concat-Id³ σ =
  right-unit-ap-binary (λ s t → horizontal-concat-Id² s t) σ

--------------------------------------------------------------------------------

{- Four ways to concatenatie in quadruple identity types -}

{- We name the three non-standard concatenations in quadruple identity types
   i-, j-, and k-concatenation, after the standard names for the quaternions
   i, j, and k. -}

concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β : Id p q}
  {r s t : Id α β} → Id r s → Id s t → Id r t
concat-Id⁴ σ τ = x-concat-Id³ σ τ

i-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : Id x y} {α β γ : Id p q} →
  {s s' : Id α β} (σ : Id s s') {t t' : Id β γ} (τ : Id t t') →
  Id (x-concat-Id³ s t) (x-concat-Id³ s' t')
i-concat-Id⁴ σ τ = y-concat-Id³ σ τ

j-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β : Id p q}
  {γ δ : Id q r} {s s' : Id α β} (σ : Id s s') {t t' : Id γ δ} (τ : Id t t') →
  Id (y-concat-Id³ s t) (y-concat-Id³ s' t')
j-concat-Id⁴ σ τ = z-concat-Id³ σ τ

k-concat-Id⁴ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β : Id p q} {γ δ : Id u v} {s s' : Id α β} (σ : Id s s') {t t' : Id γ δ}
  (τ : Id t t') → Id (z-concat-Id³ s t) (z-concat-Id³ s' t')
k-concat-Id⁴ σ τ = ap-binary (λ m n → z-concat-Id³ m n) σ τ

--------------------------------------------------------------------------------

{- The interchange law at the level of identity types of identity types -}

interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  (α : Id p q) (β : Id q r) (γ : Id u v) (δ : Id v w) →
  Id ( horizontal-concat-Id²
       ( vertical-concat-Id² α β)
       ( vertical-concat-Id² γ δ))
     ( vertical-concat-Id²
       ( horizontal-concat-Id² α γ)
       ( horizontal-concat-Id² β δ))
interchange-Id² refl refl refl refl = refl

unit-law-α-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (α : Id p q) (u : Id y z) →
  Id ( ( interchange-Id² α refl (refl {x = u}) refl) ∙
       ( right-unit ∙ right-unit-law-horizontal-concat-Id² α))
     ( ( right-unit-law-horizontal-concat-Id² (α ∙ refl)) ∙
       ( ap (ap (concat' x u)) right-unit))
unit-law-α-interchange-Id² refl u = refl

unit-law-β-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} (β : Id p q) (u : Id y z) →
  Id ( interchange-Id² refl β (refl {x = u}) refl) refl
unit-law-β-interchange-Id² refl u = refl

unit-law-γ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : Id x y) {u v : Id y z} (γ : Id u v) →
  Id ( ( interchange-Id² (refl {x = p}) refl γ refl) ∙
       ( right-unit ∙ left-unit-law-horizontal-concat-Id² γ))
     ( ( left-unit-law-horizontal-concat-Id² (γ ∙ refl)) ∙
       ( ap (ap (concat p z)) right-unit))
unit-law-γ-interchange-Id² p refl = refl

unit-law-δ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : Id x y) {u v : Id y z} (δ : Id u v) →
  Id ( interchange-Id² (refl {x = p}) refl refl δ) refl
unit-law-δ-interchange-Id² p refl = refl

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

-- Identity types of identity types of identity types

interchange-x-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : Id x y} {α β γ : Id p q}
  {δ ε ζ : Id q r} (σ : Id α β) (τ : Id β γ) (υ : Id δ ε) (ϕ : Id ε ζ) →
  Id ( y-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ))
     ( x-concat-Id³ (y-concat-Id³ σ υ) (y-concat-Id³ τ ϕ))
interchange-x-y-concat-Id³ = interchange-Id²

interchange-x-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : Id x y} {u v : Id y z}
  {α β γ : Id p q} {δ ε ζ : Id u v} (σ : Id α β) (τ : Id β γ) (υ : Id δ ε)
  (ϕ : Id ε ζ) →
  Id ( z-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ))
     ( x-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ))
interchange-x-z-concat-Id³ refl τ refl ϕ = refl

interchange-y-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q r : Id x y} {u v w : Id y z}
  {α β : Id p q} {γ δ : Id q r} {ε ζ : Id u v} {η θ : Id v w}
  (σ : Id α β) (τ : Id γ δ) (υ : Id ε ζ) (ϕ : Id η θ) →
  Id ( ( z-concat-Id³ (y-concat-Id³ σ τ) (y-concat-Id³ υ ϕ)) ∙
       ( interchange-Id² β δ ζ θ))
     ( ( interchange-Id² α γ ε η) ∙
       ( y-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ)))
interchange-y-z-concat-Id³ refl refl refl refl = inv right-unit
```

### Commuting cubes

```agda
module _
  {l : Level} {A : UU l} {x000 x001 x010 x100 x011 x101 x110 x111 : A}
  where
  
  cube :
    (p000̂ : Id x000 x001) (p00̂0 : Id x000 x010) (p0̂00 : Id x000 x100)
    (p00̂1 : Id x001 x011) (p0̂01 : Id x001 x101) (p010̂ : Id x010 x011)
    (p0̂10 : Id x010 x110) (p100̂ : Id x100 x101) (p10̂0 : Id x100 x110)
    (p0̂11 : Id x011 x111) (p10̂1 : Id x101 x111) (p110̂ : Id x110 x111)
    (p00̂0̂ : square p000̂ p00̂1 p00̂0 p010̂)
    (p0̂00̂ : square p000̂ p0̂01 p0̂00 p100̂)
    (p0̂0̂0 : square p00̂0 p0̂10 p0̂00 p10̂0)
    (p0̂0̂1 : square p00̂1 p0̂11 p0̂01 p10̂1)
    (p0̂10̂ : square p010̂ p0̂11 p0̂10 p110̂)
    (p10̂0̂ : square p100̂ p10̂1 p10̂0 p110̂) → UU l
  cube
    p000̂ p00̂0 p0̂00 p00̂1 p0̂01 p010̂ p0̂10 p100̂ p10̂0 p0̂11 p10̂1 p110̂
    p00̂0̂ p0̂00̂ p0̂0̂0 p0̂0̂1 p0̂10̂ p10̂0̂ =
    Id ( ( ap (concat' x000 p0̂11) p00̂0̂) ∙
         ( ( assoc p00̂0 p010̂ p0̂11) ∙
           ( ( ap (concat p00̂0 x111) p0̂10̂) ∙
             ( ( inv (assoc p00̂0 p0̂10 p110̂)) ∙
               ( ( ap (concat' x000 p110̂) p0̂0̂0) ∙
                 ( assoc p0̂00 p10̂0 p110̂))))))
       ( ( assoc p000̂ p00̂1 p0̂11) ∙
         (  ( ap (concat p000̂ x111) p0̂0̂1) ∙
           ( ( inv (assoc p000̂ p0̂01 p10̂1)) ∙
             ( ( ap (concat' x000 p10̂1) p0̂00̂) ∙
               ( ( assoc p0̂00 p100̂ p10̂1) ∙
                 ( ( ap (concat p0̂00 x111) p10̂0̂)))))))
