# The universal cover of the circle

```agda
{-# OPTIONS --lossy-unification #-}

module synthetic-homotopy-theory.universal-cover-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.nonzero-integers
open import elementary-number-theory.universal-property-integers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.negation
open import foundation.precomposition-dependent-functions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

### 12.2 The universal cover of the circle

We show that if a type with a free loop satisfies the induction principle of the
circle with respect to any universe level, then it satisfies the induction
principle with respect to the zeroth universe level.

```agda
functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  free-dependent-loop l P → free-dependent-loop l Q
functor-free-dependent-loop l {P} {Q} f =
  map-Σ
    ( λ q → dependent-identification Q (loop-free-loop l) q q)
    ( f (base-free-loop l))
    ( λ p α →
      inv (preserves-tr f (loop-free-loop l) p) ∙
      ( ap (f (base-free-loop l)) α))

coherence-square-functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : x ＝ y)
  ( h : (x : X) → P x) →
  Id
    ( inv ( preserves-tr f α (h x)) ∙
      ( ap (f y) (apd h α)))
    ( apd (map-Π f h) α)
coherence-square-functor-free-dependent-loop f refl h = refl

square-functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  ( (functor-free-dependent-loop l f) ∘ (ev-free-loop-Π l P)) ~
  ( (ev-free-loop-Π l Q) ∘ (map-Π f))
square-functor-free-dependent-loop (pair x l) {P} {Q} f h =
  eq-Eq-free-dependent-loop (pair x l) Q
    ( functor-free-dependent-loop (pair x l) f
      ( ev-free-loop-Π (pair x l) P h))
    ( ev-free-loop-Π (pair x l) Q (map-Π f h))
    ( pair refl
      ( right-unit ∙ (coherence-square-functor-free-dependent-loop f l h)))

abstract
  is-equiv-functor-free-dependent-loop-is-fiberwise-equiv :
    { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
    { P : X → UU l2} {Q : X → UU l3} {f : (x : X) → P x → Q x}
    ( is-equiv-f : (x : X) → is-equiv (f x)) →
    is-equiv (functor-free-dependent-loop l f)
  is-equiv-functor-free-dependent-loop-is-fiberwise-equiv
    (pair x l) {P} {Q} {f} is-equiv-f =
    is-equiv-map-Σ
      ( λ q₀ → Id (tr Q l q₀) q₀)
      ( is-equiv-f x)
      ( λ p₀ →
        is-equiv-comp
          ( concat
            ( inv (preserves-tr f l p₀))
            ( f x p₀))
          ( ap (f x))
          ( is-emb-is-equiv (is-equiv-f x) (tr P l p₀) p₀)
          ( is-equiv-concat
            ( inv (preserves-tr f l p₀))
            ( f x p₀)))
```

### The universal cover

```agda
module _
  { l1 : Level} {S : UU l1} (l : free-loop S)
  where

  descent-data-universal-cover-circle : descent-data-circle lzero
  pr1 descent-data-universal-cover-circle = ℤ
  pr2 descent-data-universal-cover-circle = equiv-succ-ℤ

  module _
    ( dup-circle : dependent-universal-property-circle l)
    where

    abstract
      universal-cover-family-with-descent-data-circle :
        family-with-descent-data-circle l lzero
      universal-cover-family-with-descent-data-circle =
        family-with-descent-data-circle-descent-data l
          ( universal-property-dependent-universal-property-circle l dup-circle)
          ( descent-data-universal-cover-circle)

      universal-cover-circle : S → UU lzero
      universal-cover-circle =
        family-family-with-descent-data-circle
          universal-cover-family-with-descent-data-circle

      compute-fiber-universal-cover-circle :
        ℤ ≃ universal-cover-circle (base-free-loop l)
      compute-fiber-universal-cover-circle =
        equiv-family-with-descent-data-circle
          universal-cover-family-with-descent-data-circle

      compute-tr-universal-cover-circle :
        coherence-square-maps
          ( map-equiv compute-fiber-universal-cover-circle)
          ( succ-ℤ)
          ( tr universal-cover-circle (loop-free-loop l))
          ( map-equiv compute-fiber-universal-cover-circle)
      compute-tr-universal-cover-circle =
        coherence-square-family-with-descent-data-circle
          universal-cover-family-with-descent-data-circle

    map-compute-fiber-universal-cover-circle :
      ℤ → universal-cover-circle (base-free-loop l)
    map-compute-fiber-universal-cover-circle =
      map-equiv compute-fiber-universal-cover-circle
```

### The universal cover of the circle is a family of sets

```agda
abstract
  is-set-universal-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l) →
    ( x : X) → is-set (universal-cover-circle l dup-circle x)
  is-set-universal-cover-circle l dup-circle =
    is-connected-circle' l
      ( dup-circle)
      ( λ x → is-set (universal-cover-circle l dup-circle x))
      ( λ x → is-prop-is-set (universal-cover-circle l dup-circle x))
      ( is-trunc-is-equiv' zero-𝕋 ℤ
        ( map-equiv (compute-fiber-universal-cover-circle l dup-circle))
        ( is-equiv-map-equiv
          ( compute-fiber-universal-cover-circle l dup-circle))
        ( is-set-ℤ))
```

### Contractibility of a general total space

```agda
contraction-total-space :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (center : Σ A B) →
  ( x : A) → UU (l1 ⊔ l2)
contraction-total-space {B = B} center x =
  ( y : B x) → Id center (pair x y)

path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} (B : A → UU l2) (x : A) →
  { y y' : B x} (q : y' ＝ y) → Id {A = Σ A B} (pair x y) (pair x y')
path-total-path-fiber B x q = eq-pair-eq-fiber (inv q)

tr-path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { y y' : B x} (q : y' ＝ y) (α : Id c (pair x y')) →
  Id
    ( tr (λ z → Id c (pair x z)) q α)
    ( α ∙ (inv (path-total-path-fiber B x q)))
tr-path-total-path-fiber c x refl α = inv right-unit

segment-Σ :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  { x x' : A} (p : x ＝ x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) (y : F) →
  Id (pair x (map-equiv e y)) (pair x' (map-equiv e' (map-equiv f y)))
segment-Σ refl f e e' H y = path-total-path-fiber _ _ (H y)

contraction-total-space' :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) → UU (l1 ⊔ l2 ⊔ l3)
contraction-total-space' c x {F} e =
  ( y : F) → Id c (pair x (map-equiv e y))

equiv-tr-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : x ＝ x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x') →
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( contraction-total-space' c x' e') ≃ (contraction-total-space' c x e)
equiv-tr-contraction-total-space' c p f e e' H =
  ( equiv-Π-equiv-family
    ( λ y → equiv-concat' c (inv (segment-Σ p f e e' H y)))) ∘e
  ( equiv-precomp-Π f _)

equiv-contraction-total-space :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  ( x : A) → {F : UU l3} (e : F ≃ B x) →
  ( contraction-total-space c x) ≃ (contraction-total-space' c x e)
equiv-contraction-total-space c x e =
  equiv-precomp-Π e (λ y → Id c (pair x y))

tr-path-total-tr-coherence :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x)
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ (map-equiv e)) →
  (y : F) (α : Id c (pair x (map-equiv e' (map-equiv f y)))) →
  Id
    ( tr (λ z → Id c (pair x z)) (H y) α)
    ( α ∙ (inv (segment-Σ refl f e e' H y)))
tr-path-total-tr-coherence c x f e e' H y α =
  tr-path-total-path-fiber c x (H y) α

square-tr-contraction-total-space :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : x ＝ x')
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e)))
  (h : contraction-total-space c x) →
  ( map-equiv
    ( ( equiv-tr-contraction-total-space' c p f e e' H) ∘e
      ( ( equiv-contraction-total-space c x' e') ∘e
        ( equiv-tr (contraction-total-space c) p)))
    ( h)) ~
  ( map-equiv (equiv-contraction-total-space c x e) h)
square-tr-contraction-total-space c refl f e e' H h y =
  ( inv (tr-path-total-tr-coherence c _ f e e' H y
    ( h (map-equiv e' (map-equiv f y))))) ∙
  ( apd h (H y))

dependent-identification-contraction-total-space' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  {x x' : A} (p : x ＝ x') →
  {F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  (H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  (h : (y : F) → Id c (pair x (map-equiv e y))) →
  (h' : (y' : F') → Id c (pair x' (map-equiv e' y'))) →
  UU (l1 ⊔ l2 ⊔ l3)
dependent-identification-contraction-total-space'
  c {x} {x'} p {F} {F'} f e e' H h h' =
  ( map-Π
    ( λ y → concat' c (segment-Σ p f e e' H y)) h) ~
  ( precomp-Π
    ( map-equiv f)
    ( λ y' → Id c (pair x' (map-equiv e' y')))
    ( h'))

map-dependent-identification-contraction-total-space' :
    { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
    { x x' : A} (p : x ＝ x') →
    { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
    ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
    ( h : contraction-total-space' c x e) →
    ( h' : contraction-total-space' c x' e') →
    ( dependent-identification-contraction-total-space' c p f e e' H h h') →
    ( dependent-identification (contraction-total-space c) p
      ( map-inv-equiv (equiv-contraction-total-space c x e) h)
      ( map-inv-equiv (equiv-contraction-total-space c x' e') h'))
map-dependent-identification-contraction-total-space'
  c {x} {.x} refl f e e' H h h' α =
  map-inv-equiv
    ( equiv-ap
      ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
        ( equiv-contraction-total-space c x e'))
      ( map-inv-equiv (equiv-contraction-total-space c x e) h)
      ( map-inv-equiv (equiv-contraction-total-space c x e') h'))
    ( ( ( eq-htpy
          ( square-tr-contraction-total-space c refl f e e' H
            ( map-inv-equiv (equiv-contraction-total-space c x e) h))) ∙
        ( is-section-map-inv-is-equiv
          ( is-equiv-map-equiv (equiv-contraction-total-space c x e))
          ( h))) ∙
      ( ( eq-htpy
          ( right-transpose-htpy-concat h
            ( segment-Σ refl f e e' H)
            ( precomp-Π
              ( map-equiv f)
              ( λ y' → Id c (pair x (map-equiv e' y')))
              ( h'))
            ( α))) ∙
        ( inv
          ( ap
            ( map-equiv (equiv-tr-contraction-total-space' c refl f e e' H))
            ( is-section-map-inv-is-equiv
              ( is-equiv-map-equiv
                ( equiv-precomp-Π e' (λ y' → Id c (pair x y'))))
              ( h'))))))

equiv-dependent-identification-contraction-total-space' :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) →
  { x x' : A} (p : x ＝ x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') ( e : F ≃ B x) (e' : F' ≃ B x')
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( h : contraction-total-space' c x e) →
  ( h' : contraction-total-space' c x' e') →
  ( dependent-identification (contraction-total-space c) p
    ( map-inv-equiv (equiv-contraction-total-space c x e) h)
    ( map-inv-equiv (equiv-contraction-total-space c x' e') h')) ≃
  ( dependent-identification-contraction-total-space' c p f e e' H h h')
equiv-dependent-identification-contraction-total-space'
  c {x} {.x} refl f e e' H h h' =
  ( inv-equiv
    ( equiv-right-transpose-htpy-concat h
      ( segment-Σ refl f e e' H)
      ( precomp-Π
        ( map-equiv f)
        ( λ y' → Id c (pair x (map-equiv e' y')))
        ( h')))) ∘e
  ( ( equiv-funext) ∘e
    ( ( equiv-concat' h
        ( ap
          ( map-equiv (equiv-tr-contraction-total-space' c refl f e e' H))
          ( is-section-map-inv-is-equiv
            ( is-equiv-map-equiv
              ( equiv-precomp-Π e' (λ y' → Id c (pair x y'))))
            ( h')))) ∘e
      ( ( equiv-concat
          ( inv
            ( ( eq-htpy
                ( square-tr-contraction-total-space c refl f e e' H
                  ( map-inv-equiv (equiv-contraction-total-space c x e) h))) ∙
              ( is-section-map-inv-is-equiv
                ( is-equiv-map-equiv (equiv-contraction-total-space c x e))
                ( h))))
          ( map-equiv
            ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
              ( ( equiv-contraction-total-space c x e') ∘e
                ( inv-equiv (equiv-contraction-total-space c x e'))))
            ( h'))) ∘e
        ( equiv-ap
          ( ( equiv-tr-contraction-total-space' c refl f e e' H) ∘e
            ( equiv-contraction-total-space c x e'))
          ( map-inv-equiv (equiv-contraction-total-space c x e) h)
          ( map-inv-equiv (equiv-contraction-total-space c x e') h')))))
```

We use the above construction to provide sufficient conditions for the total
space of the universal cover to be contractible.

```agda
center-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  Σ X (universal-cover-circle l dup-circle)
pr1 (center-total-universal-cover-circle l dup-circle) = base-free-loop l
pr2 (center-total-universal-cover-circle l dup-circle) =
  map-equiv ( compute-fiber-universal-cover-circle l dup-circle) zero-ℤ

dependent-identification-loop-contraction-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  dependent-identification
    ( contraction-total-space
      ( center-total-universal-cover-circle l dup-circle))
    ( pr2 l)
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-universal-cover-circle l dup-circle))
      ( h))
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-universal-cover-circle l dup-circle))
      ( h))
dependent-identification-loop-contraction-total-universal-cover-circle
  l dup-circle h p =
  map-dependent-identification-contraction-total-space'
    ( center-total-universal-cover-circle l dup-circle)
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-tr-universal-cover-circle l dup-circle)
    ( h)
    ( h)
    ( p)

contraction-total-universal-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  ( t : Σ X (universal-cover-circle l dup-circle)) →
  Id (center-total-universal-cover-circle l dup-circle) t
contraction-total-universal-cover-circle-data
  {l1} l dup-circle h p (pair x y) =
  map-inv-is-equiv
    ( dup-circle
      ( contraction-total-space
        ( center-total-universal-cover-circle l dup-circle)))
    ( pair
      ( map-inv-equiv
        ( equiv-contraction-total-space
          ( center-total-universal-cover-circle l dup-circle)
          ( base-free-loop l)
          ( compute-fiber-universal-cover-circle l dup-circle))
        ( h))
      ( dependent-identification-loop-contraction-total-universal-cover-circle
        l dup-circle h p))
    x y

is-torsorial-universal-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( h :
    contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-universal-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-universal-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-fiber-universal-cover-circle l dup-circle)
      ( compute-tr-universal-cover-circle l dup-circle)
      ( h)
      ( h)) →
  is-torsorial (universal-cover-circle l dup-circle)
pr1 (is-torsorial-universal-cover-circle-data l dup-circle h p) =
  center-total-universal-cover-circle l dup-circle
pr2 (is-torsorial-universal-cover-circle-data l dup-circle h p) =
  contraction-total-universal-cover-circle-data l dup-circle h p
```

### Section 12.5 The identity type of the circle

```agda
path-total-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l)
  ( k : ℤ) →
  Id
    { A = Σ X (universal-cover-circle l dup-circle)}
    ( pair
      ( base-free-loop l)
      ( map-equiv (compute-fiber-universal-cover-circle l dup-circle) k))
    ( pair
      ( base-free-loop l)
      ( map-equiv
        ( compute-fiber-universal-cover-circle l dup-circle)
        ( succ-ℤ k)))
path-total-universal-cover-circle l dup-circle k =
  segment-Σ
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-fiber-universal-cover-circle l dup-circle)
    ( compute-tr-universal-cover-circle l dup-circle)
    k

CONTRACTION-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  UU l1
CONTRACTION-universal-cover-circle l dup-circle =
  ELIM-ℤ
    ( λ k →
      Id
        ( center-total-universal-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-universal-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-universal-cover-circle l dup-circle)
      ( path-total-universal-cover-circle l dup-circle k))

Contraction-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  CONTRACTION-universal-cover-circle l dup-circle
Contraction-universal-cover-circle l dup-circle =
  Elim-ℤ
    ( λ k →
      Id
        ( center-total-universal-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-universal-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-universal-cover-circle l dup-circle)
      ( path-total-universal-cover-circle l dup-circle k))

abstract
  is-torsorial-universal-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l) →
    is-torsorial (universal-cover-circle l dup-circle)
  is-torsorial-universal-cover-circle l dup-circle =
    is-torsorial-universal-cover-circle-data l dup-circle
      ( pr1 (Contraction-universal-cover-circle l dup-circle))
      ( inv-htpy
        ( pr2 (pr2 (Contraction-universal-cover-circle l dup-circle))))

point-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  universal-cover-circle l dup-circle (base-free-loop l)
point-universal-cover-circle l dup-circle =
  map-equiv (compute-fiber-universal-cover-circle l dup-circle) zero-ℤ

universal-cover-circle-eq :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( x : X) → Id (base-free-loop l) x → universal-cover-circle l dup-circle x
universal-cover-circle-eq l dup-circle .(base-free-loop l) refl =
  point-universal-cover-circle l dup-circle

abstract
  is-equiv-universal-cover-circle-eq :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : dependent-universal-property-circle l) →
    ( x : X) → is-equiv (universal-cover-circle-eq l dup-circle x)
  is-equiv-universal-cover-circle-eq l dup-circle =
    fundamental-theorem-id
      ( is-torsorial-universal-cover-circle l dup-circle)
      ( universal-cover-circle-eq l dup-circle)

equiv-universal-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  ( x : X) →
  ( Id (base-free-loop l) x) ≃ (universal-cover-circle l dup-circle x)
equiv-universal-cover-circle l dup-circle x =
  pair
    ( universal-cover-circle-eq l dup-circle x)
    ( is-equiv-universal-cover-circle-eq l dup-circle x)

compute-loop-space-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : dependent-universal-property-circle l) →
  type-Ω (X , base-free-loop l) ≃ ℤ
compute-loop-space-circle l dup-circle =
  ( inv-equiv (compute-fiber-universal-cover-circle l dup-circle)) ∘e
  ( equiv-universal-cover-circle l dup-circle (base-free-loop l))
```

### The loop of the circle is nontrivial

```agda
module _
  {l1 : Level} {X : UU l1} (l : free-loop X)
  (H : dependent-universal-property-circle l)
  where

  is-nontrivial-loop-dependent-universal-property-circle :
    loop-free-loop l ≠ refl
  is-nontrivial-loop-dependent-universal-property-circle p =
    is-nonzero-one-ℤ
      ( is-injective-equiv
        ( compute-fiber-universal-cover-circle l H)
        ( ( compute-tr-universal-cover-circle l H zero-ℤ) ∙
          ( ap
            ( λ q →
              tr
                ( universal-cover-circle l H)
                ( q)
                ( map-compute-fiber-universal-cover-circle l H zero-ℤ))
            ( p))))
```
