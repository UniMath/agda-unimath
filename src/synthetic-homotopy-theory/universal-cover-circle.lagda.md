# The universal cover of the circle

```agda
module synthetic-homotopy-theory.universal-cover-circle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

### 12.2 The fundamental cover of the circle

We show that if a type with a free loop satisfies the induction principle of the
circle with respect to any universe level, then it satisfies the induction
principle with respect to the zeroth universe level.

```agda
naturality-tr-fiberwise-transformation :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : Id x y) (p : P x) →
  Id (tr Q α (f x p)) (f y (tr P α p))
naturality-tr-fiberwise-transformation f refl p = refl

functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  { P : X → UU l2} {Q : X → UU l3} (f : (x : X) → P x → Q x) →
  free-dependent-loop l P → free-dependent-loop l Q
functor-free-dependent-loop l {P} {Q} f =
  map-Σ
    ( λ q₀ → Id (tr Q (loop-free-loop l) q₀) q₀)
    ( f (base-free-loop l))
    ( λ p₀ α →
      ( naturality-tr-fiberwise-transformation f (loop-free-loop l) p₀) ∙
      ( ap (f (base-free-loop l)) α))

coherence-square-functor-free-dependent-loop :
  { l1 l2 l3 : Level} {X : UU l1} {P : X → UU l2} {Q : X → UU l3}
  ( f : (x : X) → P x → Q x) {x y : X} (α : Id x y)
  ( h : (x : X) → P x) →
  Id
    ( ( naturality-tr-fiberwise-transformation f α (h x)) ∙
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
      ( _)
      ( _)
      ( is-equiv-f x)
      ( λ p₀ →
        is-equiv-comp
          ( concat
            ( naturality-tr-fiberwise-transformation f l p₀)
            ( f x p₀))
          ( ap (f x))
          ( is-emb-is-equiv (is-equiv-f x) (tr P l p₀) p₀)
          ( is-equiv-concat
            ( naturality-tr-fiberwise-transformation f l p₀)
            ( f x p₀)))

abstract
  lower-dependent-universal-property-circle :
    { l1 l2 : Level} (l3 : Level) {X : UU l1} (l : free-loop X) →
    dependent-universal-property-circle (l2 ⊔ l3) l →
    dependent-universal-property-circle l3 l
  lower-dependent-universal-property-circle {l1} {l2} l3 l dup-circle P =
    is-equiv-left-is-equiv-right-square
      ( ev-free-loop-Π l P)
      ( ev-free-loop-Π l (λ x → raise l2 (P x)))
      ( map-Π (λ x → map-raise))
      ( functor-free-dependent-loop l (λ x → map-raise))
      ( square-functor-free-dependent-loop l (λ x → map-raise))
      ( is-equiv-map-Π _ (λ x → is-equiv-map-raise))
      ( is-equiv-functor-free-dependent-loop-is-fiberwise-equiv l
        ( λ x → is-equiv-map-raise))
      ( dup-circle (λ x → raise l2 (P x)))

abstract
  lower-lzero-dependent-universal-property-circle :
    { l1 l2 : Level} {X : UU l1} (l : free-loop X) →
    dependent-universal-property-circle l2 l →
    dependent-universal-property-circle lzero l
  lower-lzero-dependent-universal-property-circle =
    lower-dependent-universal-property-circle lzero
```

### The fundamental cover

```agda
abstract
  Fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( {l2 : Level} → dependent-universal-property-circle l2 l) →
    Σ ( X → UU lzero)
      ( λ P →
        Eq-descent-data-circle
        ( pair ℤ equiv-succ-ℤ)
        ( ev-descent-data-circle l P))
  Fundamental-cover-circle {l1} l dup-circle =
    center
      ( unique-family-property-universal-property-circle l
        ( universal-property-dependent-universal-property-circle l
          ( dup-circle))
        ( pair ℤ equiv-succ-ℤ))

  fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ({k : Level} → dependent-universal-property-circle k l) →
    X → UU lzero
  fundamental-cover-circle l dup-circle =
    pr1 (Fundamental-cover-circle l dup-circle)

  compute-fiber-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ℤ ≃ fundamental-cover-circle l dup-circle (base-free-loop l)
  compute-fiber-fundamental-cover-circle l dup-circle =
    pr1 ( pr2 ( Fundamental-cover-circle l dup-circle))

  compute-tr-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ( ( map-equiv (compute-fiber-fundamental-cover-circle l dup-circle)) ∘
      ( succ-ℤ)) ~
    ( ( tr (fundamental-cover-circle l dup-circle) (loop-free-loop l)) ∘
      ( map-equiv (compute-fiber-fundamental-cover-circle l dup-circle)))
  compute-tr-fundamental-cover-circle l dup-circle =
    pr2 ( pr2 ( Fundamental-cover-circle l dup-circle))
```

### The fundamental cover of the circle is a family of sets

```agda
abstract
  is-set-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ( x : X) → is-set (fundamental-cover-circle l dup-circle x)
  is-set-fundamental-cover-circle l dup-circle =
    is-connected-circle' l
      ( dup-circle)
      ( λ x → is-set (fundamental-cover-circle l dup-circle x))
      ( λ x → is-prop-is-set (fundamental-cover-circle l dup-circle x))
      ( is-trunc-is-equiv' zero-𝕋 ℤ
        ( map-equiv (compute-fiber-fundamental-cover-circle l dup-circle))
        ( is-equiv-map-equiv
          ( compute-fiber-fundamental-cover-circle l dup-circle))
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
  { y y' : B x} (q : Id y' y) → Id {A = Σ A B} (pair x y) (pair x y')
path-total-path-fiber B x q = eq-pair-Σ refl (inv q)

tr-path-total-path-fiber :
  { l1 l2 : Level} {A : UU l1} {B : A → UU l2} (c : Σ A B) (x : A) →
  { y y' : B x} (q : Id y' y) (α : Id c (pair x y')) →
  Id
    ( tr (λ z → Id c (pair x z)) q α)
    ( α ∙ (inv (path-total-path-fiber B x q)))
tr-path-total-path-fiber c x refl α = inv right-unit

segment-Σ :
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  { x x' : A} (p : Id x x')
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
  { x x' : A} (p : Id x x') →
  { F : UU l3} {F' : UU l4} (f : F ≃ F') (e : F ≃ B x) (e' : F' ≃ B x') →
  ( H : ((map-equiv e') ∘ (map-equiv f)) ~ ((tr B p) ∘ (map-equiv e))) →
  ( contraction-total-space' c x' e') ≃ (contraction-total-space' c x e)
equiv-tr-contraction-total-space' c p f e e' H =
  ( equiv-map-Π
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
  { x x' : A} (p : Id x x')
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
  {x x' : A} (p : Id x x') →
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
    { x x' : A} (p : Id x x') →
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
          ( con-inv-htpy h
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
  { x x' : A} (p : Id x x') →
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
    ( equiv-con-inv-htpy h
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
space of the fundamental cover to be contractible.

```agda
center-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  Σ X (fundamental-cover-circle l dup-circle)
pr1 (center-total-fundamental-cover-circle l dup-circle) = base-free-loop l
pr2 (center-total-fundamental-cover-circle l dup-circle) =
  map-equiv ( compute-fiber-fundamental-cover-circle l dup-circle) zero-ℤ

dependent-identification-loop-contraction-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  dependent-identification
    ( contraction-total-space
      ( center-total-fundamental-cover-circle l dup-circle))
    ( pr2 l)
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-fundamental-cover-circle l dup-circle))
      ( h))
    ( map-inv-equiv
      ( equiv-contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)
        ( base-free-loop l)
        ( compute-fiber-fundamental-cover-circle l dup-circle))
      ( h))
dependent-identification-loop-contraction-total-fundamental-cover-circle
  l dup-circle h p =
  map-dependent-identification-contraction-total-space'
    ( center-total-fundamental-cover-circle l dup-circle)
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-fundamental-cover-circle l dup-circle)
    ( compute-fiber-fundamental-cover-circle l dup-circle)
    ( compute-tr-fundamental-cover-circle l dup-circle)
    ( h)
    ( h)
    ( p)

contraction-total-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  ( t : Σ X (fundamental-cover-circle l dup-circle)) →
  Id (center-total-fundamental-cover-circle l dup-circle) t
contraction-total-fundamental-cover-circle-data
  {l1} l dup-circle h p (pair x y) =
  map-inv-is-equiv
    ( lower-dependent-universal-property-circle
      { l2 = lsuc lzero} l1 l dup-circle
      ( contraction-total-space
        ( center-total-fundamental-cover-circle l dup-circle)))
    ( pair
      ( map-inv-equiv
        ( equiv-contraction-total-space
          ( center-total-fundamental-cover-circle l dup-circle)
          ( base-free-loop l)
          ( compute-fiber-fundamental-cover-circle l dup-circle))
        ( h))
      ( dependent-identification-loop-contraction-total-fundamental-cover-circle
        l dup-circle h p))
    x y

is-contr-total-fundamental-cover-circle-data :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( h :
    contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( base-free-loop l)
      ( compute-fiber-fundamental-cover-circle l dup-circle)) →
  ( p :
    dependent-identification-contraction-total-space'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( loop-free-loop l)
      ( equiv-succ-ℤ)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-fiber-fundamental-cover-circle l dup-circle)
      ( compute-tr-fundamental-cover-circle l dup-circle)
      ( h)
      ( h)) →
  is-contr (Σ X (fundamental-cover-circle l dup-circle))
pr1 (is-contr-total-fundamental-cover-circle-data l dup-circle h p) =
  center-total-fundamental-cover-circle l dup-circle
pr2 (is-contr-total-fundamental-cover-circle-data l dup-circle h p) =
  contraction-total-fundamental-cover-circle-data l dup-circle h p
```

### Section 12.4 The dependent universal property of ℤ

```agda
abstract
  elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( k : ℤ) → P k
  elim-ℤ P p0 pS (inl zero-ℕ) =
    map-inv-is-equiv (is-equiv-map-equiv (pS neg-one-ℤ)) p0
  elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    map-inv-is-equiv
      ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (inl x))
  elim-ℤ P p0 pS (inr (inl star)) = p0
  elim-ℤ P p0 pS (inr (inr zero-ℕ)) = map-equiv (pS zero-ℤ) p0
  elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
    map-equiv
      ( pS (inr (inr x)))
      ( elim-ℤ P p0 pS (inr (inr x)))

  compute-zero-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    Id (elim-ℤ P p0 pS zero-ℤ) p0
  compute-zero-elim-ℤ P p0 pS = refl

  compute-succ-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
    Id (elim-ℤ P p0 pS (succ-ℤ k)) (map-equiv (pS k) (elim-ℤ P p0 pS k))
  compute-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl zero-ℕ)))
        ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
  compute-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
        ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
  compute-succ-elim-ℤ P p0 pS (inr (inl star)) = refl
  compute-succ-elim-ℤ P p0 pS (inr (inr x)) = refl

ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → UU l1
ELIM-ℤ P p0 pS =
  Σ ( (k : ℤ) → P k)
    ( λ f →
      ( ( Id (f zero-ℤ) p0) ×
        ( (k : ℤ) → Id (f (succ-ℤ k)) ((map-equiv (pS k)) (f k)))))

Elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → ELIM-ℤ P p0 pS
pr1 (Elim-ℤ P p0 pS) = elim-ℤ P p0 pS
pr1 (pr2 (Elim-ℤ P p0 pS)) = compute-zero-elim-ℤ P p0 pS
pr2 (pr2 (Elim-ℤ P p0 pS)) = compute-succ-elim-ℤ P p0 pS

equiv-comparison-map-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (k : ℤ) →
  Id ((pr1 s) k) ((pr1 t) k) ≃ Id ((pr1 s) (succ-ℤ k)) ((pr1 t) (succ-ℤ k))
equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k =
  ( ( equiv-concat (pr2 (pr2 s) k) (pr1 t (succ-ℤ k))) ∘e
    ( equiv-concat' (map-equiv (pS k) (pr1 s k)) (inv (pr2 (pr2 t) k)))) ∘e
  ( equiv-ap (pS k) (pr1 s k) (pr1 t k))

zero-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
zero-Eq-ELIM-ℤ P p0 pS s t H =
  Id (H zero-ℤ) ((pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))

succ-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
succ-Eq-ELIM-ℤ P p0 pS s t H =
  ( k : ℤ) →
  Id
    ( H (succ-ℤ k))
    ( map-equiv (equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k) (H k))

Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → UU l1
Eq-ELIM-ℤ P p0 pS s t =
  ELIM-ℤ
    ( λ k → Id (pr1 s k) (pr1 t k))
    ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
    ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)

reflexive-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s s
pr1 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H)) = refl-htpy
pr1 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv (right-inv p)
pr2 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv ∘ (right-inv ∘ H)

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Id s t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq P p0 pS s .s refl = reflexive-Eq-ELIM-ℤ P p0 pS s

abstract
  is-contr-total-Eq-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s : ELIM-ℤ P p0 pS) → is-contr (Σ (ELIM-ℤ P p0 pS) (Eq-ELIM-ℤ P p0 pS s))
  is-contr-total-Eq-ELIM-ℤ P p0 pS s =
    is-contr-total-Eq-structure
      ( λ f t H →
        ( zero-Eq-ELIM-ℤ P p0 pS s (pair f t) H) ×
        ( succ-Eq-ELIM-ℤ P p0 pS s (pair f t) H))
      ( is-contr-total-htpy (pr1 s))
      ( pair (pr1 s) refl-htpy)
      ( is-contr-total-Eq-structure
        ( λ p K
          ( q : zero-Eq-ELIM-ℤ P p0 pS s
            ( pair (pr1 s) (pair p K))
            ( refl-htpy)) →
          succ-Eq-ELIM-ℤ P p0 pS s
            ( pair (pr1 s) (pair p K))
            ( refl-htpy))
        ( is-contr-is-equiv'
          ( Σ (Id (pr1 s zero-ℤ) p0) (λ α → Id α (pr1 (pr2 s))))
          ( tot (λ α → con-inv refl α (pr1 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α → is-equiv-con-inv refl α (pr1 (pr2 s))))
          ( is-contr-total-path' (pr1 (pr2 s))))
        ( pair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
        ( is-contr-is-equiv'
          ( Σ ( ( k : ℤ) → Id (pr1 s (succ-ℤ k)) (pr1 (pS k) (pr1 s k)))
              ( λ β → β ~ (pr2 (pr2 s))))
          ( tot (λ β → con-inv-htpy refl-htpy β (pr2 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ β → is-equiv-con-inv-htpy refl-htpy β (pr2 (pr2 s))))
          ( is-contr-total-htpy' (pr2 (pr2 s)))))

abstract
  is-equiv-Eq-ELIM-ℤ-eq :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
  is-equiv-Eq-ELIM-ℤ-eq P p0 pS s =
    fundamental-theorem-id
      ( is-contr-total-Eq-ELIM-ℤ P p0 pS s)
      ( Eq-ELIM-ℤ-eq P p0 pS s)

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → Id s t
eq-Eq-ELIM-ℤ P p0 pS s t = map-inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq P p0 pS s t)

abstract
  is-prop-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-prop (ELIM-ℤ P p0 pS)
  is-prop-ELIM-ℤ P p0 pS =
    is-prop-all-elements-equal
      ( λ s t → eq-Eq-ELIM-ℤ P p0 pS s t
        ( Elim-ℤ
          ( λ k → Id (pr1 s k) (pr1 t k))
          ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
          ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)))
```

We finally arrive at the dependent universal property of ℤ

```agda
abstract
  is-contr-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-contr (ELIM-ℤ P p0 pS)
  is-contr-ELIM-ℤ P p0 pS =
    is-proof-irrelevant-is-prop (is-prop-ELIM-ℤ P p0 pS) (Elim-ℤ P p0 pS)
```

The universal property of ℤ is now just a special case

```agda
ELIM-ℤ' :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → UU l1
ELIM-ℤ' {X = X} x e = ELIM-ℤ (λ k → X) x (λ k → e)

abstract
  universal-property-ℤ :
    { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
  universal-property-ℤ {X = X} x e = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)
```

### Section 12.5 The identity type of the circle

```agda
path-total-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l)
  ( k : ℤ) →
  Id
    { A = Σ X (fundamental-cover-circle l dup-circle)}
    ( pair
      ( base-free-loop l)
      ( map-equiv (compute-fiber-fundamental-cover-circle l dup-circle) k))
    ( pair
      ( base-free-loop l)
      ( map-equiv
        ( compute-fiber-fundamental-cover-circle l dup-circle)
        ( succ-ℤ k)))
path-total-fundamental-cover-circle l dup-circle k =
  segment-Σ
    ( loop-free-loop l)
    ( equiv-succ-ℤ)
    ( compute-fiber-fundamental-cover-circle l dup-circle)
    ( compute-fiber-fundamental-cover-circle l dup-circle)
    ( compute-tr-fundamental-cover-circle l dup-circle)
    k

CONTRACTION-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  UU l1
CONTRACTION-fundamental-cover-circle l dup-circle =
  ELIM-ℤ
    ( λ k →
      Id
        ( center-total-fundamental-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-fundamental-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( path-total-fundamental-cover-circle l dup-circle k))

Contraction-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  CONTRACTION-fundamental-cover-circle l dup-circle
Contraction-fundamental-cover-circle l dup-circle =
  Elim-ℤ
    ( λ k →
      Id
        ( center-total-fundamental-cover-circle l dup-circle)
        ( pair
          ( base-free-loop l)
          ( map-equiv
            ( compute-fiber-fundamental-cover-circle l dup-circle)
            ( k))))
    ( refl)
    ( λ k → equiv-concat'
      ( center-total-fundamental-cover-circle l dup-circle)
      ( path-total-fundamental-cover-circle l dup-circle k))

abstract
  is-contr-total-fundamental-cover-circle :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    is-contr (Σ X (fundamental-cover-circle l dup-circle))
  is-contr-total-fundamental-cover-circle l dup-circle =
    is-contr-total-fundamental-cover-circle-data l dup-circle
      ( pr1 (Contraction-fundamental-cover-circle l dup-circle))
      ( inv-htpy
        ( pr2 (pr2 (Contraction-fundamental-cover-circle l dup-circle))))

point-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  fundamental-cover-circle l dup-circle (base-free-loop l)
point-fundamental-cover-circle l dup-circle =
  map-equiv (compute-fiber-fundamental-cover-circle l dup-circle) zero-ℤ

fundamental-cover-circle-eq :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( x : X) → Id (base-free-loop l) x → fundamental-cover-circle l dup-circle x
fundamental-cover-circle-eq l dup-circle .(base-free-loop l) refl =
  point-fundamental-cover-circle l dup-circle

abstract
  is-equiv-fundamental-cover-circle-eq :
    { l1 : Level} {X : UU l1} (l : free-loop X) →
    ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
    ( x : X) → is-equiv (fundamental-cover-circle-eq l dup-circle x)
  is-equiv-fundamental-cover-circle-eq l dup-circle =
    fundamental-theorem-id
      ( is-contr-total-fundamental-cover-circle l dup-circle)
      ( fundamental-cover-circle-eq l dup-circle)

equiv-fundamental-cover-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( x : X) →
  ( Id (base-free-loop l) x) ≃ (fundamental-cover-circle l dup-circle x)
equiv-fundamental-cover-circle l dup-circle x =
  pair
    ( fundamental-cover-circle-eq l dup-circle x)
    ( is-equiv-fundamental-cover-circle-eq l dup-circle x)

compute-loop-space-circle :
  { l1 : Level} {X : UU l1} (l : free-loop X) →
  ( dup-circle : {l2 : Level} → dependent-universal-property-circle l2 l) →
  ( Id (base-free-loop l) (base-free-loop l)) ≃ ℤ
compute-loop-space-circle l dup-circle =
  ( inv-equiv (compute-fiber-fundamental-cover-circle l dup-circle)) ∘e
  ( equiv-fundamental-cover-circle l dup-circle (base-free-loop l))
```
