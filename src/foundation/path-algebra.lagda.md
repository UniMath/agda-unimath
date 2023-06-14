# Path algebra

```agda
module foundation.path-algebra where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-embeddings
open import foundation.binary-equivalences
open import foundation.commuting-squares-of-identifications
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

As we iterate identity type (i.e., consider the type of identifications between
two identifications), the identity types gain further structure.

Identity types of identity types are types of the form `p ＝ q`, where
`p q : x ＝ y` and `x y : A`. Using the homotopy interpretation of type theory,
elements of such a type are often called _2-paths_ and a twice iterated identity
type is often called a _type of 2-paths_.

Since 2-paths are just identifications, they have the usual operations and
coherences on paths/identifications. In the context of 2-paths, this famliar
concatination operation is called vertical concatination (see
`vertical-concat-Id²` below). However, 2-paths have novel operations and
coherences derived from the operations and coherences of the boundary 1-paths
(these are `p` and `q` in the example above). Since concatination of 1-paths is
a functor, it has an induced action on paths. We call this operation horizontal
concatination (see `horizontal-concat-Id²` below). It comes with the standard
coherences of an action on paths function, as well as coherences induced by
coherences on the boundary 1-paths.

## Properties

### the unit laws of concatination induce homotopies

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A}
  where

  htpy-left-unit : (λ (p : a0 ＝ a1) → refl {x = a0} ∙ p) ~ id
  htpy-left-unit p = left-unit

  htpy-right-unit : (λ (p : a0 ＝ a1) → p ∙ refl) ~ id
  htpy-right-unit p = right-unit
```

### squares

```agda
horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-lleft : a ＝ b) (p-lbottom : b ＝ d) (p-rbottom : d ＝ f)
  (p-middle : c ＝ d) (p-ltop : a ＝ c) (p-rtop : c ＝ e) (p-rright : e ＝ f)
  (s-left : coherence-square-identifications p-lleft p-lbottom p-ltop p-middle)
  (s-right :
    coherence-square-identifications p-middle p-rbottom p-rtop p-rright) →
  coherence-square-identifications
    p-lleft (p-lbottom ∙ p-rbottom) (p-ltop ∙ p-rtop) p-rright
horizontal-concat-square {a = a} {f = f}
  p-lleft p-lbottom p-rbottom p-middle p-ltop p-rtop p-rright s-left s-right =
  ( inv (assoc p-lleft p-lbottom p-rbottom)) ∙
  ( ( ap (concat' a p-rbottom) s-left) ∙
    ( ( assoc p-ltop p-middle p-rbottom) ∙
      ( ( ap (concat p-ltop f) s-right) ∙
        ( inv (assoc p-ltop p-rtop p-rright)))))

horizontal-unit-square :
  {l : Level} {A : UU l} {a b : A} (p : a ＝ b) →
  coherence-square-identifications p refl refl p
horizontal-unit-square p = right-unit

left-unit-law-horizontal-concat-square :
  {l : Level} {A : UU l} {a b c d : A}
  (p-left : a ＝ b) (p-bottom : b ＝ d) (p-top : a ＝ c) (p-right : c ＝ d) →
  (s : coherence-square-identifications p-left p-bottom p-top p-right) →
  ( horizontal-concat-square
    p-left refl p-bottom p-left refl p-top p-right
    ( horizontal-unit-square p-left)
    ( s)) ＝
  ( s)
left-unit-law-horizontal-concat-square refl p-bottom p-top p-right s =
  right-unit ∙ ap-id s

vertical-concat-square :
  {l : Level} {A : UU l} {a b c d e f : A}
  (p-tleft : a ＝ b) (p-bleft : b ＝ c) (p-bbottom : c ＝ f)
  (p-middle : b ＝ e) (p-ttop : a ＝ d) (p-tright : d ＝ e) (p-bright : e ＝ f)
  (s-top : coherence-square-identifications p-tleft p-middle p-ttop p-tright)
  (s-bottom :
    coherence-square-identifications p-bleft p-bbottom p-middle p-bright) →
  coherence-square-identifications
    (p-tleft ∙ p-bleft) p-bbottom p-ttop (p-tright ∙ p-bright)
vertical-concat-square {a = a} {f = f}
  p-tleft p-bleft p-bbottom p-middle p-ttop p-tright p-bright s-top s-bottom =
  ( assoc p-tleft p-bleft p-bbottom) ∙
  ( ( ap (concat p-tleft f) s-bottom) ∙
    ( ( inv (assoc p-tleft p-middle p-bright)) ∙
      ( ( ap (concat' a p-bright) s-top) ∙
        ( assoc p-ttop p-tright p-bright))))
```

### Unit laws for the associator

```agda
unit-law-assoc-011 :
  {l : Level} {X : UU l} {x y z : X} (p : x ＝ y) (q : y ＝ z) →
  assoc refl p q ＝ refl
unit-law-assoc-011 p q = refl

unit-law-assoc-101 :
  {l : Level} {X : UU l} {x y z : X} (p : x ＝ y) (q : y ＝ z) →
  assoc p refl q ＝ ap (concat' x q) right-unit
unit-law-assoc-101 refl refl = refl

unit-law-assoc-101' :
  {l : Level} {X : UU l} {x y z : X} (p : x ＝ y) (q : y ＝ z) →
  inv (assoc p refl q) ＝ ap (concat' x q) (inv right-unit)
unit-law-assoc-101' refl refl = refl

unit-law-assoc-110 :
  {l : Level} {X : UU l} {x y z : X} (p : x ＝ y) (q : y ＝ z) →
  (assoc p q refl ∙ ap (concat p z) right-unit) ＝ right-unit
unit-law-assoc-110 refl refl = refl

unit-law-assoc-110' :
  {l : Level} {X : UU l} {x y z : X} (p : x ＝ y) (q : y ＝ z) →
  (inv right-unit ∙ assoc p q refl) ＝ ap (concat p z) (inv right-unit)
unit-law-assoc-110' refl refl = refl
```

## Properties of 2-paths

### Definition of vertical and horizontal concatenation in identity types of identity types (a type of 2-paths)

```agda
vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} → p ＝ q → q ＝ r → p ＝ r
vertical-concat-Id² α β = α ∙ β

horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  p ＝ q → u ＝ v → (p ∙ u) ＝ (q ∙ v)
horizontal-concat-Id² α β = ap-binary (λ s t → s ∙ t) α β
```

### Both horizontal and vertical concatenation of 2-paths are binary equivalences

```agda
is-binary-equiv-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} →
  is-binary-equiv (vertical-concat-Id² {l} {A} {x} {y} {p} {q} {r})
is-binary-equiv-vertical-concat-Id² = is-binary-equiv-concat

is-binary-equiv-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  is-binary-equiv (horizontal-concat-Id² {l} {A} {x} {y} {z} {p} {q} {u} {v})
is-binary-equiv-horizontal-concat-Id² =
  is-binary-emb-is-binary-equiv is-binary-equiv-concat
```

### Unit laws for horizontal and vertical concatenation of 2-paths

```agda
left-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {β : p ＝ q} →
  vertical-concat-Id² refl β ＝ β
left-unit-law-vertical-concat-Id² = left-unit

right-unit-law-vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α : p ＝ q} →
  vertical-concat-Id² α refl ＝ α
right-unit-law-vertical-concat-Id² = right-unit

left-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : x ＝ y} {u v : y ＝ z} (γ : u ＝ v) →
  horizontal-concat-Id² (refl {x = p}) γ ＝ ap (concat p z) γ
left-unit-law-horizontal-concat-Id² γ = left-unit-ap-binary (λ s t → s ∙ t) γ

right-unit-law-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) {u : y ＝ z} →
  horizontal-concat-Id² α (refl {x = u}) ＝ ap (concat' x u) α
right-unit-law-horizontal-concat-Id² α = right-unit-ap-binary (λ s t → s ∙ t) α
```

Horizontal concatination satisfies an additional "2-dimensional" unit law (on
both the left and right) induced by the unit laws on the boundary 1-paths.

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A} {p p' : a0 ＝ a1} (α : p ＝ p')
  where

  nat-sq-right-unit-Id² :
    coherence-square-identifications
      right-unit α (horizontal-concat-Id² α refl) right-unit
  nat-sq-right-unit-Id² =
    ( ( horizontal-concat-Id² refl (inv (ap-id α))) ∙
      ( nat-htpy htpy-right-unit α)) ∙
    ( horizontal-concat-Id² (inv (right-unit-law-horizontal-concat-Id² α)) refl)

  nat-sq-left-unit-Id² :
    coherence-square-identifications
      left-unit α (horizontal-concat-Id² (refl {x = refl}) α) left-unit
  nat-sq-left-unit-Id² =
    ( ( (inv (ap-id α) ∙ (nat-htpy htpy-left-unit α)) ∙ right-unit) ∙
    ( inv (left-unit-law-horizontal-concat-Id² α))) ∙ inv right-unit
```

### Definition of horizontal inverse

2-paths have an induced inverse operation from the operation on boundary 1-paths

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A} {p p' : a0 ＝ a1}
  where

  horizontal-inv-Id² : p ＝ p' → (inv p) ＝ (inv p')
  horizontal-inv-Id² α = ap inv α
```

This operation satisfies a left and right idenity induced by the inverse laws on
1-paths

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A} {p p' : a0 ＝ a1} (α : p ＝ p')
  where

  nat-sq-right-inv-Id² :
    coherence-square-identifications
      ( right-inv p)
      ( refl)
      ( horizontal-concat-Id² α (horizontal-inv-Id² α))
      ( right-inv p')
  nat-sq-right-inv-Id² =
    ( ( ( horizontal-concat-Id² refl (inv (ap-const refl α))) ∙
        ( nat-htpy right-inv α)) ∙
      ( horizontal-concat-Id²
        ( ap-binary-comp-diagonal (_∙_) id inv α)
        ( refl))) ∙
    ( ap
      ( λ t → horizontal-concat-Id² t (horizontal-inv-Id² α) ∙ right-inv p')
      ( ap-id α))

  nat-sq-left-inv-Id² :
    coherence-square-identifications
      ( left-inv p)
      ( refl)
      ( horizontal-concat-Id² (horizontal-inv-Id² α) α)
      ( left-inv p')
  nat-sq-left-inv-Id² =
    ( ( ( horizontal-concat-Id² refl (inv (ap-const refl α))) ∙
        ( nat-htpy left-inv α)) ∙
      ( horizontal-concat-Id²
        ( ap-binary-comp-diagonal _∙_ inv id α)
        ( refl))) ∙
    ( ap
      ( λ t → (horizontal-concat-Id² (horizontal-inv-Id² α) t) ∙ left-inv p')
      ( ap-id α))
```

### Interchange laws for 2-paths

```agda
interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q r : x ＝ y} {u v w : y ＝ z}
  (α : p ＝ q) (β : q ＝ r) (γ : u ＝ v) (δ : v ＝ w) →
  ( horizontal-concat-Id²
    ( vertical-concat-Id² α β)
    ( vertical-concat-Id² γ δ)) ＝
  ( vertical-concat-Id²
    ( horizontal-concat-Id² α γ)
    ( horizontal-concat-Id² β δ))
interchange-Id² refl refl refl refl = refl

unit-law-α-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) (u : y ＝ z) →
  ( ( interchange-Id² α refl (refl {x = u}) refl) ∙
    ( right-unit ∙ right-unit-law-horizontal-concat-Id² α)) ＝
  ( ( right-unit-law-horizontal-concat-Id² (α ∙ refl)) ∙
    ( ap (ap (concat' x u)) right-unit))
unit-law-α-interchange-Id² refl u = refl

unit-law-β-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (β : p ＝ q) (u : y ＝ z) →
  interchange-Id² refl β (refl {x = u}) refl ＝ refl
unit-law-β-interchange-Id² refl u = refl

unit-law-γ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (γ : u ＝ v) →
  ( ( interchange-Id² (refl {x = p}) refl γ refl) ∙
    ( right-unit ∙ left-unit-law-horizontal-concat-Id² γ)) ＝
  ( ( left-unit-law-horizontal-concat-Id² (γ ∙ refl)) ∙
    ( ap (ap (concat p z)) right-unit))
unit-law-γ-interchange-Id² p refl = refl

unit-law-δ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (δ : u ＝ v) →
  interchange-Id² (refl {x = p}) refl refl δ ＝ refl
unit-law-δ-interchange-Id² p refl = refl
```

### Action on 2-paths of functors

Functions have an induced action on 2-paths

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A}
  {p p' : a0 ＝ a1} (f : A → B) (α : p ＝ p')
  where

  ap² : (ap f p) ＝ (ap f p')
  ap² = (ap (ap f)) α
```

Since this is define in terms of `ap`, it comes with the standard coherences. It
also has induced cohereces.

Inverse law.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A}
  {p p' : a0 ＝ a1} (f : A → B) (α : p ＝ p')
  where

  nat-sq-ap-inv-Id² :
    coherence-square-identifications
      ( ap-inv f p)
      ( horizontal-inv-Id² (ap² f α))
      ( ap² f (horizontal-inv-Id² α))
      ( ap-inv f p')
  nat-sq-ap-inv-Id² =
    (inv (horizontal-concat-Id² refl (ap-comp inv (ap f) α)) ∙
      (nat-htpy (ap-inv f) α)) ∙
        (horizontal-concat-Id² (ap-comp (ap f) inv α) refl)
```

Identity law and constant law.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {a0 a1 : A}
  {p p' : a0 ＝ a1} (α : p ＝ p')
  where

  nat-sq-ap-id-Id² :
    coherence-square-identifications (ap-id p) α (ap² id α) (ap-id p')
  nat-sq-ap-id-Id² =
    ((horizontal-concat-Id² refl (inv (ap-id α))) ∙ (nat-htpy ap-id α))

  nat-sq-ap-const-Id² :
    (b : B) →
    coherence-square-identifications
      ( ap-const b p)
      ( refl)
      ( ap² (const A B b) α)
      ( ap-const b p')
  nat-sq-ap-const-Id² b =
    ( inv (horizontal-concat-Id² refl (ap-const refl α))) ∙
    ( nat-htpy (ap-const b) α)
```

Composition law

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {a0 a1 : A} {p p' : a0 ＝ a1} (g : B → C) (f : A → B) (α : p ＝ p')
  where

  nat-sq-ap-comp-Id² :
    coherence-square-identifications
      ( ap-comp g f p)
      ( (ap² g ∘ ap² f) α)
      ( ap² (g ∘ f) α)
      ( ap-comp g f p')
  nat-sq-ap-comp-Id² =
    (horizontal-concat-Id² refl (inv (ap-comp (ap g) (ap f) α)) ∙
      (nat-htpy (ap-comp g f) α))
```

## Properties of 3-paths

3-paths are identifications of 2-paths. In symbols, a type of 3-paths is a type
of the form `α ＝ β` where `α β : p ＝ q` and `p q : x ＝ y`.

### Concatination in a type of 3-paths

Like with 2-paths, 3-paths have the standard operations on equalties, plus the
operations induced by the operations on 1-paths. But 3-paths also have
operations induced by those on 2-paths. Thus there are three ways to concatenate
in triple identity types. We name the three concatenations of triple identity
types x-, y-, and z-concatenation, after the standard names for the three axis
in 3-dimensional space.

The x-concatenation operation corresponds the standard concatination of
equalities.

```agda
x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  α ＝ β → β ＝ γ → α ＝ γ
x-concat-Id³ σ τ = vertical-concat-Id² σ τ
```

The y-concatenation operation corresponds the operation induced by the
concatination on 1-paths.

```agda
y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} → α ＝ β → γ ＝ δ → (α ∙ γ) ＝ (β ∙ δ)
y-concat-Id³ σ τ = horizontal-concat-Id² σ τ
```

The z-concatenation operation corresponds the concatination induced by the
horizontal concatination on 2-paths.

```agda
z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ δ : u ＝ v} →
  α ＝ β → γ ＝ δ → horizontal-concat-Id² α γ ＝ horizontal-concat-Id² β δ
z-concat-Id³ σ τ = ap-binary (λ s t → horizontal-concat-Id² s t) σ τ
```

### Unit laws for the concatenation operations on 3-paths

```agda
left-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q} {σ : α ＝ β} →
  x-concat-Id³ refl σ ＝ σ
left-unit-law-x-concat-Id³ = left-unit-law-vertical-concat-Id²

right-unit-law-x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q} {τ : α ＝ β} →
  x-concat-Id³ τ refl ＝ τ
right-unit-law-x-concat-Id³ = right-unit-law-vertical-concat-Id²

left-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α : p ＝ q} {γ δ : q ＝ r}
  {τ : γ ＝ δ} → y-concat-Id³ (refl {x = α}) τ ＝ ap (concat α r) τ
left-unit-law-y-concat-Id³ {τ = τ} = left-unit-law-horizontal-concat-Id² τ

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q} {γ : q ＝ r}
  {σ : α ＝ β} → y-concat-Id³ σ (refl {x = γ}) ＝ ap (concat' p γ) σ
right-unit-law-y-concat-Id³ {σ = σ} = right-unit-law-horizontal-concat-Id² σ

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α : p ＝ q} {γ δ : u ＝ v} (τ : γ ＝ δ) →
  z-concat-Id³ (refl {x = α}) τ ＝ ap (horizontal-concat-Id² α) τ
left-unit-law-z-concat-Id³ τ =
  left-unit-ap-binary (λ s t → horizontal-concat-Id² s t) τ

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ : u ＝ v} (σ : α ＝ β) →
  z-concat-Id³ σ (refl {x = γ}) ＝ ap (λ ω → horizontal-concat-Id² ω γ) σ
right-unit-law-z-concat-Id³ σ =
  right-unit-ap-binary (λ s t → horizontal-concat-Id² s t) σ
```

### Interchange laws for 3-paths for the concatenation operations on 3-paths

```agda
interchange-x-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β γ : p ＝ q}
  {δ ε ζ : q ＝ r} (σ : α ＝ β) (τ : β ＝ γ) (υ : δ ＝ ε) (ϕ : ε ＝ ζ) →
  ( y-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ)) ＝
  ( x-concat-Id³ (y-concat-Id³ σ υ) (y-concat-Id³ τ ϕ))
interchange-x-y-concat-Id³ = interchange-Id²

interchange-x-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β γ : p ＝ q} {δ ε ζ : u ＝ v} (σ : α ＝ β) (τ : β ＝ γ) (υ : δ ＝ ε)
  (ϕ : ε ＝ ζ) →
  ( z-concat-Id³ (x-concat-Id³ σ τ) (x-concat-Id³ υ ϕ)) ＝
  ( x-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ))
interchange-x-z-concat-Id³ refl τ refl ϕ = refl

interchange-y-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q r : x ＝ y} {u v w : y ＝ z}
  {α β : p ＝ q} {γ δ : q ＝ r} {ε ζ : u ＝ v} {η θ : v ＝ w}
  (σ : α ＝ β) (τ : γ ＝ δ) (υ : ε ＝ ζ) (ϕ : η ＝ θ) →
  ( ( z-concat-Id³ (y-concat-Id³ σ τ) (y-concat-Id³ υ ϕ)) ∙
    ( interchange-Id² β δ ζ θ)) ＝
  ( ( interchange-Id² α γ ε η) ∙
    ( y-concat-Id³ (z-concat-Id³ σ υ) (z-concat-Id³ τ ϕ)))
interchange-y-z-concat-Id³ refl refl refl refl = inv right-unit
```

## Properties of 4-paths

The pattern for concatination of 1, 2, and 3-paths continues. There are four
ways to concatenate in quadruple identity types. We name the three non-standard
concatenations in quadruple identity types `i`-, `j`-, and `k`-concatenation,
after the standard names for the quaternions `i`, `j`, and `k`.

### Concatenation of four paths

#### The standard concatination

```agda
concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q}
  {r s t : α ＝ β} → r ＝ s → s ＝ t → r ＝ t
concat-Id⁴ σ τ = x-concat-Id³ σ τ
```

#### Concatination induced by concatination of boundary 1-paths

```agda
i-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  {s s' : α ＝ β} (σ : s ＝ s') {t t' : β ＝ γ} (τ : t ＝ t') →
  x-concat-Id³ s t ＝ x-concat-Id³ s' t'
i-concat-Id⁴ σ τ = y-concat-Id³ σ τ
```

#### Concatination induced by concatination of boundary 2-paths

```agda
j-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} {s s' : α ＝ β} (σ : s ＝ s') {t t' : γ ＝ δ} (τ : t ＝ t') →
  y-concat-Id³ s t ＝ y-concat-Id³ s' t'
j-concat-Id⁴ σ τ = z-concat-Id³ σ τ
```

#### Concatination induced by concatination of boundary 3-paths

```agda
k-concat-Id⁴ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ δ : u ＝ v} {s s' : α ＝ β} (σ : s ＝ s') {t t' : γ ＝ δ}
  (τ : t ＝ t') → z-concat-Id³ s t ＝ z-concat-Id³ s' t'
k-concat-Id⁴ σ τ = ap-binary (λ m n → z-concat-Id³ m n) σ τ
```

### Commuting cubes

```agda
module _
  {l : Level} {A : UU l} {x000 x001 x010 x100 x011 x101 x110 x111 : A}
  where

  cube :
    (p000̂ : x000 ＝ x001) (p00̂0 : x000 ＝ x010) (p0̂00 : x000 ＝ x100)
    (p00̂1 : x001 ＝ x011) (p0̂01 : x001 ＝ x101) (p010̂ : x010 ＝ x011)
    (p0̂10 : x010 ＝ x110) (p100̂ : x100 ＝ x101) (p10̂0 : x100 ＝ x110)
    (p0̂11 : x011 ＝ x111) (p10̂1 : x101 ＝ x111) (p110̂ : x110 ＝ x111)
    (p00̂0̂ : coherence-square-identifications p000̂ p00̂1 p00̂0 p010̂)
    (p0̂00̂ : coherence-square-identifications p000̂ p0̂01 p0̂00 p100̂)
    (p0̂0̂0 : coherence-square-identifications p00̂0 p0̂10 p0̂00 p10̂0)
    (p0̂0̂1 : coherence-square-identifications p00̂1 p0̂11 p0̂01 p10̂1)
    (p0̂10̂ : coherence-square-identifications p010̂ p0̂11 p0̂10 p110̂)
    (p10̂0̂ : coherence-square-identifications p100̂ p10̂1 p10̂0 p110̂) → UU l
  cube
    p000̂ p00̂0 p0̂00 p00̂1 p0̂01 p010̂ p0̂10 p100̂ p10̂0 p0̂11 p10̂1 p110̂
    p00̂0̂ p0̂00̂ p0̂0̂0 p0̂0̂1 p0̂10̂ p10̂0̂ =
    Id
      ( ( ap (concat' x000 p0̂11) p00̂0̂) ∙
        ( ( assoc p00̂0 p010̂ p0̂11) ∙
          ( ( ap (concat p00̂0 x111) p0̂10̂) ∙
            ( ( inv (assoc p00̂0 p0̂10 p110̂)) ∙
              ( ( ap (concat' x000 p110̂) p0̂0̂0) ∙
                ( assoc p0̂00 p10̂0 p110̂))))))
      ( ( assoc p000̂ p00̂1 p0̂11) ∙
        ( ( ap (concat p000̂ x111) p0̂0̂1) ∙
          ( ( inv (assoc p000̂ p0̂01 p10̂1)) ∙
            ( ( ap (concat' x000 p10̂1) p0̂00̂) ∙
              ( ( assoc p0̂00 p100̂ p10̂1) ∙
                ( ( ap (concat p0̂00 x111) p10̂0̂)))))))
```
