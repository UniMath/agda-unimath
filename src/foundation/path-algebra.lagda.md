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
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-identifications
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.whiskering-identifications-concatenation
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
coherences on paths/identifications. In the context of 2-paths, this familiar
concatenation operation is called vertical concatenation (see
`vertical-concat-Id²` below). However, 2-paths have novel operations and
coherences derived from the operations and coherences of the boundary 1-paths
(these are `p` and `q` in the example above). Since concatenation of 1-paths is
a functor, it has an induced action on paths. We call this operation horizontal
concatenation (see `horizontal-concat-Id²` below). It comes with the standard
coherences of an action on paths function, as well as coherences induced by
coherences on the boundary 1-paths.

## Properties

### The unit laws of concatenation induce homotopies

```agda
module _
  {l : Level} {A : UU l} {a0 a1 : A}
  where

  htpy-left-unit : (λ (p : a0 ＝ a1) → refl {x = a0} ∙ p) ~ id
  htpy-left-unit p = left-unit

  htpy-right-unit : (λ (p : a0 ＝ a1) → p ∙ refl) ~ id
  htpy-right-unit p = right-unit
```

### Unit laws for `assoc`

We give two treatments of the unit laws for the associator. One for computing
with the associator, and one for coherences between the unit laws.

#### Computing `assoc` at a reflexivity

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  left-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc refl p q ＝ refl
  left-unit-law-assoc p q = refl

  middle-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p refl q ＝ right-whisker-concat right-unit q
  middle-unit-law-assoc refl q = refl

  right-unit-law-assoc :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p q refl ＝
      right-unit ∙ left-whisker-concat p (inv right-unit)
  right-unit-law-assoc refl refl = refl
```

#### Unit laws for `assoc` and their coherence

We use a binary naming scheme for the (higher) unit laws of the associator. For
each 3-digit binary number except when all digits are `1`, there is a
corresponding unit law. A `0` reflects that the unit of the operator is present
in the corresponding position. More generally, there is for each `n`-digit
binary number (except all `1`s) a unit law for the `n`-ary coherence operator.

```agda
module _
  {l : Level} {A : UU l} {x y z : A}
  where

  unit-law-assoc-011 :
    (p : x ＝ y) (q : y ＝ z) →
    assoc refl p q ＝ refl
  unit-law-assoc-011 p q = refl

  unit-law-assoc-101 :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p refl q ＝ right-whisker-concat right-unit q
  unit-law-assoc-101 refl q = refl

  unit-law-assoc-101' :
    (p : x ＝ y) (q : y ＝ z) →
    inv (assoc p refl q) ＝ right-whisker-concat (inv right-unit) q
  unit-law-assoc-101' refl q = refl

  unit-law-assoc-110 :
    (p : x ＝ y) (q : y ＝ z) →
    assoc p q refl ∙ left-whisker-concat p right-unit ＝ right-unit
  unit-law-assoc-110 refl refl = refl

  unit-law-assoc-110' :
    (p : x ＝ y) (q : y ＝ z) →
    inv right-unit ∙ assoc p q refl ＝
    left-whisker-concat p (inv right-unit)
  unit-law-assoc-110' refl refl = refl
```

### Second-order associators

```agda
module _
  {l : Level} {A : UU l} {x y z u v : A}
  (p : x ＝ y) (q : y ＝ z) (r : z ＝ u) (s : u ＝ v)
  where

  assoc²-1 : ((p ∙ q) ∙ r) ∙ s ＝ p ∙ ((q ∙ r) ∙ s)
  assoc²-1 = ap (_∙ s) (assoc p q r) ∙ assoc p (q ∙ r) s

  assoc²-2 : (p ∙ (q ∙ r)) ∙ s ＝ p ∙ (q ∙ (r ∙ s))
  assoc²-2 = assoc p (q ∙ r) s ∙ ap (p ∙_) (assoc q r s)

  assoc²-3 : ((p ∙ q) ∙ r) ∙ s ＝ p ∙ (q ∙ (r ∙ s))
  assoc²-3 = assoc (p ∙ q) r s ∙ assoc p q (r ∙ s)

  assoc²-4 : (p ∙ q) ∙ (r ∙ s) ＝ p ∙ ((q ∙ r) ∙ s)
  assoc²-4 = assoc p q (r ∙ s) ∙ ap (p ∙_) (inv (assoc q r s))

  assoc²-5 : (p ∙ q) ∙ (r ∙ s) ＝ (p ∙ (q ∙ r)) ∙ s
  assoc²-5 = inv (assoc (p ∙ q) r s) ∙ ap (_∙ s) (assoc p q r)
```

## Properties of 2-paths

### Definition of vertical and horizontal concatenation in identity types of identity types (a type of 2-paths)

```agda
vertical-concat-Id² :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} → p ＝ q → q ＝ r → p ＝ r
vertical-concat-Id² α β = α ∙ β

horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z} →
  p ＝ q → u ＝ v → p ∙ u ＝ q ∙ v
horizontal-concat-Id² α β = ap-binary (_∙_) α β
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

compute-left-refl-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p : x ＝ y} {u v : y ＝ z} (γ : u ＝ v) →
  horizontal-concat-Id² refl γ ＝ left-whisker-concat p γ
compute-left-refl-horizontal-concat-Id² = left-unit-ap-binary (_∙_)

compute-right-refl-horizontal-concat-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) {u : y ＝ z} →
  horizontal-concat-Id² α refl ＝ right-whisker-concat α u
compute-right-refl-horizontal-concat-Id² = right-unit-ap-binary (_∙_)
```

Horizontal concatenation satisfies an additional "2-dimensional" unit law (on
both the left and right) induced by the unit laws on the boundary 1-paths.

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y} (α : p ＝ p')
  where

  nat-sq-right-unit-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² α refl)
      ( right-unit)
      ( right-unit)
      ( α)
  nat-sq-right-unit-Id² =
    ( ( horizontal-concat-Id² refl (inv (ap-id α))) ∙
      ( nat-htpy htpy-right-unit α)) ∙
    ( horizontal-concat-Id²
      ( inv (compute-right-refl-horizontal-concat-Id² α))
      ( refl))

  nat-sq-left-unit-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² refl α)
      ( left-unit)
      ( left-unit)
      ( α)
  nat-sq-left-unit-Id² =
    ( ( (inv (ap-id α) ∙ (nat-htpy htpy-left-unit α)) ∙ right-unit) ∙
      ( inv (compute-left-refl-horizontal-concat-Id² α))) ∙
    ( inv right-unit)
```

### Vertical inverses distribute over horizontal concatenation

```agda
module _
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  where

  distributive-inv-horizontal-concat-Id² :
    (α : p ＝ q) (β : u ＝ v) →
    inv (horizontal-concat-Id² α β) ＝ horizontal-concat-Id² (inv α) (inv β)
  distributive-inv-horizontal-concat-Id² refl refl =
    refl
```

### Definition of horizontal inverse

2-paths have an induced inverse operation from the operation on boundary 1-paths

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y}
  where

  horizontal-inv-Id² : p ＝ p' → inv p ＝ inv p'
  horizontal-inv-Id² = ap inv
```

This operation satisfies a left and right identity induced by the inverse laws
on 1-paths

```agda
module _
  {l : Level} {A : UU l} {x y : A} {p p' : x ＝ y} (α : p ＝ p')
  where

  nat-sq-right-inv-Id² :
    coherence-square-identifications
      ( horizontal-concat-Id² α (horizontal-inv-Id² α))
      ( right-inv p)
      ( right-inv p')
      ( refl)
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
      ( horizontal-concat-Id² (horizontal-inv-Id² α) α)
      ( left-inv p)
      ( left-inv p')
      ( refl)
  nat-sq-left-inv-Id² =
    ( ( ( horizontal-concat-Id² refl (inv (ap-const refl α))) ∙
        ( nat-htpy left-inv α)) ∙
      ( horizontal-concat-Id²
        ( ap-binary-comp-diagonal (_∙_) inv id α)
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
interchange-Id² refl _ refl _ = refl

inner-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p r : x ＝ y} {u v : y ＝ z}
  (β : p ＝ r) (γ : u ＝ v) →
  ( horizontal-concat-Id² β γ) ＝
  ( vertical-concat-Id² (left-whisker-concat p γ) (right-whisker-concat β v))
inner-interchange-Id² {u = refl} β refl =
  compute-right-refl-horizontal-concat-Id² β

outer-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u w : y ＝ z}
  (α : p ＝ q) (δ : u ＝ w) →
  ( horizontal-concat-Id² α δ) ＝
  ( vertical-concat-Id² (right-whisker-concat α u) (left-whisker-concat q δ))
outer-interchange-Id² {p = refl} refl δ =
  compute-left-refl-horizontal-concat-Id² δ

unit-law-α-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (α : p ＝ q) (u : y ＝ z) →
  ( ( interchange-Id² α refl (refl {x = u}) refl) ∙
    ( right-unit ∙ compute-right-refl-horizontal-concat-Id² α)) ＝
  ( ( compute-right-refl-horizontal-concat-Id² (α ∙ refl)) ∙
    ( ap (λ s → right-whisker-concat s u) right-unit))
unit-law-α-interchange-Id² refl _ = refl

unit-law-β-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} (β : p ＝ q) (u : y ＝ z) →
  interchange-Id² refl β (refl {x = u}) refl ＝ refl
unit-law-β-interchange-Id² refl _ = refl

unit-law-γ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (γ : u ＝ v) →
  ( ( interchange-Id² (refl {x = p}) refl γ refl) ∙
    ( right-unit ∙ compute-left-refl-horizontal-concat-Id² γ)) ＝
  ( ( compute-left-refl-horizontal-concat-Id² (γ ∙ refl)) ∙
    ( ap (left-whisker-concat p) right-unit))
unit-law-γ-interchange-Id² _ refl = refl

unit-law-δ-interchange-Id² :
  {l : Level} {A : UU l} {x y z : A} (p : x ＝ y) {u v : y ＝ z} (δ : u ＝ v) →
  interchange-Id² (refl {x = p}) refl refl δ ＝ refl
unit-law-δ-interchange-Id² _ refl = refl
```

## Properties of 3-paths

3-paths are identifications of 2-paths. In symbols, a type of 3-paths is a type
of the form `α ＝ β` where `α β : p ＝ q` and `p q : x ＝ y`.

### Concatenation in a type of 3-paths

Like with 2-paths, 3-paths have the standard operations on equalties, plus the
operations induced by the operations on 1-paths. But 3-paths also have
operations induced by those on 2-paths. Thus there are three ways to concatenate
in triple identity types. We name the three concatenations of triple identity
types x-, y-, and z-concatenation, after the standard names for the three axis
in 3-dimensional space.

The x-concatenation operation corresponds the standard concatenation of
equalities.

```agda
x-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  α ＝ β → β ＝ γ → α ＝ γ
x-concat-Id³ σ τ = vertical-concat-Id² σ τ
```

The y-concatenation operation corresponds the operation induced by the
concatenation on 1-paths.

```agda
y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} → α ＝ β → γ ＝ δ → (α ∙ γ) ＝ (β ∙ δ)
y-concat-Id³ = horizontal-concat-Id²
```

The z-concatenation operation corresponds the concatenation induced by the
horizontal concatenation on 2-paths.

```agda
z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ δ : u ＝ v} →
  α ＝ β → γ ＝ δ → horizontal-concat-Id² α γ ＝ horizontal-concat-Id² β δ
z-concat-Id³ σ τ = ap-binary horizontal-concat-Id² σ τ
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
  {τ : γ ＝ δ} →
  y-concat-Id³ (refl {x = α}) τ ＝ left-whisker-concat α τ
left-unit-law-y-concat-Id³ {τ = τ} = compute-left-refl-horizontal-concat-Id² τ

right-unit-law-y-concat-Id³ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q} {γ : q ＝ r}
  {σ : α ＝ β} →
  y-concat-Id³ σ (refl {x = γ}) ＝ right-whisker-concat σ γ
right-unit-law-y-concat-Id³ {σ = σ} = compute-right-refl-horizontal-concat-Id² σ

left-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α : p ＝ q} {γ δ : u ＝ v} (τ : γ ＝ δ) →
  z-concat-Id³ (refl {x = α}) τ ＝ ap (horizontal-concat-Id² α) τ
left-unit-law-z-concat-Id³ {α = α} =
  left-unit-ap-binary horizontal-concat-Id² {α}

right-unit-law-z-concat-Id³ :
  {l : Level} {A : UU l} {x y z : A} {p q : x ＝ y} {u v : y ＝ z}
  {α β : p ＝ q} {γ : u ＝ v} (σ : α ＝ β) →
  z-concat-Id³ σ (refl {x = γ}) ＝ ap (λ ω → horizontal-concat-Id² ω γ) σ
right-unit-law-z-concat-Id³ σ =
  right-unit-ap-binary horizontal-concat-Id² σ
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

The pattern for concatenation of 1, 2, and 3-paths continues. There are four
ways to concatenate in quadruple identity types. We name the three nonstandard
concatenations in quadruple identity types `i`-, `j`-, and `k`-concatenation,
after the standard names for the quaternions `i`, `j`, and `k`.

### Concatenation of four paths

#### The standard concatenation

```agda
concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β : p ＝ q}
  {r s t : α ＝ β} → r ＝ s → s ＝ t → r ＝ t
concat-Id⁴ σ τ = x-concat-Id³ σ τ
```

#### Concatenation induced by concatenation of boundary 1-paths

```agda
i-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q : x ＝ y} {α β γ : p ＝ q} →
  {s s' : α ＝ β} (σ : s ＝ s') {t t' : β ＝ γ} (τ : t ＝ t') →
  x-concat-Id³ s t ＝ x-concat-Id³ s' t'
i-concat-Id⁴ σ τ = y-concat-Id³ σ τ
```

#### Concatenation induced by concatenation of boundary 2-paths

```agda
j-concat-Id⁴ :
  {l : Level} {A : UU l} {x y : A} {p q r : x ＝ y} {α β : p ＝ q}
  {γ δ : q ＝ r} {s s' : α ＝ β} (σ : s ＝ s') {t t' : γ ＝ δ} (τ : t ＝ t') →
  y-concat-Id³ s t ＝ y-concat-Id³ s' t'
j-concat-Id⁴ σ τ = z-concat-Id³ σ τ
```

#### Concatenation induced by concatenation of boundary 3-paths

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

  coherence-cube-identifications :
    (p000̂ : x000 ＝ x001) (p00̂0 : x000 ＝ x010) (p0̂00 : x000 ＝ x100)
    (p00̂1 : x001 ＝ x011) (p0̂01 : x001 ＝ x101) (p010̂ : x010 ＝ x011)
    (p0̂10 : x010 ＝ x110) (p100̂ : x100 ＝ x101) (p10̂0 : x100 ＝ x110)
    (p0̂11 : x011 ＝ x111) (p10̂1 : x101 ＝ x111) (p110̂ : x110 ＝ x111)
    (p00̂0̂ : coherence-square-identifications p00̂0 p000̂ p010̂ p00̂1)
    (p0̂00̂ : coherence-square-identifications p0̂00 p000̂ p100̂ p0̂01)
    (p0̂0̂0 : coherence-square-identifications p0̂00 p00̂0 p10̂0 p0̂10)
    (p0̂0̂1 : coherence-square-identifications p0̂01 p00̂1 p10̂1 p0̂11)
    (p0̂10̂ : coherence-square-identifications p0̂10 p010̂ p110̂ p0̂11)
    (p10̂0̂ : coherence-square-identifications p10̂0 p100̂ p110̂ p10̂1) → UU l
  coherence-cube-identifications
    p000̂ p00̂0 p0̂00 p00̂1 p0̂01 p010̂ p0̂10 p100̂ p10̂0 p0̂11 p10̂1 p110̂
    p00̂0̂ p0̂00̂ p0̂0̂0 p0̂0̂1 p0̂10̂ p10̂0̂ =
    Id
      ( ( right-whisker-concat p00̂0̂ p0̂11) ∙
        ( ( assoc p00̂0 p010̂ p0̂11) ∙
          ( ( left-whisker-concat p00̂0 p0̂10̂) ∙
            ( ( inv (assoc p00̂0 p0̂10 p110̂)) ∙
              ( ( right-whisker-concat p0̂0̂0 p110̂) ∙
                ( assoc p0̂00 p10̂0 p110̂))))))
      ( ( assoc p000̂ p00̂1 p0̂11) ∙
        ( ( left-whisker-concat p000̂ p0̂0̂1) ∙
          ( ( inv (assoc p000̂ p0̂01 p10̂1)) ∙
            ( ( right-whisker-concat p0̂00̂ p10̂1) ∙
              ( ( assoc p0̂00 p100̂ p10̂1) ∙
                ( ( left-whisker-concat p0̂00 p10̂0̂)))))))
```
