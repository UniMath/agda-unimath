# Transport along higher identifications

```agda
module foundation.transport-along-higher-identifications where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.function-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
open import foundation-core.whiskering-homotopies-concatenation
```

</details>

### The action on identifications of transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  where

  tr² : (B : A → UU l2) (α : p ＝ p') (b : B x) → (tr B p b) ＝ (tr B p' b)
  tr² B α b = ap (λ t → tr B t b) α

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'}
  where

  tr³ : (B : A → UU l2) (β : α ＝ α') (b : B x) → (tr² B α b) ＝ (tr² B α' b)
  tr³ B β b = ap (λ t → tr² B t b) β

module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y}
  {α α' : p ＝ p'} {γ γ' : α ＝ α'}
  where

  tr⁴ : (B : A → UU l2) (ψ : γ ＝ γ') → (tr³ B γ) ~ (tr³ B γ')
  tr⁴ B ψ b = ap (λ t → tr³ B t b) ψ
```

### Computing 2-dimensional transport in a family of identifications with a fixed source

```agda
module _
  {l : Level} {A : UU l} {a b c : A} {q q' : b ＝ c}
  where

  tr²-Id-right :
    (α : q ＝ q') (p : a ＝ b) →
    coherence-square-identifications
      ( tr-Id-right q p)
      ( tr² (Id a) α p)
      ( left-whisker-concat p α)
      ( tr-Id-right q' p)
  tr²-Id-right α p =
    inv-nat-htpy (λ (t : b ＝ c) → tr-Id-right t p) α
```

### Coherences and algebraic identities for `tr²`

#### Computing `tr²` along the concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-concat :
    {p p' p'' : x ＝ y} (α : p ＝ p') (β : p' ＝ p'') →
    tr² B (α ∙ β) ~ tr² B α ∙h tr² B β
  tr²-concat α β b = ap-concat (λ t → tr B t b) α β
```

#### Computing `tr²` along the inverse of an identification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-inv :
    {p p' : x ＝ y} (α : p ＝ p') →
    tr² B (inv α) ~ inv-htpy (tr² B α)
  tr²-inv α b = ap-inv (λ t → tr B t b) α

  left-inverse-law-tr² :
    {p p' : x ＝ y} (α : p ＝ p') →
    tr² B (inv α) ∙h tr² B α ~ refl-htpy
  left-inverse-law-tr² α =
    ( right-whisker-concat-htpy (tr²-inv α) (tr² B α)) ∙h
    ( left-inv-htpy (tr² B α))

  right-inverse-law-tr² :
    {p p' : x ＝ y} (α : p ＝ p') →
    tr² B α ∙h tr² B (inv α) ~ refl-htpy
  right-inverse-law-tr² α =
    ( left-whisker-concat-htpy (tr² B α) (tr²-inv α)) ∙h
    ( right-inv-htpy (tr² B α))
```

#### Computing `tr²` along the unit laws for vertical concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr²-left-unit :
    (p : x ＝ y) → tr² B left-unit ~ tr-concat refl p
  tr²-left-unit p = refl-htpy

  tr²-right-unit :
    (p : x ＝ y) → tr² B right-unit ~ tr-concat p refl
  tr²-right-unit refl = refl-htpy
```

#### Computing `tr²` along the whiskering of identification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-left-whisker :
    (p : x ＝ y) {q q' : y ＝ z} (β : q ＝ q') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (left-whisker-concat p β))
      ( tr² B β ·r tr B p)
      ( tr-concat p q')
  tr²-left-whisker refl refl = refl-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr²-right-whisker :
    {p p' : x ＝ y} (α : p ＝ p') (q : y ＝ z) →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (right-whisker-concat α q))
      ( ( tr B q) ·l (tr² B α))
      ( tr-concat p' q)
  tr²-right-whisker refl refl = inv-htpy right-unit-htpy
```

### Coherences and algebraic identities for `tr³`

#### Computing `tr³` along the concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  {x y : A} {p p' : x ＝ y} {α α' α'' : p ＝ p'}
  where

  tr³-concat :
    (γ : α ＝ α') (δ : α' ＝ α'') → tr³ B (γ ∙ δ) ~ (tr³ B γ) ∙h (tr³ B δ)
  tr³-concat γ δ b = ap-concat (λ t → tr² B t b) γ δ
```

#### Computing `tr³` along the horizontal concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' p'' : x ＝ y}
  {α α' : p ＝ p'} {β β' : p' ＝ p''} {B : A → UU l2}
  where

  tr³-horizontal-concat :
    (γ : α ＝ α') (δ : β ＝ β') →
    coherence-square-homotopies
      ( tr²-concat α β)
      ( tr³ B (horizontal-concat-Id² γ δ))
      ( horizontal-concat-htpy² (tr³ B γ) (tr³ B δ))
      ( tr²-concat α' β')
  tr³-horizontal-concat refl refl = inv-htpy right-unit-htpy
```

#### Computing `tr³` along the inverse of an identification

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p p' : x ＝ y} {α α' : p ＝ p'}
  {B : A → UU l2}
  where

  tr³-inv :
    (γ : α ＝ α') →
    tr³ B (inv γ) ~ inv-htpy (tr³ B γ)
  tr³-inv γ b = ap-inv (λ t → tr² B t b) γ

  left-inv-law-tr³ :
    (γ : α ＝ α') →
    tr³ B (inv γ) ∙h tr³ B γ ~ refl-htpy
  left-inv-law-tr³ γ =
    ( right-whisker-concat-htpy (tr³-inv γ) (tr³ B γ)) ∙h
    ( left-inv-htpy (tr³ B γ))

  right-inv-law-tr³ :
    (γ : α ＝ α') →
    tr³ B γ ∙h tr³ B (inv γ) ~ refl-htpy
  right-inv-law-tr³ γ =
    ( left-whisker-concat-htpy (tr³ B γ) (tr³-inv γ)) ∙h
    ( right-inv-htpy (tr³ B γ))
```

#### Computing `tr³` along the unit laws for vertical concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A} {p q : x ＝ y}
  {B : A → UU l2}
  where

  tr³-right-unit :
    (α : p ＝ q) →
    tr³ B (right-unit {p = α}) ~ tr²-concat α refl ∙h right-unit-htpy
  tr³-right-unit refl = refl-htpy

  tr³-left-unit :
    (α : p ＝ q) →
    tr³ B (left-unit {p = α}) ~ tr²-concat refl α ∙h left-unit-htpy
  tr³-left-unit α = refl-htpy
```

#### Computing tr³ along the unit laws for whiskering of identifications

These coherences take the form of the following commutative diagrams. Note that
there is an asymmetry between the left and right coherence laws due to the
asymmetry in the definition of concatenation of identifications.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr³-left-unit-law-left-whisker-concat :
    {q q' : x ＝ y} (β : q ＝ q') →
    coherence-square-homotopies
      ( inv-htpy right-unit-htpy)
      ( refl-htpy)
      ( tr²-left-whisker refl β)
      ( tr³ B (left-unit-law-left-whisker-concat β))
  tr³-left-unit-law-left-whisker-concat refl = refl-htpy
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y : A}
  {B : A → UU l2}
  where

  tr³-right-unit-law-right-whisker-concat :
    {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-homotopies
      ( ( tr²-concat (right-whisker-concat α refl) right-unit) ∙h
        ( left-whisker-concat-htpy
          ( tr² B (right-whisker-concat α refl))
          ( tr²-right-unit p')))
      ( tr³ B (inv (right-unit-law-right-whisker-concat α)))
      ( tr²-right-whisker α refl)
      ( ( tr²-concat right-unit α) ∙h
        ( right-whisker-concat-htpy (tr²-right-unit p) (tr² B α)) ∙h
        ( inv-htpy
          ( left-whisker-concat-htpy
            ( tr-concat p refl)
            ( left-unit-law-left-whisker-comp (tr² B α)))))
  tr³-right-unit-law-right-whisker-concat {p = refl} {p' = refl} refl =
    refl-htpy
```

The above coherences have simplified forms when we consider 2-loops

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x : A}
  {B : A → UU l2}
  where

  tr³-left-unit-law-left-whisker-concat-Ω² :
    (β : refl {x = x} ＝ refl) →
    coherence-square-homotopies
      ( inv-htpy right-unit-htpy)
      ( refl-htpy)
      ( tr²-left-whisker refl β)
      ( tr³ B (left-unit-law-left-whisker-concat β))
  tr³-left-unit-law-left-whisker-concat-Ω² β =
    tr³-left-unit-law-left-whisker-concat β

  tr³-right-unit-law-right-whisker-concat-Ω² :
    (α : refl {x = x} ＝ refl) →
    coherence-square-homotopies
      ( inv-htpy right-unit-htpy)
      ( tr³ B (inv (right-unit-law-right-whisker-concat α ∙ right-unit)))
      ( tr²-right-whisker α refl)
      ( inv-htpy (left-unit-law-left-whisker-comp (tr² B α)))
  tr³-right-unit-law-right-whisker-concat-Ω² α =
    concat-top-homotopy-coherence-square-homotopies
      ( ( tr³ B (inv right-unit)) ∙h
        ( tr²-concat (right-whisker-concat α refl) refl))
      ( tr³
        ( B)
        ( inv (right-unit-law-right-whisker-concat α ∙ right-unit)))
      ( tr²-right-whisker α refl)
      ( inv-htpy (left-unit-law-left-whisker-comp (tr² B α)))
      ( ( right-whisker-concat-htpy
          ( tr³-inv right-unit)
          ( tr²-concat (right-whisker-concat α refl) refl)) ∙h
        ( inv-htpy
          ( left-transpose-htpy-concat
            ( tr³ B right-unit)
            ( inv-htpy right-unit-htpy)
            ( tr²-concat (right-whisker-concat α refl) refl)
            ( inv-htpy
              ( right-transpose-htpy-concat
                ( tr²-concat (right-whisker-concat α refl) refl)
                ( right-unit-htpy)
                ( tr³ B right-unit)
                ( inv-htpy
                  ( tr³-right-unit (right-whisker-concat α refl))))))))
      ( concat-left-homotopy-coherence-square-homotopies
        ( ( tr³ B (inv right-unit)) ∙h
          ( tr²-concat (right-whisker-concat α refl) refl))
        ( ( tr³ B (inv right-unit)) ∙h
          ( tr³ B (inv (right-unit-law-right-whisker-concat α))))
        ( tr²-right-whisker α refl)
        ( inv-htpy (left-unit-law-left-whisker-comp (tr² B α)))
        ( ( inv-htpy
            ( tr³-concat
              ( inv right-unit)
              ( inv (right-unit-law-right-whisker-concat α)))) ∙h
          ( tr⁴
            ( B)
            ( inv
              ( distributive-inv-concat
                ( right-unit-law-right-whisker-concat α) (right-unit)))))
        ( left-whisker-concat-coherence-square-homotopies
          ( tr³ B (inv right-unit))
          ( tr²-concat (right-whisker-concat α refl) refl)
          ( tr³ B (inv (right-unit-law-right-whisker-concat α)))
          ( tr²-right-whisker α refl)
          ( inv-htpy (left-unit-law-left-whisker-comp (tr² B α)))
          ( concat-bottom-homotopy-coherence-square-homotopies
            ( tr²-concat (right-whisker-concat α refl) refl)
            ( tr³ B (inv (right-unit-law-right-whisker-concat α)))
            ( tr²-right-whisker α refl)
            ( inv-htpy
              ( left-whisker-concat-htpy
                ( refl-htpy)
                ( left-unit-law-left-whisker-comp (tr² B α))))
            ( ap-inv-htpy
              ( left-unit-law-left-whisker-concat-htpy
                ( left-unit-law-left-whisker-comp (tr² B α))))
            ( concat-top-homotopy-coherence-square-homotopies
              ( ( tr²-concat (right-whisker-concat α refl) refl) ∙h
                ( refl-htpy))
              ( tr³ B (inv (right-unit-law-right-whisker-concat α)))
              ( tr²-right-whisker α refl)
              ( inv-htpy
                ( left-whisker-concat-htpy
                  ( refl-htpy)
                  ( left-unit-law-left-whisker-comp (tr² B α))))
              ( right-unit-htpy)
              ( tr³-right-unit-law-right-whisker-concat α)))))
```

#### Computing `tr³` along `commutative-left-whisker-right-whisker-concat`

This coherence naturally takes the form of a filler for a cube whose left face
is

```text
tr³ B (commutative-left-whisker-right-whisker-concat β α)
```

and whose right face is

```text
commutative-right-whisker-left-whisker-htpy (tr² B β) (tr² B α)
```

However, this cube has trivial front and back faces. Thus, we only prove a
simplified form of the coherence.

##### Non-trivial faces of the cube

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2} {p p' : x ＝ y} {q q' : y ＝ z}
  where

  tr²-left-whisker-concat-tr²-right-whisker-concat :
    (β : q ＝ q') (α : p ＝ p') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( ( tr² B (left-whisker-concat p β)) ∙h
        ( tr² B (right-whisker-concat α q')))
      ( (tr² B β ·r tr B p) ∙h (tr B q' ·l tr² B α))
      ( tr-concat p' q')
  tr²-left-whisker-concat-tr²-right-whisker-concat β α =
    ( vertical-pasting-coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (left-whisker-concat p β))
      ( right-whisker-comp (tr² B β) (tr B p))
      ( tr-concat p q')
      ( tr² B (right-whisker-concat α q'))
      ( left-whisker-comp (tr B q') (tr² B α))
      ( tr-concat p' q')
      ( tr²-left-whisker p β)
      ( tr²-right-whisker α q'))

  tr²-concat-left-whisker-concat-right-whisker-concat :
    (β : q ＝ q') (α : p ＝ p') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (left-whisker-concat p β ∙ right-whisker-concat α q'))
      ( (tr² B β ·r tr B p) ∙h (tr B q' ·l tr² B α))
      ( tr-concat p' q')
  tr²-concat-left-whisker-concat-right-whisker-concat β α =
    ( right-whisker-concat-htpy
      ( tr²-concat
        ( left-whisker-concat p β)
        ( right-whisker-concat α q'))
      ( tr-concat p' q')) ∙h
    ( tr²-left-whisker-concat-tr²-right-whisker-concat β α)

  tr²-right-whisker-concat-tr²-left-whisker-concat :
    (α : p ＝ p') (β : q ＝ q') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( ( tr² B (right-whisker-concat α q)) ∙h
        ( tr² B (left-whisker-concat p' β)))
      ( (tr B q ·l tr² B α) ∙h (tr² B β ·r tr B p'))
      ( tr-concat p' q')
  tr²-right-whisker-concat-tr²-left-whisker-concat α β =
    ( vertical-pasting-coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (right-whisker-concat α q))
      ( left-whisker-comp (tr B q) (tr² B α))
      ( tr-concat p' q)
      ( tr² B (left-whisker-concat p' β))
      ( right-whisker-comp (tr² B β) (tr B p'))
      ( tr-concat p' q')
      ( tr²-right-whisker α q)
      ( tr²-left-whisker p' β))

  tr²-concat-right-whisker-concat-left-whisker-concat :
    (α : p ＝ p') (β : q ＝ q') →
    coherence-square-homotopies
      ( tr-concat p q)
      ( tr² B (right-whisker-concat α q ∙ left-whisker-concat p' β))
      ( ( tr B q ·l tr² B α) ∙h (tr² B β ·r tr B p'))
      ( tr-concat p' q')
  tr²-concat-right-whisker-concat-left-whisker-concat α β =
    ( right-whisker-concat-htpy
      ( tr²-concat
        ( right-whisker-concat α q)
        ( left-whisker-concat p' β))
      ( tr-concat p' q')) ∙h
    ( tr²-right-whisker-concat-tr²-left-whisker-concat α β)
```

##### The coherence itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} {x y z : A}
  {B : A → UU l2}
  where

  tr³-commutative-left-whisker-right-whisker-concat :
    {q q' : y ＝ z} (β : q ＝ q') {p p' : x ＝ y} (α : p ＝ p') →
    coherence-square-homotopies
      ( tr²-concat-left-whisker-concat-right-whisker-concat β α)
      ( right-whisker-concat-htpy
        ( tr³
          ( B)
          ( commutative-left-whisker-right-whisker-concat β α))
        ( tr-concat p' q'))
      ( left-whisker-concat-htpy
        ( tr-concat p q)
        ( commutative-right-whisker-left-whisker-htpy
          ( tr² B β)
          ( tr² B α)))
      ( tr²-concat-right-whisker-concat-left-whisker-concat α β)
  tr³-commutative-left-whisker-right-whisker-concat
    {q = refl} refl {p = refl} refl =
    refl-htpy
```

##### A simplification of the non-trivial faces of the cube when `α` and `β` are 2-loops

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A}
  {B : A → UU l2}
  where

  tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( ( tr² B (left-whisker-concat refl α)) ∙h
      ( tr² B (right-whisker-concat β refl))) ~
    ( tr² B α ∙h (id ·l (tr² B β)))
  tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β =
    horizontal-concat-htpy²
      ( tr³ B (left-unit-law-left-whisker-concat α))
      ( ( tr³
          ( B)
          ( inv (right-unit-law-right-whisker-concat β ∙ right-unit))) ∙h
        ( inv-htpy (left-unit-law-left-whisker-comp (tr² B β))))

  compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( inv-coherence-square-homotopies-horizontal-refl
      ( ( tr² B (left-whisker-concat refl α)) ∙h
        ( tr² B (right-whisker-concat β refl)))
      ( tr² B α ∙h id ·l (tr² B β))
      ( tr²-left-whisker-concat-tr²-right-whisker-concat α β)) ~
    ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β)
  compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β =
    ( vertical-pasting-inv-coherence-square-homotopies-horizontal-refl
      ( tr² B (left-whisker-concat refl α))
      ( tr² B α)
      ( tr² B (right-whisker-concat β refl))
      ( id ·l (tr² B β))
      ( tr²-left-whisker refl α)
      ( tr²-right-whisker β refl)) ∙h
    ( z-concat-htpy³
      ( inv-htpy (tr³-left-unit-law-left-whisker-concat-Ω² α))
      ( inv-htpy (tr³-right-unit-law-right-whisker-concat-Ω² β)))

  tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( ( tr² B (right-whisker-concat α refl)) ∙h
      ( tr² B (left-whisker-concat refl β))) ~
    ( ( id ·l (tr² B α)) ∙h (tr² B β))
  tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² α β =
    horizontal-concat-htpy²
      ( ( tr³
          ( B)
          ( inv (right-unit-law-right-whisker-concat α ∙ right-unit))) ∙h
        ( inv-htpy (left-unit-law-left-whisker-comp (tr² B α))))
      ( tr³ B (left-unit-law-left-whisker-concat β))

  compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( inv-coherence-square-homotopies-horizontal-refl
      ( ( tr² B (right-whisker-concat α refl)) ∙h
      ( tr² B (left-whisker-concat refl β)))
      ( id ·l (tr² B α) ∙h tr² B β)
      ( tr²-right-whisker-concat-tr²-left-whisker-concat α β)) ~
    ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² α β)
  compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² α β =
    ( vertical-pasting-inv-coherence-square-homotopies-horizontal-refl
      ( tr² B (right-whisker-concat α refl))
      ( id ·l (tr² B α))
      ( tr² B (left-whisker-concat refl β))
      ( tr² B β)
      ( tr²-right-whisker α refl)
      ( tr²-left-whisker refl β)) ∙h
    ( z-concat-htpy³
      ( inv-htpy (tr³-right-unit-law-right-whisker-concat-Ω² α))
      ( inv-htpy (tr³-left-unit-law-left-whisker-concat-Ω² β)))

  tr²-concat-left-whisker-concat-right-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( tr²
      ( B)
      ( ( left-whisker-concat refl α) ∙
        ( right-whisker-concat β refl))) ~
    ( ( ( tr² B α) ·r (tr B refl)) ∙h ((tr B refl) ·l (tr² B β)))
  tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β =
    ( tr²-concat
      ( left-whisker-concat refl α)
      ( right-whisker-concat β refl)) ∙h
    ( tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β)

  compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( ( inv-htpy right-unit-htpy) ∙h
      ( tr²-concat-left-whisker-concat-right-whisker-concat α β)) ~
    ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
  compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β =
    ( inv-htpy
      ( assoc-htpy
        ( inv-htpy right-unit-htpy)
        ( right-whisker-concat-htpy
          ( tr²-concat
            ( left-whisker-concat refl α)
            ( right-whisker-concat β refl))
          ( refl-htpy))
        ( tr²-left-whisker-concat-tr²-right-whisker-concat α β))) ∙h
    ( right-whisker-concat-htpy
      ( vertical-inv-coherence-square-homotopies
        ( right-whisker-concat-htpy
          ( tr²-concat
            ( left-whisker-concat refl α)
            ( right-whisker-concat β refl))
          ( refl-htpy))
        ( right-unit-htpy)
        ( right-unit-htpy)
        ( tr²-concat
          ( left-whisker-concat refl α)
          ( right-whisker-concat β refl))
        ( right-unit-law-right-whisker-concat-htpy
          ( tr²-concat
            ( left-whisker-concat refl α)
            ( right-whisker-concat β refl))))
      ( tr²-left-whisker-concat-tr²-right-whisker-concat α β)) ∙h
    ( assoc-htpy
      ( tr²-concat
        ( left-whisker-concat refl α)
        ( right-whisker-concat β refl))
      ( inv-htpy right-unit-htpy)
      ( tr²-left-whisker-concat-tr²-right-whisker-concat α β)) ∙h
    ( left-whisker-concat-htpy
      ( tr²-concat
        ( left-whisker-concat refl α)
        ( right-whisker-concat β refl))
      ( compute-tr²-left-whisker-concat-tr²-right-whisker-concat-Ω² α β))

  tr²-concat-right-whisker-concat-left-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( tr²
      ( B)
      ( ( right-whisker-concat α refl) ∙
        ( left-whisker-concat refl β))) ~
    ( ( ( tr B refl) ·l (tr² B α)) ∙h ((tr² B β) ·r (tr B refl)))
  tr²-concat-right-whisker-concat-left-whisker-concat-Ω² α β =
    ( tr²-concat
      ( right-whisker-concat α refl)
      ( left-whisker-concat refl β)) ∙h
    ( tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² α β)

  compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    ( ( inv-htpy right-unit-htpy) ∙h
      ( tr²-concat-right-whisker-concat-left-whisker-concat α β)) ~
    ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² α β)
  compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω² α β =
    ( inv-htpy
      ( assoc-htpy
        ( inv-htpy right-unit-htpy)
        ( right-whisker-concat-htpy
          ( tr²-concat
            ( right-whisker-concat α refl)
            ( left-whisker-concat refl β))
          ( refl-htpy))
        ( tr²-right-whisker-concat-tr²-left-whisker-concat α β))) ∙h
    ( right-whisker-concat-htpy
      ( vertical-inv-coherence-square-homotopies
        ( right-whisker-concat-htpy
          ( tr²-concat
            ( right-whisker-concat α refl)
            ( left-whisker-concat refl β))
          ( refl-htpy))
        ( right-unit-htpy)
        ( right-unit-htpy)
        ( tr²-concat
          ( right-whisker-concat α refl)
          ( left-whisker-concat refl β))
        ( right-unit-law-right-whisker-concat-htpy
          ( tr²-concat
            ( right-whisker-concat α refl)
            ( left-whisker-concat refl β))))
      ( tr²-right-whisker-concat-tr²-left-whisker-concat α β)) ∙h
    ( assoc-htpy
      ( tr²-concat
        ( right-whisker-concat α refl)
        ( left-whisker-concat refl β))
      ( inv-htpy right-unit-htpy)
      ( tr²-right-whisker-concat-tr²-left-whisker-concat α β)) ∙h
    ( left-whisker-concat-htpy
      ( tr²-concat
        ( right-whisker-concat α refl)
        ( left-whisker-concat refl β))
      ( compute-tr²-right-whisker-concat-tr²-left-whisker-concat-Ω² α β))
```

##### A simplification of the main coherence when `α` and `β` are 2-loops

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a : A}
  {B : A → UU l2}
  where

  tr³-commutative-left-whisker-right-whisker-concat-Ω² :
    (α β : refl {x = a} ＝ refl) →
    coherence-square-homotopies
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
      ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
      ( commutative-right-whisker-left-whisker-htpy
        ( tr² B α)
        ( tr² B β))
      ( tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
  tr³-commutative-left-whisker-right-whisker-concat-Ω² α β =
    concat-bottom-homotopy-coherence-square-homotopies
      ( tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
      ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
      ( commutative-right-whisker-left-whisker-htpy
        ( tr² B α)
        ( tr² B β))
      ( ( inv-htpy right-unit-htpy) ∙h
        ( tr²-concat-right-whisker-concat-left-whisker-concat β α))
      ( compute-tr²-concat-right-whisker-concat-left-whisker-concat-Ω² β α)
      ( concat-top-homotopy-coherence-square-homotopies
        ( ( inv-htpy right-unit-htpy) ∙h
          ( tr²-concat-left-whisker-concat-right-whisker-concat α β))
        ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
        ( commutative-right-whisker-left-whisker-htpy
          ( tr² B α)
          ( tr² B β))
        ( ( inv-htpy right-unit-htpy) ∙h
          ( tr²-concat-right-whisker-concat-left-whisker-concat β α))
        ( compute-tr²-concat-left-whisker-concat-right-whisker-concat-Ω² α β)
        ( horizontal-pasting-coherence-square-homotopies
          ( inv-htpy right-unit-htpy)
          ( tr²-concat-left-whisker-concat-right-whisker-concat α β)
          ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
          ( right-whisker-concat-htpy
            ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
            ( refl-htpy))
          ( commutative-right-whisker-left-whisker-htpy
            ( tr² B α)
            ( tr² B β))
          ( inv-htpy right-unit-htpy)
          ( tr²-concat-right-whisker-concat-left-whisker-concat β α)
          ( horizontal-inv-coherence-square-homotopies
            ( right-unit-htpy)
            ( right-whisker-concat-htpy
              ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
              ( refl-htpy))
            ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
            ( right-unit-htpy)
            ( inv-htpy
              ( right-unit-law-right-whisker-concat-htpy
                ( tr³
                  ( B)
                  ( commutative-left-whisker-right-whisker-concat α β)))))
          ( concat-right-homotopy-coherence-square-homotopies
            ( tr²-concat-left-whisker-concat-right-whisker-concat α β)
            ( right-whisker-concat-htpy
              ( tr³ B (commutative-left-whisker-right-whisker-concat α β))
              ( refl-htpy))
            ( left-whisker-concat-htpy
              ( refl-htpy)
              ( commutative-right-whisker-left-whisker-htpy
                ( tr² B α)
                ( tr² B β)))
            ( tr²-concat-right-whisker-concat-left-whisker-concat β α)
            ( left-unit-law-left-whisker-comp
              ( commutative-right-whisker-left-whisker-htpy
                ( tr² B α)
                ( tr² B β)))
            ( tr³-commutative-left-whisker-right-whisker-concat α β))))
```
