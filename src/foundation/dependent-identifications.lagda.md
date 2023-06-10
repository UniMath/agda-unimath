# Dependent identifications

```agda
module foundation.dependent-identifications where

open import foundation-core.dependent-identifications public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.transport
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

We characterize dependent paths in the family of depedent paths; define the
groupoidal operators on dependent paths; define the cohrences paths: prove the
operators are equivalences.

## Properites

### Transport in the type family of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2) {b0 : B a0} {b1 : B a1} (α : p0 ＝ p1)
  where

  tr-dependent-identification :
    (q01 : dependent-identification B p0 b0 b1) →
    tr (λ t → dependent-identification B t b0 b1) α q01 ＝
    (inv (tr² B α b0) ∙ q01)
  tr-dependent-identification q01 = inv (tr-ap {D = (λ x → x ＝ b1)}
    (λ t → tr B t b0) (λ x → id) α q01) ∙ tr-Id-left (tr² B α b0) q01

  tr-inv-dependent-identification :
    (q01 : dependent-identification B p1 b0 b1) →
    tr (λ t → dependent-identification B t b0 b1) (inv α) q01 ＝
    ((tr² B α b0) ∙ q01)
  tr-inv-dependent-identification q01 =
    ( inv
      ( tr-ap
        { D = λ x → x ＝ b1}
        ( λ t → tr B t b0)
        ( λ x → id)
        ( inv α)
        ( q01))) ∙
    ( ( tr-Id-left (ap (λ t → tr B t b0) (inv α)) q01) ∙
      ( ( ap (λ t → t ∙ q01) (inv (ap-inv (λ t → tr B t b0) (inv α)))) ∙
        ( ap (λ x → ap (λ t → tr B t b0) x ∙ q01) (inv-inv α))))

  tr-dependent-identification-eq-inv-tr²-concat :
    tr (λ t → dependent-identification B t b0 b1) α ＝ (inv (tr² B α b0) ∙_)
  tr-dependent-identification-eq-inv-tr²-concat =
    map-inv-equiv
      ( htpy-eq ,
        funext
          ( tr
            ( λ t → dependent-identification B t b0 b1) α)
          ( inv (tr² B α b0) ∙_))
      ( tr-dependent-identification)

  tr-inv-dependent-identification-eq-tr²-concat :
    (tr (λ t → dependent-identification B t b0 b1) (inv α)) ＝ ((tr² B α b0) ∙_)
  tr-inv-dependent-identification-eq-tr²-concat =
    map-inv-equiv
      ( htpy-eq ,
        funext
          ( tr
            ( λ t → dependent-identification B t b0 b1)
            ( inv α))
          ( tr² B α b0 ∙_))
      ( tr-inv-dependent-identification)
```

### Characterizing iterated types of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  where

  dependent-identification² :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1} (α : p0 ＝ p1)
    {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    UU l2
  dependent-identification² α q0 q1 =
    q0 ＝ ((tr² B α _) ∙ q1)

  tr-dependent-identification-dependent-identification² :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1}
    (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    dependent-identification² α q0 q1 →
    dependent-identification (λ t → dependent-identification B t b0 b1) α q0 q1
  tr-dependent-identification-dependent-identification²
    {p0 = refl} refl ._ refl refl =
    refl

  dependent-identification²-tr-dependent-identification :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1}
    (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    tr (λ t → dependent-identification B t b0 b1) α q0 ＝ q1 →
    dependent-identification² α q0 q1
  dependent-identification²-tr-dependent-identification
    {p0 = refl} refl refl ._ refl =
    refl

  issec-dependent-identification²-tr-dependent-identification :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1}
    (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    ( tr-dependent-identification-dependent-identification² α q0 q1 ∘
      dependent-identification²-tr-dependent-identification α q0 q1) ~ id
  issec-dependent-identification²-tr-dependent-identification
    {p0 = refl} refl refl ._ refl =
    refl

  isretr-dependent-identification²-tr-dependent-identification :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1}
    (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    ( dependent-identification²-tr-dependent-identification α q0 q1 ∘
      tr-dependent-identification-dependent-identification² α q0 q1) ~ id
  isretr-dependent-identification²-tr-dependent-identification
    {p0 = refl} refl ._ refl refl =
    refl

  is-equiv-tr-dependent-identification-dependent-identification² :
    {a0 a1 : A} {p0 p1 : a0 ＝ a1}
    (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
    (q0 : dependent-identification B p0 b0 b1)
    (q1 : dependent-identification B p1 b0 b1) →
    is-equiv (tr-dependent-identification-dependent-identification² α q0 q1)
  is-equiv-tr-dependent-identification-dependent-identification² α q0 q1 =
    is-equiv-has-inverse
      ( dependent-identification²-tr-dependent-identification α q0 q1)
      ( issec-dependent-identification²-tr-dependent-identification α q0 q1)
      ( isretr-dependent-identification²-tr-dependent-identification α q0 q1)
```

### The groupoidal structure of dependent identifications

We show that there is groupoidal structure on the dependent identifications. The
statement of the groupoid laws use dependent identifications, due to the
dependent nature of dependent identifications.

#### Concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2)
  {a0 a1 a2 : A} (p01 : a0 ＝ a1) (p12 : a1 ＝ a2)
  {b0 : B a0} {b1 : B a1} {b2 : B a2}
  (q01 : dependent-identification B p01 b0 b1)
  (q12 : dependent-identification B p12 b1 b2)
  where

  concat-dependent-identification :
    dependent-identification B (p01 ∙ p12) b0 b2
  concat-dependent-identification =
    ( tr-concat {B = B} p01 p12 b0) ∙
    ( ( ap (tr B p12) q01) ∙
      ( q12))
```

#### Inverses of dependent identifications

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {a0 a1 : A}
  (B : A → UU l2) (p01 : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
  (q01 : dependent-identification B p01 b0 b1)
  where

  inv-dependent-identification : dependent-identification B (inv p01) b1 b0
  inv-dependent-identification =
    ( inv (ap (tr B (inv p01)) q01)) ∙
    ( ( inv (tr-concat {B = B} (p01) (inv p01) b0)) ∙
      ( ap (λ t → tr B t b0) (right-inv p01)))
```

#### Associativity of concatenation of dependent identifications

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {a0 a1 : A} (B : A → UU l2) {b0 : B a0} {b1 : B a1}
  where

  d-assoc :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1) (q01 : dependent-identification B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2)
    (p23 : a2 ＝ a3) (q23 : dependent-identification B p23 b2 b3) →
    dependent-identification² B
      ( assoc p01 p12 p23)
      ( concat-dependent-identification B
        ( p01 ∙ p12)
        ( p23)
        ( concat-dependent-identification B p01 p12 q01 q12)
        ( q23))
      ( concat-dependent-identification B
        ( p01)
        ( p12 ∙ p23)
        ( q01)
        ( concat-dependent-identification B p12 p23 q12 q23))
  d-assoc refl refl p12 q12 p23 q23 = refl

  d-assoc' :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : dependent-identification B p12 b1 b2) (p23 : a2 ＝ a3)
    (q23 : dependent-identification B p23 b2 b3) →
    dependent-identification
      ( λ t → dependent-identification B t b0 b3)
      ( assoc p01 p12 p23)
      ( concat-dependent-identification B
        ( p01 ∙ p12)
        ( p23)
        ( concat-dependent-identification B p01 p12 q01 q12)
        ( q23))
      ( concat-dependent-identification B
        ( p01)
        ( p12 ∙ p23)
        ( q01)
        ( concat-dependent-identification B p12 p23 q12 q23))
  d-assoc' p01 q01 p12 q12 p23 q23 =
    tr-dependent-identification-dependent-identification² B
      ( assoc p01 p12 p23)
      ( concat-dependent-identification B
        ( p01 ∙ p12)
        ( p23)
        ( concat-dependent-identification B p01 p12 q01 q12)
        ( q23))
      ( concat-dependent-identification B
        ( p01)
        ( p12 ∙ p23)
        ( q01)
        ( concat-dependent-identification B p12 p23 q12 q23))
      ( d-assoc p01 q01 p12 q12 p23 q23)

  d-right-unit :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( right-unit {p = p})
      ( concat-dependent-identification B p refl q
        ( refl-dependent-identification B))
      ( q)
  d-right-unit refl refl = refl

  d-right-unit' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification
      ( λ t → dependent-identification B t b0 b1)
      ( right-unit)
      ( concat-dependent-identification B p refl q
        ( refl-dependent-identification B))
      ( q)
  d-right-unit' p q =
    tr-dependent-identification-dependent-identification² B
      ( right-unit {p = p})
      ( concat-dependent-identification B p refl q
        ( refl-dependent-identification B))
      ( q)
      ( d-right-unit p q)

  d-left-unit :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( left-unit {p = p})
      ( concat-dependent-identification B refl p
        ( refl-dependent-identification B)
        ( q))
      ( q)
  d-left-unit p q = refl

  d-left-unit' :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    dependent-identification
      ( λ t → dependent-identification B t b0 b1)
      ( left-unit)
      ( concat-dependent-identification B refl p
        ( refl-dependent-identification B)
        ( q))
      ( q)
  d-left-unit' p q =
    tr-dependent-identification-dependent-identification² B
      ( left-unit {p = p})
      ( concat-dependent-identification B refl p
        ( refl-dependent-identification B)
        ( q))
      ( q)
      ( d-left-unit p q)

  d-right-inv :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification² B
      ( right-inv p)
      ( concat-dependent-identification B
        ( p)
        ( inv p)
        ( q)
        ( inv-dependent-identification B p q))
      ( refl-dependent-identification B)
  d-right-inv refl refl = refl

  d-right-inv' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification
      ( λ t → dependent-identification B t b0 b0)
      ( right-inv p)
      ( concat-dependent-identification B
        ( p)
        ( inv p)
        ( q)
        ( inv-dependent-identification B p q))
      ( refl-dependent-identification B)
  d-right-inv' p q =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( right-inv p)
      ( concat-dependent-identification B
        ( p)
        ( inv p)
        ( q)
        ( inv-dependent-identification B p q))
      ( refl-dependent-identification B)
      ( d-right-inv p q)

  d-left-inv :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( left-inv p)
      ( concat-dependent-identification B
        ( inv p)
        ( p)
        ( inv-dependent-identification B p q)
        ( q))
      ( refl-dependent-identification B)
  d-left-inv refl refl = refl

  d-left-inv' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification
      ( λ t → dependent-identification B t b1 b1)
      ( left-inv p)
      ( concat-dependent-identification B
        ( inv p)
        ( p)
        ( inv-dependent-identification B p q)
        ( q))
      ( refl-dependent-identification B)
  d-left-inv' p q =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( left-inv p)
      ( concat-dependent-identification B
        ( inv p)
        ( p)
        ( inv-dependent-identification B p q)
        ( q))
      ( refl-dependent-identification B)
      ( d-left-inv p q)

  inv-inv-dependent-identification :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification² B
      ( inv-inv p)
      ( inv-dependent-identification B
        ( inv p)
        ( inv-dependent-identification B p q))
      ( q)
  inv-inv-dependent-identification refl refl = refl

  inv-inv-dependent-identification' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification
      ( λ t → dependent-identification B t b0 b1)
      ( inv-inv p)
      ( inv-dependent-identification B
        ( inv p)
        ( inv-dependent-identification B p q))
      ( q)
  inv-inv-dependent-identification' p q =
    tr-dependent-identification-dependent-identification² B
      ( inv-inv p)
      ( inv-dependent-identification B
        ( inv p)
        ( inv-dependent-identification B p q))
      ( q)
      ( inv-inv-dependent-identification p q)

  distributive-inv-concat-dependent-identification :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2) →
    dependent-identification² B
      ( distributive-inv-concat p01 p12)
      ( inv-dependent-identification B
        ( p01 ∙ p12)
        ( concat-dependent-identification B p01 p12 q01 q12))
      ( concat-dependent-identification B
        ( inv p12)
        ( inv p01)
        ( inv-dependent-identification B p12 q12)
        ( inv-dependent-identification B p01 q01))
  distributive-inv-concat-dependent-identification refl refl refl refl = refl

  distributive-inv-concat-dependent-identification' :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2) →
    dependent-identification
      ( λ t → dependent-identification B t b2 b0)
      ( distributive-inv-concat p01 p12)
      ( inv-dependent-identification B
        ( p01 ∙ p12)
        ( concat-dependent-identification B p01 p12 q01 q12))
      ( concat-dependent-identification B
        ( inv p12)
        ( inv p01)
        ( inv-dependent-identification B p12 q12)
        ( inv-dependent-identification B p01 q01))
  distributive-inv-concat-dependent-identification' p01 q01 p12 q12 =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( distributive-inv-concat p01 p12)
      ( inv-dependent-identification B
        ( p01 ∙ p12)
        ( concat-dependent-identification B p01 p12 q01 q12))
      ( concat-dependent-identification B
        ( inv p12)
        ( inv p01)
        ( inv-dependent-identification B p12 q12)
        ( inv-dependent-identification B p01 q01))
      ( distributive-inv-concat-dependent-identification p01 q01 p12 q12)
```
