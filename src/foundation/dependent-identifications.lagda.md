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
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.transport
```

</details>

## Idea

We characterize dependent paths in the family of depedent paths; define the
groupoidal operators on dependent paths; define the cohrences paths: prove the
operators are equivalences.

## Properites

We characterize dependent paths in the family
`λ t → dependent-identification B t b0 b1`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2)
  where

  tr² : (α : p0 ＝ p1) (b0 : B a0) → (tr B p0 b0) ＝ (tr B p1 b0)
  tr² α b0 = ap (λ t → tr B t b0) α

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

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2) (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
  (q0 : dependent-identification B p0 b0 b1)
  (q1 : dependent-identification B p1 b0 b1)
  where

  dependent-identification² : UU l2
  dependent-identification² = q0 ＝ ((tr² B α b0) ∙ q1)

  tr-dependent-identification-dependent-identification² :
    dependent-identification² →
    tr (λ t → dependent-identification B t b0 b1) α q0 ＝ q1
  tr-dependent-identification-dependent-identification² z =
    ( tr-dependent-identification B α q0) ∙
    ( map-inv-equiv
      ( equiv-inv-con (inv (tr² B α b0)) q0 q1)
      ( z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (tr² B α b0)))))

  dependent-identification²-tr-dependent-identification :
    tr (λ t → dependent-identification B t b0 b1) α q0 ＝ q1 →
    dependent-identification²
  dependent-identification²-tr-dependent-identification z =
    ( map-equiv
      ( equiv-inv-con (inv (tr² B α b0)) q0 q1)
      ( (inv (tr-dependent-identification B α q0)) ∙ z)) ∙
    ( ap (_∙ q1) (inv-inv (tr² B α b0)))

  issec-dependent-identification²-tr-dependent-identification :
    ( tr-dependent-identification-dependent-identification² ∘
      dependent-identification²-tr-dependent-identification) ~ id
  issec-dependent-identification²-tr-dependent-identification z =
    ( ap
      ( λ x →
        tr-dependent-identification B α q0 ∙
        pr1 (pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)) x)
      ( assoc
        ( inv-con
          ( inv (ap (λ t → tr B t b0) α))
          ( q0)
          ( q1)
          ( inv (tr-dependent-identification B α q0) ∙ z))
        ( ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))
        ( inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))))) ∙
      ( ( ap
          ( λ x →
            tr-dependent-identification B α q0 ∙
            pr1
              ( pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1))
              ( ( inv-con
                  ( inv (ap (λ t → tr B t b0) α))
                  ( q0)
                  ( q1)
                  ( inv (tr-dependent-identification B α q0) ∙ z)) ∙
                ( x)))
          ( right-inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))) ∙
        ( ( ap
            ( λ x →
              tr-dependent-identification B α q0 ∙
              pr1
                ( pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1))
                ( x))
            ( right-unit)) ∙
          ( ( ap
              ( λ x → tr-dependent-identification B α q0 ∙ x)
              ( isretr-map-inv-equiv
                ( equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)
                ( inv (tr-dependent-identification B α q0) ∙ z))) ∙
            ( ( inv
                ( assoc
                  ( tr-dependent-identification B α q0)
                  ( inv (tr-dependent-identification B α q0))
                  ( z))) ∙
              ( ap (_∙ z) (right-inv (tr-dependent-identification B α q0)))))))

  isretr-dependent-identification²-tr-dependent-identification :
    ( dependent-identification²-tr-dependent-identification ∘
      tr-dependent-identification-dependent-identification²) ~ id
  isretr-dependent-identification²-tr-dependent-identification z =
    ( ap
      ( λ x →
        ( inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1 x) ∙
        ( ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))
      ( inv
        ( assoc
          ( inv (tr-dependent-identification B α q0))
          ( tr-dependent-identification B α q0)
          ( map-inv-is-equiv
            ( is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)
            ( z ∙ inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))))))) ∙
    ( ap
      ( λ x →
        inv-con
          ( inv (ap (λ t → tr B t b0) α))
          ( q0)
          ( q1)
          ( ( x) ∙
            ( map-inv-is-equiv
              ( is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)
              ( z ∙ inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))))) ∙
          ( ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))
      ( left-inv (tr-dependent-identification B α q0)) ∙
      ( ( ap
          ( _∙ ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))
          ( issec-map-inv-equiv
            ( equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)
            ( z ∙ inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))))) ∙
        ( ( assoc
            ( z)
            ( inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))
            ( ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))) ∙
          ( ( ap
              ( z ∙_)
              ( left-inv (ap (_∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))) ∙
            ( right-unit)))))

  is-equiv-tr-dependent-identification-dependent-identification² :
    is-equiv tr-dependent-identification-dependent-identification²
  is-equiv-tr-dependent-identification-dependent-identification² =
    is-equiv-has-inverse
      ( dependent-identification²-tr-dependent-identification)
      ( issec-dependent-identification²-tr-dependent-identification)
      ( isretr-dependent-identification²-tr-dependent-identification)
```

### The groupoidal operators on dependent paths

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {a0 a1 a2 : A}
  (B : A → UU l2) {b0 : B a0} {b1 : B a1} {b2 : B a2}
  (p01 : a0 ＝ a1) (q01 : dependent-identification B p01 b0 b1)
  (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2)
  where

  d-concat : dependent-identification B (p01 ∙ p12) b0 b2
  d-concat = (tr-concat {B = B} p01 p12 b0) ∙ ((ap (tr B p12) q01) ∙ (q12))

module _
  {l1 l2 : Level}
  {A : UU l1} {a0 a1 : A}
  (B : A → UU l2) (p01 : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
  (q01 : dependent-identification B p01 b0 b1)
  where

  d-inv : dependent-identification B (inv p01) b1 b0
  d-inv =
    ( inv (ap (tr B (inv p01)) q01)) ∙
    ( ( inv (tr-concat {B = B} (p01) (inv p01) b0)) ∙
      ( ap (λ t → tr B t b0) (right-inv p01)))
```

Now we prove these paths satisfy identities analgous to the usual unit, inverse,
and associativity laws. Though, due to the dependent nature, the naive
identities are not well typed. So these identities involve transporting.

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
    dependent-identification² B (assoc p01 p12 p23)
      (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
      (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
  d-assoc refl refl p12 q12 p23 q23 = refl

  d-assoc' :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : dependent-identification B p12 b1 b2) (p23 : a2 ＝ a3)
    (q23 : dependent-identification B p23 b2 b3) →
    ( tr
      ( λ t → dependent-identification B t b0 b3)
      ( assoc p01 p12 p23)
      ( d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)) ＝
    ( d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
  d-assoc' p01 q01 p12 q12 p23 q23 =
    tr-dependent-identification-dependent-identification² B (assoc p01 p12 p23)
    (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
    (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
    (d-assoc p01 q01 p12 q12 p23 q23)

  d-right-unit :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( right-unit {p = p})
      ( d-concat B p q refl (refl-dependent-identification B))
      ( q)
  d-right-unit refl refl = refl

  d-right-unit' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    ( tr
      ( λ t → dependent-identification B t b0 b1)
      ( right-unit)
      (d-concat B p q refl (refl-dependent-identification B))) ＝ q
  d-right-unit' p q =
    tr-dependent-identification-dependent-identification² B (right-unit {p = p})
    (d-concat B p q refl (refl-dependent-identification B)) q (d-right-unit p q)

  d-left-unit :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( left-unit {p = p})
      ( d-concat B refl (refl-dependent-identification B) p q)
      ( q)
  d-left-unit p q = refl

  d-left-unit' :
    (p : a0 ＝ a1)
    (q : dependent-identification B p b0 b1) →
    ( tr
      ( λ t → dependent-identification B t b0 b1)
      ( left-unit)
      ( d-concat B refl (refl-dependent-identification B) p q)) ＝
    ( q)
  d-left-unit' p q =
    tr-dependent-identification-dependent-identification² B (left-unit {p = p})
    (d-concat B refl (refl-dependent-identification B) p q) q (d-left-unit p q)

  d-right-inv :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification² B
      ( right-inv p)
      ( d-concat B p q (inv p) (d-inv B p q))
      ( refl-dependent-identification B)
  d-right-inv refl refl = refl

  d-right-inv' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    ( tr
      ( λ t → dependent-identification B t b0 b0)
      ( right-inv p)
      ( d-concat B p q (inv p) (d-inv B p q))) ＝
    ( refl-dependent-identification B)
  d-right-inv' p q =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( right-inv p)
      ( d-concat B p q (inv p) (d-inv B p q))
      ( refl-dependent-identification B)
      ( d-right-inv p q)

  d-left-inv :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification²
      ( B)
      ( left-inv p)
      ( d-concat B (inv p) (d-inv B p q) p q)
      ( refl-dependent-identification B)
  d-left-inv refl refl = refl

  d-left-inv' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    ( tr
      ( λ t → dependent-identification B t b1 b1)
      ( left-inv p)
      ( d-concat B (inv p) (d-inv B p q) p q)) ＝
    ( refl-dependent-identification B)
  d-left-inv' p q =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( left-inv p)
      ( d-concat B (inv p) (d-inv B p q) p q)
      ( refl-dependent-identification B)
      ( d-left-inv p q)

  d-inv-d-inv :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    dependent-identification² B (inv-inv p) (d-inv B (inv p) (d-inv B p q)) q
  d-inv-d-inv refl refl = refl

  d-inv-d-inv' :
    (p : a0 ＝ a1) (q : dependent-identification B p b0 b1) →
    ( tr
      ( λ t → dependent-identification B t b0 b1)
      ( inv-inv p)
      ( d-inv B (inv p) (d-inv B p q))) ＝
    ( q)
  d-inv-d-inv' p q =
    tr-dependent-identification-dependent-identification² B (inv-inv p)
    (d-inv B (inv p) (d-inv B p q)) q (d-inv-d-inv p q)

  distributive-d-inv-d-concat :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2) →
    dependent-identification² B (distributive-inv-concat p01 p12)
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
    (d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat refl refl refl refl = refl

  distributive-d-inv-d-concat' :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1)
    (q01 : dependent-identification B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : dependent-identification B p12 b1 b2) →
    tr
      ( λ t → dependent-identification B t b2 b0)
      ( distributive-inv-concat p01 p12)
      ( d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12)) ＝
    d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01)
  distributive-d-inv-d-concat' p01 q01 p12 q12 =
    tr-dependent-identification-dependent-identification²
      ( B)
      ( distributive-inv-concat p01 p12)
      ( d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
      ( d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
      ( distributive-d-inv-d-concat p01 q01 p12 q12)
```
