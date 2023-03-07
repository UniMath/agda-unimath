<<<<<<< Updated upstream
# Dependent paths

=======
#  Dependent paths
>>>>>>> Stashed changes
We characterize dependent paths in the family of depedent paths;
define the groupoidal operators on dependent paths; define the cohrences paths: prove the operators are equivalences.

```agda
module foundation.dependent-paths where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.transport
open import foundation.universe-levels
```

</details>

We characterize dependent paths in the family λ t → path-over B t b0 b1

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

  tr-path-over :
    (q01 : path-over B p0 b0 b1) →
    (tr (λ t → path-over B t b0 b1) α q01) ＝ (inv (tr² B α b0) ∙ q01)
  tr-path-over q01 = inv (tr-ap {D = (λ x → x ＝ b1)}
    (λ t → tr B t b0) (λ x → id) α q01) ∙ tr-Id-left (tr² B α b0) q01

  tr-inv-path-over :
    (q01 : path-over B p1 b0 b1) →
    (tr (λ t → path-over B t b0 b1) (inv α) q01) ＝ ((tr² B α b0) ∙ q01)
  tr-inv-path-over q01 = inv (tr-ap {D = λ x → x ＝ b1}
    (λ t → tr B t b0) (λ x → id) (inv α) q01) ∙
    (tr-Id-left (ap (λ t → tr B t b0) (inv α)) q01 ∙
    (ap (λ t → t ∙ q01) (inv (ap-inv (λ t → tr B t b0) (inv α))) ∙
    ap (λ x → ap (λ t → tr B t b0) x ∙ q01) (inv-inv α)))

  tr-path-over-eq-inv-tr²-concat :
    (tr (λ t → path-over B t b0 b1) α) ＝ (λ q → inv (tr² B α b0) ∙ q)
  tr-path-over-eq-inv-tr²-concat = map-inv-equiv ((htpy-eq) ,
    (funext (tr (λ t → path-over B t b0 b1) α) (λ q → inv (tr² B α b0) ∙ q))) tr-path-over

  tr-inv-path-over-eq-tr²-concat :
    (λ q → tr (λ t → path-over B t b0 b1) (inv α) q) ＝ (λ q → (tr² B α b0) ∙ q)
  tr-inv-path-over-eq-tr²-concat = map-inv-equiv ((htpy-eq) ,
    (funext (tr (λ t → path-over B t b0 b1) (inv α)) (λ q → (tr² B α b0) ∙ q))) tr-inv-path-over

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} {p0 p1 : a0 ＝ a1}
  (B : A → UU l2) (α : p0 ＝ p1) {b0 : B a0} {b1 : B a1}
  (q0 : path-over B p0 b0 b1) (q1 : path-over B p1 b0 b1)
  where

  path-over² : UU l2
  path-over² = q0 ＝ ((tr² B α b0) ∙ q1)

  tr-path-over-path-over² :
    (path-over²) → ((tr (λ t → path-over B t b0 b1) α q0) ＝ q1)
  tr-path-over-path-over² z = tr-path-over B α q0 ∙ (
    (map-inv-equiv (equiv-inv-con (inv (tr² B α b0)) q0 q1)
    (z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (tr² B α b0))))))

  path-over²-tr-path-over :
    ((tr (λ t → path-over B t b0 b1) α q0) ＝ q1) → (path-over²)
  path-over²-tr-path-over z =
    (map-equiv (equiv-inv-con (inv (tr² B α b0)) q0 q1) ((inv (tr-path-over B α q0)) ∙ z)) ∙
    ap (λ t → t ∙ q1) (inv-inv (tr² B α b0))

{- Could simplify ensuing proof enormously by rewriting map
and inverse as compositions of known equivalences and then applying 2-of-3 like lemma
Too bad I thought of this only after writing everything out...oops -}

  issec-path-over²-tr-path-over :
    ((λ z → tr-path-over-path-over² z) ∘ path-over²-tr-path-over) ~ id
  issec-path-over²-tr-path-over z =
    (ap (λ x → tr-path-over B α q0 ∙
    pr1 (pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)) x)
    (assoc (inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1 (inv (tr-path-over B α q0) ∙ z))
    (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))
    (inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))))) ∙
    ((ap (λ x → tr-path-over B α q0 ∙
    pr1 (pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1))
    (inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1 (inv (tr-path-over B α q0) ∙ z) ∙ x ))
    (right-inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))) ∙
    ((ap (λ x → tr-path-over B α q0 ∙ pr1 (pr1 (is-equiv-inv-con
    (inv (ap (λ t → tr B t b0) α)) q0 q1)) x) right-unit) ∙
    ((ap (λ x → tr-path-over B α q0 ∙ x) ( isretr-map-inv-equiv
    (equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1) (inv (tr-path-over B α q0) ∙ z) )) ∙
    (inv (assoc (tr-path-over B α q0) (inv (tr-path-over B α q0)) z) ∙
    (ap (λ t → t ∙ z) (right-inv (tr-path-over B α q0)))))))

  isretr-path-over²-tr-path-over :
    (path-over²-tr-path-over ∘ (λ z → tr-path-over-path-over² z)) ~ id
  isretr-path-over²-tr-path-over z =
    (ap (λ x → inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1 x ∙
    ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))
    (inv (assoc (inv (tr-path-over B α q0)) (tr-path-over B α q0)
    (pr1 (pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1))
    (z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))))) ) ∙
    (ap (λ x → inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1
    (x ∙ pr1 (pr1 (is-equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1))
    (z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))) ∙
    ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))) (left-inv (tr-path-over B α q0)) ∙
    (ap (λ x → x ∙ ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))
    (issec-map-inv-equiv (equiv-inv-con (inv (ap (λ t → tr B t b0) α)) q0 q1)
    (z ∙ inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))) ∙
    (assoc z (inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))))
    (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α))) ∙
    (ap (λ t → z ∙ t) (left-inv (ap (λ t → t ∙ q1) (inv-inv (ap (λ t → tr B t b0) α)))) ∙ right-unit))))

  is-equiv-tr-path-over-path-over² :
    is-equiv tr-path-over-path-over²
  is-equiv-tr-path-over-path-over² =
    is-equiv-has-inverse path-over²-tr-path-over
    issec-path-over²-tr-path-over isretr-path-over²-tr-path-over

```

Definition: Groupoidal operators on dependent paths.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 a2 : A} (B : A → UU l2) {b0 : B a0} {b1 : B a1} {b2 : B a2}
   (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2)
  where

  d-concat : path-over B (p01 ∙ p12) b0 b2
  d-concat =   (tr-concat {B = B} p01 p12 b0)  ∙ ((ap (tr B p12) q01) ∙ (q12))

module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) (p01 : a0 ＝ a1) {b0 : B a0} {b1 : B a1}
  (q01 : path-over B p01 b0 b1)
  where

  d-inv : path-over B (inv p01) b1 b0
  d-inv =  (inv (ap (tr B (inv p01)) q01)) ∙ ((inv (tr-concat {B = B} (p01) (inv p01) b0)) ∙ (
    ap (λ t → tr B t b0) (right-inv p01)))
```

Now we prove these paths satisfy identities analgous to the usual unit, inverse, and associativity laws.
Though, due to the dependent nature, the naive identities are not well typed. So these identities involve transporting.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {a0 a1 : A} (B : A → UU l2) {b0 : B a0} {b1  : B a1}
  where

  d-assoc :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : path-over B p12 b1 b2) (p23 : a2 ＝ a3) (q23 : path-over B p23 b2 b3) →
    path-over² B (assoc p01 p12 p23)
      (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
      (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
  d-assoc refl refl p12 q12 p23 q23 = refl

  d-assoc' :
    {a2 a3 : A} {b2 : B a2} {b3 : B a3}
    (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1) (p12 : a1 ＝ a2)
    (q12 : path-over B p12 b1 b2) (p23 : a2 ＝ a3) (q23 : path-over B p23 b2 b3) →
    (tr (λ t → path-over B t b0 b3) (assoc p01 p12 p23) (d-concat B (p01 ∙ p12) (
    d-concat B p01 q01 p12 q12) p23 q23)) ＝
    d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23)
  d-assoc' p01 q01 p12 q12 p23 q23 =
    tr-path-over-path-over² B  (assoc p01 p12 p23)
    (d-concat B (p01 ∙ p12) (d-concat B p01 q01 p12 q12) p23 q23)
    (d-concat B p01 q01 (p12 ∙ p23) (d-concat B p12 q12 p23 q23))
    (d-assoc p01 q01 p12 q12 p23 q23)

  d-right-unit : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (right-unit {p = p}) (d-concat B p q refl (refl-path-over B a1 b1)) q
  d-right-unit refl refl = refl

  d-right-unit' :
    (p : a0 ＝ a1) (q : path-over B p b0 b1) → (tr (λ t → path-over B t b0 b1) (right-unit) (
    d-concat B p q refl (refl-path-over B a1 b1))) ＝ q
  d-right-unit' p q = tr-path-over-path-over² B (right-unit {p = p})
    (d-concat B p q refl (refl-path-over B a1 b1)) q (d-right-unit p q)

  d-left-unit : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (left-unit {p = p}) (d-concat B refl (refl-path-over B a0 b0) p q) q
  d-left-unit p q = refl

  d-left-unit' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (left-unit) (d-concat B refl (refl-path-over B a0 b0) p q)) ＝ q
  d-left-unit' p q = tr-path-over-path-over² B (left-unit {p = p})
    (d-concat B refl (refl-path-over B a0 b0) p q) q (d-left-unit p q)

  d-right-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (right-inv p) (d-concat B p q (inv p) (d-inv B p q))
    (refl-path-over B a0 b0)
  d-right-inv refl refl = refl

  d-right-inv' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b0) (right-inv p) (d-concat B p q (inv p) (d-inv B p q))) ＝ (
     refl-path-over B a0 b0)
  d-right-inv' p q  = tr-path-over-path-over² B (right-inv p)
    (d-concat B p q (inv p) (d-inv B p q)) (refl-path-over B a0 b0) (d-right-inv p q)

  d-left-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (left-inv p) (d-concat B (inv p) (d-inv B p q) p q) (refl-path-over B a1 b1)
  d-left-inv refl refl = refl

  d-left-inv' :  (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b1 b1) (left-inv p) (d-concat B (inv p) (d-inv B p q) p q)) ＝ (
     refl-path-over B a1 b1)
  d-left-inv' p q = tr-path-over-path-over² B (left-inv p)
    (d-concat B (inv p) (d-inv B p q) p q) (refl-path-over B a1 b1) (d-left-inv p q)

  d-inv-d-inv : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    path-over² B (inv-inv p) (d-inv B (inv p) (d-inv B p q)) q
  d-inv-d-inv refl refl = refl

  d-inv-d-inv' : (p : a0 ＝ a1) (q : path-over B p b0 b1) →
    (tr (λ t → path-over B t b0 b1) (inv-inv p) (d-inv B (inv p) (d-inv B p q))) ＝ q
  d-inv-d-inv' p q = tr-path-over-path-over² B (inv-inv p)
    (d-inv B (inv p) (d-inv B p q)) q (d-inv-d-inv p q)

  distributive-d-inv-d-concat :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2) →
    path-over² B (distributive-inv-concat p01 p12)
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
    (d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat refl refl refl refl = refl

  distributive-d-inv-d-concat' :
    {a2 : A} {b2 : B a2} (p01 : a0 ＝ a1) (q01 : path-over B p01 b0 b1)
    (p12 : a1 ＝ a2) (q12 : path-over B p12 b1 b2) →
    (tr (λ t → path-over B t b2 b0) (distributive-inv-concat p01 p12) (
    (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12)))) ＝ (
    d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01))
  distributive-d-inv-d-concat' p01 q01 p12 q12 = tr-path-over-path-over² B
    (distributive-inv-concat p01 p12) (d-inv B (p01 ∙ p12) (d-concat B p01 q01 p12 q12))
    (d-concat B (inv p12) (d-inv B p12 q12) (inv p01) (d-inv B p01 q01)) (distributive-d-inv-d-concat p01 q01 p12 q12)
```
