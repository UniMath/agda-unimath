# W-types

```agda
module trees.w-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-truncated-types
open import foundation.double-negation-dense-equality
open import foundation.double-negation-stable-equality
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.irrefutable-equality
open import foundation.postcomposition-functions
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.type-theoretic-principle-of-choice
open import foundation.types-with-decidable-dependent-product-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.discrete-types
open import foundation-core.propositions

open import logic.double-negation-elimination

open import trees.algebras-polynomial-endofunctors
open import trees.coalgebras-polynomial-endofunctors
open import trees.morphisms-algebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

Consider a type `A` equipped with a type family `B` over `A`. The type `𝕎`
generated inductively by a constructor `B x → 𝕎` for each `x : A` is called the
{{#concept "W-type" Agda=𝕎}} `𝕎 A B` of `B`. The elements of `A` can be thought
of as symbols for the constructors of `𝕎 A B`, and the functions `B x → 𝕎 A B`
are the constructors. The elements of `𝕎 A B` can be thought of as well-founded
trees.

## Definition

```agda
data 𝕎 {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  tree-𝕎 : (x : A) (α : B x → 𝕎 A B) → 𝕎 A B

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  shape-𝕎 : 𝕎 A B → A
  shape-𝕎 (tree-𝕎 x α) = x

  component-𝕎 : (x : 𝕎 A B) → B (shape-𝕎 x) → 𝕎 A B
  component-𝕎 (tree-𝕎 x α) = α

  η-𝕎 : (x : 𝕎 A B) → tree-𝕎 (shape-𝕎 x) (component-𝕎 x) ＝ x
  η-𝕎 (tree-𝕎 x α) = refl
```

### W-types as algebras for a polynomial endofunctor

```agda
structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor' A B (𝕎 A B) → 𝕎 A B
structure-𝕎-Alg (pair x α) = tree-𝕎 x α

𝕎-Alg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  algebra-polynomial-endofunctor (l1 ⊔ l2) (A , B)
𝕎-Alg A B = pair (𝕎 A B) structure-𝕎-Alg
```

### W-types as coalgebras for a polynomial endofunctor

```agda
𝕎-Coalg :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  coalgebra-polynomial-endofunctor (l1 ⊔ l2) (A , B)
pr1 (𝕎-Coalg A B) = 𝕎 A B
pr1 (pr2 (𝕎-Coalg A B) x) = shape-𝕎 x
pr2 (pr2 (𝕎-Coalg A B) x) = component-𝕎 x
```

## Properties

### The elements of the form `tree-𝕎 x α` where `B x` is an empty type are called the constants of `W A B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  constant-𝕎 : (x : A) → is-empty (B x) → 𝕎 A B
  constant-𝕎 x h = tree-𝕎 x (ex-falso ∘ h)

  is-constant-𝕎 : 𝕎 A B → UU l2
  is-constant-𝕎 x = is-empty (B (shape-𝕎 x))
```

### If each `B x` is inhabited, then the type `W A B` is empty

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-empty-𝕎 : ((x : A) → type-trunc-Prop (B x)) → is-empty (𝕎 A B)
  is-empty-𝕎 H (tree-𝕎 x α) =
    apply-universal-property-trunc-Prop
      ( H x)
      ( empty-Prop)
      ( λ y → is-empty-𝕎 H (α y))
```

### Equality of W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  Eq-𝕎 : 𝕎 A B → 𝕎 A B → UU (l1 ⊔ l2)
  Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β) =
    Σ (x ＝ y) (λ p → (z : B x) → Eq-𝕎 (α z) (β (tr B p z)))

  refl-Eq-𝕎 : (w : 𝕎 A B) → Eq-𝕎 w w
  refl-Eq-𝕎 (tree-𝕎 x α) = pair refl (λ z → refl-Eq-𝕎 (α z))

  center-total-Eq-𝕎 : (w : 𝕎 A B) → Σ (𝕎 A B) (Eq-𝕎 w)
  center-total-Eq-𝕎 w = pair w (refl-Eq-𝕎 w)

  aux-total-Eq-𝕎 :
    (x : A) (α : B x → 𝕎 A B) →
    Σ (B x → 𝕎 A B) (λ β → (y : B x) → Eq-𝕎 (α y) (β y)) →
    Σ (𝕎 A B) (Eq-𝕎 (tree-𝕎 x α))
  aux-total-Eq-𝕎 x α (pair β e) = pair (tree-𝕎 x β) (pair refl e)

  contraction-total-Eq-𝕎 :
    (w : 𝕎 A B) (t : Σ (𝕎 A B) (Eq-𝕎 w)) → center-total-Eq-𝕎 w ＝ t
  contraction-total-Eq-𝕎
    ( tree-𝕎 x α) (pair (tree-𝕎 .x β) (pair refl e)) =
    ap
      ( ( aux-total-Eq-𝕎 x α) ∘
        ( map-distributive-Π-Σ
          { A = B x}
          { B = λ y → 𝕎 A B}
          { C = λ y → Eq-𝕎 (α y)}))
      { x = λ y → pair (α y) (refl-Eq-𝕎 (α y))}
      { y = λ y → pair (β y) (e y)}
      ( eq-htpy (λ y → contraction-total-Eq-𝕎 (α y) (pair (β y) (e y))))

  is-torsorial-Eq-𝕎 : (w : 𝕎 A B) → is-torsorial (Eq-𝕎 w)
  is-torsorial-Eq-𝕎 w =
    pair (center-total-Eq-𝕎 w) (contraction-total-Eq-𝕎 w)

  Eq-𝕎-eq : (v w : 𝕎 A B) → v ＝ w → Eq-𝕎 v w
  Eq-𝕎-eq v .v refl = refl-Eq-𝕎 v

  is-equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → is-equiv (Eq-𝕎-eq v w)
  is-equiv-Eq-𝕎-eq v =
    fundamental-theorem-id
      ( is-torsorial-Eq-𝕎 v)
      ( Eq-𝕎-eq v)

  eq-Eq-𝕎 : (v w : 𝕎 A B) → Eq-𝕎 v w → v ＝ w
  eq-Eq-𝕎 v w = map-inv-is-equiv (is-equiv-Eq-𝕎-eq v w)

  equiv-Eq-𝕎-eq : (v w : 𝕎 A B) → (v ＝ w) ≃ Eq-𝕎 v w
  equiv-Eq-𝕎-eq v w = pair (Eq-𝕎-eq v w) (is-equiv-Eq-𝕎-eq v w)

  is-trunc-𝕎 : (k : 𝕋) → is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (𝕎 A B)
  is-trunc-𝕎 k is-trunc-A (tree-𝕎 x α) (tree-𝕎 y β) =
    is-trunc-is-equiv k
      ( Eq-𝕎 (tree-𝕎 x α) (tree-𝕎 y β))
      ( Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-equiv-Eq-𝕎-eq (tree-𝕎 x α) (tree-𝕎 y β))
      ( is-trunc-Σ
        ( is-trunc-A x y)
        ( λ p → is-trunc-Π k
          ( λ z →
            is-trunc-is-equiv' k
            ( α z ＝ β (tr B p z))
            ( Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-equiv-Eq-𝕎-eq (α z) (β (tr B p z)))
            ( is-trunc-𝕎 k is-trunc-A (α z) (β (tr B p z))))))

  is-set-𝕎 : is-set A → is-set (𝕎 A B)
  is-set-𝕎 = is-trunc-𝕎 neg-one-𝕋
```

### The structure map of the algebra `𝕎 A B` is an equivalence

```agda
map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B → type-polynomial-endofunctor' A B (𝕎 A B)
map-inv-structure-𝕎-Alg (tree-𝕎 x α) = pair x α

is-section-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (structure-𝕎-Alg {B = B} ∘ map-inv-structure-𝕎-Alg {B = B}) ~ id
is-section-map-inv-structure-𝕎-Alg (tree-𝕎 x α) = refl

is-retraction-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  (map-inv-structure-𝕎-Alg {B = B} ∘ structure-𝕎-Alg {B = B}) ~ id
is-retraction-map-inv-structure-𝕎-Alg (pair x α) = refl

is-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (structure-𝕎-Alg {B = B})
is-equiv-structure-𝕎-Alg =
  is-equiv-is-invertible
    map-inv-structure-𝕎-Alg
    is-section-map-inv-structure-𝕎-Alg
    is-retraction-map-inv-structure-𝕎-Alg

equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  type-polynomial-endofunctor' A B (𝕎 A B) ≃ 𝕎 A B
equiv-structure-𝕎-Alg =
  pair structure-𝕎-Alg is-equiv-structure-𝕎-Alg

is-equiv-map-inv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  is-equiv (map-inv-structure-𝕎-Alg {B = B})
is-equiv-map-inv-structure-𝕎-Alg =
  is-equiv-is-invertible
    structure-𝕎-Alg
    is-retraction-map-inv-structure-𝕎-Alg
    is-section-map-inv-structure-𝕎-Alg

inv-equiv-structure-𝕎-Alg :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  𝕎 A B ≃ type-polynomial-endofunctor' A B (𝕎 A B)
inv-equiv-structure-𝕎-Alg =
  pair map-inv-structure-𝕎-Alg is-equiv-map-inv-structure-𝕎-Alg
```

### W-types are initial algebras for polynomial endofunctors

```agda
map-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  𝕎 A B → type-algebra-polynomial-endofunctor X
map-hom-𝕎-Alg X (tree-𝕎 x α) =
  structure-algebra-polynomial-endofunctor X
    ( pair x (λ y → map-hom-𝕎-Alg X (α y)))

structure-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  ( (map-hom-𝕎-Alg X) ∘ structure-𝕎-Alg) ~
  ( ( structure-algebra-polynomial-endofunctor X) ∘
    ( map-polynomial-endofunctor' A B (map-hom-𝕎-Alg X)))
structure-hom-𝕎-Alg X (pair x α) = refl

hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X
hom-𝕎-Alg X = pair (map-hom-𝕎-Alg X) (structure-hom-𝕎-Alg X)

htpy-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  map-hom-𝕎-Alg X ~
  map-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
htpy-htpy-hom-𝕎-Alg {A = A} {B} X f (tree-𝕎 x α) =
  ( ap
    ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
    ( eq-htpy (λ z → htpy-htpy-hom-𝕎-Alg X f (α z)))) ∙
  ( inv
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f
      ( pair x α)))

compute-structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) (x : A) (α : B x → 𝕎 A B)
  {f : 𝕎 A B → type-algebra-polynomial-endofunctor X} →
  (H : map-hom-𝕎-Alg X ~ f) →
  ( ap
    ( structure-algebra-polynomial-endofunctor X)
    ( htpy-polynomial-endofunctor' A B H (pair x α))) ＝
  ( ap
    ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
    ( htpy-postcomp (B x) H α))
compute-structure-htpy-hom-𝕎-Alg {A = A} {B} X x α =
  ind-htpy
    ( map-hom-𝕎-Alg X)
    ( λ f H →
      ( ap
        ( structure-algebra-polynomial-endofunctor X)
        ( htpy-polynomial-endofunctor' A B H (pair x α))) ＝
      ( ap
        ( λ t → structure-algebra-polynomial-endofunctor X (pair x t))
        ( htpy-postcomp (B x) H α)))
    ( ap
      ( ap (pr2 X))
      ( coh-refl-htpy-polynomial-endofunctor' A B
        ( map-hom-𝕎-Alg X)
        ( pair x α)) ∙
    ( inv
      ( ap
        ( ap (λ t → pr2 X (pair x t)))
        ( eq-htpy-refl-htpy (map-hom-𝕎-Alg X ∘ α)))))

structure-htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  ( structure-hom-𝕎-Alg X ∙h
    ( ( structure-algebra-polynomial-endofunctor X) ·l
      ( htpy-polynomial-endofunctor' A B (htpy-htpy-hom-𝕎-Alg X f)))) ~
  ( ( (htpy-htpy-hom-𝕎-Alg X f) ·r structure-𝕎-Alg {B = B}) ∙h
    ( structure-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X f))
structure-htpy-hom-𝕎-Alg {A = A} {B} X (pair f μ-f) (pair x α) =
  ( ( ( compute-structure-htpy-hom-𝕎-Alg X x α
        ( htpy-htpy-hom-𝕎-Alg X (pair f μ-f))) ∙
      ( inv right-unit)) ∙
    ( ap
      ( concat
        ( ap
          ( λ t → pr2 X (pair x t))
          ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
        ( pr2 X (map-polynomial-endofunctor' A B f (pair x α))))
      ( inv (left-inv ( μ-f (pair x α)))))) ∙
  ( inv
    ( assoc
      ( ap
        ( λ t → pr2 X (pair x t))
        ( eq-htpy (htpy-htpy-hom-𝕎-Alg X (pair f μ-f) ·r α)))
      ( inv (μ-f (pair x α)))
      ( μ-f (pair x α))))

htpy-hom-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  (f : hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X) →
  htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
htpy-hom-𝕎-Alg X f =
  pair (htpy-htpy-hom-𝕎-Alg X f) (structure-htpy-hom-𝕎-Alg X f)

is-initial-𝕎-Alg :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 (A , B)) →
  is-contr (hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X)
is-initial-𝕎-Alg {A = A} {B} X =
  pair
    ( hom-𝕎-Alg X)
    ( λ f →
      eq-htpy-hom-algebra-polynomial-endofunctor (𝕎-Alg A B) X (hom-𝕎-Alg X) f
        ( htpy-hom-𝕎-Alg X f))
```

### Decidable equality for W-types

If `A` has decidable equality and `B : A → 𝒰` is a family of types with
decidable dependent products, then `𝕎 A B` has decidable equality.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (dA : has-decidable-equality A)
  (dΠB : (x : A) → has-decidable-Π (B x))
  where

  is-decidable-Eq-𝕎-has-decidable-equality-shape-has-decidable-Π-position :
    (v w : 𝕎 A B) → is-decidable (Eq-𝕎 v w)
  is-decidable-Eq-𝕎-has-decidable-equality-shape-has-decidable-Π-position
    (tree-𝕎 x α) (tree-𝕎 y β) =
    is-decidable-Σ-has-double-negation-dense-equality-base
      ( λ p q →
        irrefutable-eq-eq
          ( eq-is-prop (is-set-has-decidable-equality dA x y)))
      ( dA x y)
      ( λ p →
        dΠB x
          ( ( λ z → Eq-𝕎 (α z) (β (tr B p z))) ,
            ( λ z →
              is-decidable-Eq-𝕎-has-decidable-equality-shape-has-decidable-Π-position
                ( α z)
                ( β (tr B p z)))))

  has-decidable-equality-𝕎-has-decidable-equality-shape-has-decidable-Π-position :
    has-decidable-equality (𝕎 A B)
  has-decidable-equality-𝕎-has-decidable-equality-shape-has-decidable-Π-position
    v w =
    is-decidable-equiv
      ( equiv-Eq-𝕎-eq v w)
      ( is-decidable-Eq-𝕎-has-decidable-equality-shape-has-decidable-Π-position
        ( v)
        ( w))
```

### Double negation stable equality for W-types

If `A` has double negation stable equality, then `𝕎 A B` has double negation
stable equality.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (hA : has-double-negation-stable-equality A)
  where

  has-double-negation-elim-Eq-𝕎-has-double-negation-stable-equality-shape :
    (v w : 𝕎 A B) → has-double-negation-elim (Eq-𝕎 v w)
  has-double-negation-elim-Eq-𝕎-has-double-negation-stable-equality-shape
    (tree-𝕎 x α) (tree-𝕎 y β) =
    double-negation-elim-Σ-has-double-negation-dense-equality-base
      ( λ p q →
        irrefutable-eq-eq
          ( eq-is-prop (is-set-has-double-negation-stable-equality hA x y)))
      ( hA x y)
      ( λ p →
        double-negation-elim-Π
          ( λ z →
            has-double-negation-elim-Eq-𝕎-has-double-negation-stable-equality-shape
              ( α z)
              ( β (tr B p z))))

  has-double-negation-stable-equality-𝕎-has-double-negation-stable-equality-shape :
    has-double-negation-stable-equality (𝕎 A B)
  has-double-negation-stable-equality-𝕎-has-double-negation-stable-equality-shape
    v w =
    has-double-negation-elim-equiv
      ( equiv-Eq-𝕎-eq v w)
      ( has-double-negation-elim-Eq-𝕎-has-double-negation-stable-equality-shape
        ( v)
        ( w))
```
