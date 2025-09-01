# Cyclic finite types

```agda
module univalent-combinatorics.cyclic-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integers
open import elementary-number-theory.modular-arithmetic
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.standard-cyclic-groups

open import foundation.0-connected-types
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.isomorphisms-groups

open import higher-group-theory.higher-groups

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.mere-equivalences-types-equipped-with-endomorphisms
open import structured-types.pointed-types
open import structured-types.types-equipped-with-endomorphisms

open import synthetic-homotopy-theory.groups-of-loops-in-1-types
open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

A {{#concept "cyclic type" Agda=Cyclic-Type}} is a type `X`
[equipped](foundation.structure.md) with an endomorphism `f : X → X` such that
the pair `(X, f)` is [merely equivalent](foundation.mere-equivalences.md) to the
pair `(ℤ-Mod k, +1)` for some `k : ℕ`.

## Definitions

### The type of cyclic types of a given order

```agda
is-cyclic-Type-With-Endomorphism :
  {l : Level} → ℕ → Type-With-Endomorphism l → UU l
is-cyclic-Type-With-Endomorphism k X =
  mere-equiv-Type-With-Endomorphism (ℤ-Mod-Type-With-Endomorphism k) X

Cyclic-Type : (l : Level) → ℕ → UU (lsuc l)
Cyclic-Type l k =
  Σ (Type-With-Endomorphism l) (is-cyclic-Type-With-Endomorphism k)

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  endo-Cyclic-Type : Type-With-Endomorphism l
  endo-Cyclic-Type = pr1 X

  type-Cyclic-Type : UU l
  type-Cyclic-Type = type-Type-With-Endomorphism endo-Cyclic-Type

  endomorphism-Cyclic-Type : type-Cyclic-Type → type-Cyclic-Type
  endomorphism-Cyclic-Type =
    endomorphism-Type-With-Endomorphism endo-Cyclic-Type

  mere-equiv-endo-Cyclic-Type :
    mere-equiv-Type-With-Endomorphism
      ( ℤ-Mod-Type-With-Endomorphism k)
      ( endo-Cyclic-Type)
  mere-equiv-endo-Cyclic-Type = pr2 X

  is-set-type-Cyclic-Type : is-set type-Cyclic-Type
  is-set-type-Cyclic-Type =
    apply-universal-property-trunc-Prop
      ( mere-equiv-endo-Cyclic-Type)
      ( is-set-Prop type-Cyclic-Type)
      ( λ e →
        is-set-equiv'
          ( ℤ-Mod k)
          ( equiv-equiv-Type-With-Endomorphism
            ( ℤ-Mod-Type-With-Endomorphism k)
            ( endo-Cyclic-Type)
            ( e))
          ( is-set-ℤ-Mod k))

  set-Cyclic-Type : Set l
  pr1 set-Cyclic-Type = type-Cyclic-Type
  pr2 set-Cyclic-Type = is-set-type-Cyclic-Type
```

### Cyclic-Type structure on a type

```agda
cyclic-structure : {l : Level} → ℕ → UU l → UU l
cyclic-structure k X =
  Σ (X → X) (λ f → is-cyclic-Type-With-Endomorphism k (X , f))

cyclic-type-cyclic-structure :
  {l : Level} (k : ℕ) {X : UU l} → cyclic-structure k X → Cyclic-Type l k
pr1 (pr1 (cyclic-type-cyclic-structure k {X} c)) = X
pr2 (pr1 (cyclic-type-cyclic-structure k c)) = pr1 c
pr2 (cyclic-type-cyclic-structure k c) = pr2 c
```

### The standard cyclic types

```agda
ℤ-Mod-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k
pr1 (ℤ-Mod-Cyclic-Type k) =
  ℤ-Mod-Type-With-Endomorphism k
pr2 (ℤ-Mod-Cyclic-Type k) =
  refl-mere-equiv-Type-With-Endomorphism (ℤ-Mod-Type-With-Endomorphism k)

Fin-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero (succ-ℕ k)
Fin-Cyclic-Type k = ℤ-Mod-Cyclic-Type (succ-ℕ k)

Cyclic-Type-Pointed-Type : (k : ℕ) → Pointed-Type (lsuc lzero)
pr1 (Cyclic-Type-Pointed-Type k) = Cyclic-Type lzero k
pr2 (Cyclic-Type-Pointed-Type k) = ℤ-Mod-Cyclic-Type k
```

### Equivalences of cyclic types

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where

  equiv-Cyclic-Type : UU (l1 ⊔ l2)
  equiv-Cyclic-Type =
    equiv-Type-With-Endomorphism (endo-Cyclic-Type k X) (endo-Cyclic-Type k Y)

  equiv-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X ≃ type-Cyclic-Type k Y
  equiv-equiv-Cyclic-Type =
    equiv-equiv-Type-With-Endomorphism
      ( endo-Cyclic-Type k X)
      ( endo-Cyclic-Type k Y)

  map-equiv-Cyclic-Type :
    equiv-Cyclic-Type → type-Cyclic-Type k X → type-Cyclic-Type k Y
  map-equiv-Cyclic-Type e =
    map-equiv-Type-With-Endomorphism
      ( endo-Cyclic-Type k X)
      ( endo-Cyclic-Type k Y)
      ( e)

  coherence-square-equiv-Cyclic-Type :
    ( e : equiv-Cyclic-Type) →
    coherence-square-maps
      ( map-equiv-Cyclic-Type e)
      ( endomorphism-Cyclic-Type k X)
      ( endomorphism-Cyclic-Type k Y)
      ( map-equiv-Cyclic-Type e)
  coherence-square-equiv-Cyclic-Type e = pr2 e

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  id-equiv-Cyclic-Type : equiv-Cyclic-Type k X X
  id-equiv-Cyclic-Type = id-equiv-Type-With-Endomorphism (endo-Cyclic-Type k X)

  equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → X ＝ Y → equiv-Cyclic-Type k X Y
  equiv-eq-Cyclic-Type .X refl = id-equiv-Cyclic-Type

is-torsorial-equiv-Cyclic-Type :
  {l1 : Level} (k : ℕ) (X : Cyclic-Type l1 k) →
  is-torsorial (equiv-Cyclic-Type k X)
is-torsorial-equiv-Cyclic-Type k X =
  is-torsorial-Eq-subtype
    ( is-torsorial-equiv-Type-With-Endomorphism (endo-Cyclic-Type k X))
    ( λ Y → is-prop-type-trunc-Prop)
    ( endo-Cyclic-Type k X)
    ( id-equiv-Type-With-Endomorphism (endo-Cyclic-Type k X))
    ( mere-equiv-endo-Cyclic-Type k X)

module _
  {l : Level} (k : ℕ) (X : Cyclic-Type l k)
  where

  is-equiv-equiv-eq-Cyclic-Type :
    (Y : Cyclic-Type l k) → is-equiv (equiv-eq-Cyclic-Type k X Y)
  is-equiv-equiv-eq-Cyclic-Type =
    fundamental-theorem-id
      ( is-torsorial-equiv-Cyclic-Type k X)
      ( equiv-eq-Cyclic-Type k X)

  extensionality-Cyclic-Type :
    (Y : Cyclic-Type l k) → (X ＝ Y) ≃ equiv-Cyclic-Type k X Y
  pr1 (extensionality-Cyclic-Type Y) = equiv-eq-Cyclic-Type k X Y
  pr2 (extensionality-Cyclic-Type Y) = is-equiv-equiv-eq-Cyclic-Type Y

  eq-equiv-Cyclic-Type :
    (Y : Cyclic-Type l k) → equiv-Cyclic-Type k X Y → X ＝ Y
  eq-equiv-Cyclic-Type Y = map-inv-is-equiv (is-equiv-equiv-eq-Cyclic-Type Y)
```

## Properties

```agda
module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  where

  htpy-equiv-Cyclic-Type : (e f : equiv-Cyclic-Type k X Y) → UU (l1 ⊔ l2)
  htpy-equiv-Cyclic-Type e f =
    map-equiv-Cyclic-Type k X Y e ~ map-equiv-Cyclic-Type k X Y f

  refl-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e e
  refl-htpy-equiv-Cyclic-Type e = refl-htpy

  htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → e ＝ f → htpy-equiv-Cyclic-Type e f
  htpy-eq-equiv-Cyclic-Type e .e refl = refl-htpy-equiv-Cyclic-Type e

  is-torsorial-htpy-equiv-Cyclic-Type :
    (e : equiv-Cyclic-Type k X Y) → is-torsorial (htpy-equiv-Cyclic-Type e)
  is-torsorial-htpy-equiv-Cyclic-Type e =
    is-contr-equiv'
      ( Σ ( equiv-Type-With-Endomorphism
            ( endo-Cyclic-Type k X)
            ( endo-Cyclic-Type k Y))
          ( htpy-equiv-Type-With-Endomorphism
            ( endo-Cyclic-Type k X)
            ( endo-Cyclic-Type k Y)
            ( e)))
      ( equiv-tot
        ( λ f →
          right-unit-law-Σ-is-contr
            ( λ H →
              is-contr-Π
                ( λ x →
                  is-set-type-Cyclic-Type k Y
                  ( map-equiv-Cyclic-Type k X Y e
                    ( endomorphism-Cyclic-Type k X x))
                  ( endomorphism-Cyclic-Type k Y
                    ( map-equiv-Cyclic-Type k X Y f x))
                  ( ( H (endomorphism-Cyclic-Type k X x)) ∙
                    ( coherence-square-equiv-Cyclic-Type k X Y f x))
                  ( ( coherence-square-equiv-Cyclic-Type k X Y e x) ∙
                    ( ap (endomorphism-Cyclic-Type k Y) (H x)))))))
      ( is-torsorial-htpy-equiv-Type-With-Endomorphism
        ( endo-Cyclic-Type k X)
        ( endo-Cyclic-Type k Y)
        ( e))

  is-equiv-htpy-eq-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → is-equiv (htpy-eq-equiv-Cyclic-Type e f)
  is-equiv-htpy-eq-equiv-Cyclic-Type e =
    fundamental-theorem-id
      ( is-torsorial-htpy-equiv-Cyclic-Type e)
      ( htpy-eq-equiv-Cyclic-Type e)

  extensionality-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → (e ＝ f) ≃ htpy-equiv-Cyclic-Type e f
  pr1 (extensionality-equiv-Cyclic-Type e f) = htpy-eq-equiv-Cyclic-Type e f
  pr2 (extensionality-equiv-Cyclic-Type e f) =
    is-equiv-htpy-eq-equiv-Cyclic-Type e f

  eq-htpy-equiv-Cyclic-Type :
    (e f : equiv-Cyclic-Type k X Y) → htpy-equiv-Cyclic-Type e f → e ＝ f
  eq-htpy-equiv-Cyclic-Type e f =
    map-inv-equiv (extensionality-equiv-Cyclic-Type e f)

comp-equiv-Cyclic-Type :
  {l1 l2 l3 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) →
  equiv-Cyclic-Type k Y Z → equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k X Z
comp-equiv-Cyclic-Type k X Y Z =
  comp-equiv-Type-With-Endomorphism
    ( endo-Cyclic-Type k X)
    ( endo-Cyclic-Type k Y)
    ( endo-Cyclic-Type k Z)

inv-equiv-Cyclic-Type :
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k) →
  equiv-Cyclic-Type k X Y → equiv-Cyclic-Type k Y X
inv-equiv-Cyclic-Type k X Y =
  inv-equiv-Type-With-Endomorphism
    ( endo-Cyclic-Type k X)
    ( endo-Cyclic-Type k Y)

associative-comp-equiv-Cyclic-Type :
  {l1 l2 l3 l4 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (Z : Cyclic-Type l3 k) (W : Cyclic-Type l4 k) (g : equiv-Cyclic-Type k Z W)
  (f : equiv-Cyclic-Type k Y Z) (e : equiv-Cyclic-Type k X Y) →
  ( comp-equiv-Cyclic-Type
    k X Y W (comp-equiv-Cyclic-Type k Y Z W g f) e) ＝
  ( comp-equiv-Cyclic-Type
    k X Z W g (comp-equiv-Cyclic-Type k X Y Z f e))
associative-comp-equiv-Cyclic-Type k X Y Z W g f e =
  eq-htpy-equiv-Cyclic-Type k X W
    ( comp-equiv-Cyclic-Type
        k X Y W (comp-equiv-Cyclic-Type k Y Z W g f) e)
    ( comp-equiv-Cyclic-Type
        k X Z W g (comp-equiv-Cyclic-Type k X Y Z f e))
    ( refl-htpy)

module _
  {l1 l2 : Level} (k : ℕ) (X : Cyclic-Type l1 k) (Y : Cyclic-Type l2 k)
  (e : equiv-Cyclic-Type k X Y)
  where

  left-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X Y Y (id-equiv-Cyclic-Type k Y) e) e
  left-unit-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X Y
      ( comp-equiv-Cyclic-Type k X Y Y (id-equiv-Cyclic-Type k Y) e)
      ( e)
      ( refl-htpy)

  right-unit-law-comp-equiv-Cyclic-Type :
    Id (comp-equiv-Cyclic-Type k X X Y e (id-equiv-Cyclic-Type k X)) e
  right-unit-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X Y
      ( comp-equiv-Cyclic-Type k X X Y e (id-equiv-Cyclic-Type k X))
      ( e)
      ( refl-htpy)

  left-inverse-law-comp-equiv-Cyclic-Type :
    Id
      ( comp-equiv-Cyclic-Type k X Y X (inv-equiv-Cyclic-Type k X Y e) e)
      ( id-equiv-Cyclic-Type k X)
  left-inverse-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k X X
      ( comp-equiv-Cyclic-Type k X Y X (inv-equiv-Cyclic-Type k X Y e) e)
      ( id-equiv-Cyclic-Type k X)
      ( is-retraction-map-inv-equiv (equiv-equiv-Cyclic-Type k X Y e))

  right-inverse-law-comp-equiv-Cyclic-Type :
    Id
      ( comp-equiv-Cyclic-Type k Y X Y e (inv-equiv-Cyclic-Type k X Y e))
      ( id-equiv-Cyclic-Type k Y)
  right-inverse-law-comp-equiv-Cyclic-Type =
    eq-htpy-equiv-Cyclic-Type k Y Y
      ( comp-equiv-Cyclic-Type k Y X Y e (inv-equiv-Cyclic-Type k X Y e))
      ( id-equiv-Cyclic-Type k Y)
      ( is-section-map-inv-equiv (equiv-equiv-Cyclic-Type k X Y e))

mere-eq-Cyclic-Type : {l : Level} (k : ℕ) (X Y : Cyclic-Type l k) → mere-eq X Y
mere-eq-Cyclic-Type k X Y =
  apply-universal-property-trunc-Prop
    ( mere-equiv-endo-Cyclic-Type k X)
    ( mere-eq-Prop X Y)
    ( λ e →
      apply-universal-property-trunc-Prop
        ( mere-equiv-endo-Cyclic-Type k Y)
        ( mere-eq-Prop X Y)
        ( λ f →
          unit-trunc-Prop
            ( eq-equiv-Cyclic-Type k X Y
              ( comp-equiv-Cyclic-Type k X (ℤ-Mod-Cyclic-Type k) Y f
                ( inv-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X e)))))

is-0-connected-Cyclic-Type :
  (k : ℕ) → is-0-connected (Cyclic-Type lzero k)
is-0-connected-Cyclic-Type k =
  is-0-connected-mere-eq
    ( ℤ-Mod-Cyclic-Type k)
    ( mere-eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))

∞-group-Cyclic-Type :
  (k : ℕ) → ∞-Group (lsuc lzero)
pr1 (∞-group-Cyclic-Type k) = Cyclic-Type-Pointed-Type k
pr2 (∞-group-Cyclic-Type k) = is-0-connected-Cyclic-Type k

Eq-Cyclic-Type : (k : ℕ) → Cyclic-Type lzero k → UU lzero
Eq-Cyclic-Type k X = type-Cyclic-Type k X

refl-Eq-Cyclic-Type : (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)
refl-Eq-Cyclic-Type k = zero-ℤ-Mod k

Eq-equiv-Cyclic-Type :
  (k : ℕ) (X : Cyclic-Type lzero k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X → Eq-Cyclic-Type k X
Eq-equiv-Cyclic-Type k X e =
  map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X e (zero-ℤ-Mod k)

equiv-Eq-Cyclic-Type :
  (k : ℕ) → Eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) →
  equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)
pr1 (equiv-Eq-Cyclic-Type k x) = equiv-add-ℤ-Mod' k x
pr2 (equiv-Eq-Cyclic-Type k x) y = left-successor-law-add-ℤ-Mod k y x

is-section-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) ∘ equiv-Eq-Cyclic-Type k) ~ id
is-section-equiv-Eq-Cyclic-Type zero-ℕ x = left-unit-law-add-ℤ x
is-section-equiv-Eq-Cyclic-Type (succ-ℕ k) x = left-unit-law-add-Fin k x

preserves-pred-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) →
  (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (f ∘ pred-ℤ-Mod k) ~ (pred-ℤ-Mod k ∘ f)
preserves-pred-preserves-succ-map-ℤ-Mod k f H x =
  ( inv (is-retraction-pred-ℤ-Mod k (f (pred-ℤ-Mod k x)))) ∙
  ( ap
    ( pred-ℤ-Mod k)
    ( ( inv (H (pred-ℤ-Mod k x))) ∙
      ( ap f (is-section-pred-ℤ-Mod k x))))

compute-map-preserves-succ-map-ℤ-Mod' :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) → (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f) →
  (x : ℤ) → Id (add-ℤ-Mod k (mod-ℤ k x) (f (zero-ℤ-Mod k))) (f (mod-ℤ k x))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl zero-ℕ) =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (mod-neg-one-ℤ k)) ∙
  ( ( inv (is-left-add-neg-one-pred-ℤ-Mod k (f (zero-ℤ-Mod k)))) ∙
    ( ( ap (pred-ℤ-Mod k) (ap f (inv (mod-zero-ℤ k)))) ∙
      ( ( inv
          ( preserves-pred-preserves-succ-map-ℤ-Mod k f H (mod-ℤ k zero-ℤ))) ∙
        ( inv (ap f (preserves-predecessor-mod-ℤ k zero-ℤ))))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inl (succ-ℕ x)) =
  ( ap
    ( add-ℤ-Mod' k (f (zero-ℤ-Mod k)))
    ( preserves-predecessor-mod-ℤ k (inl x))) ∙
  ( ( left-predecessor-law-add-ℤ-Mod k (mod-ℤ k (inl x)) (f (zero-ℤ-Mod k))) ∙
    ( ( ap
        ( pred-ℤ-Mod k)
        ( compute-map-preserves-succ-map-ℤ-Mod' k f H (inl x))) ∙
      ( ( inv
          ( preserves-pred-preserves-succ-map-ℤ-Mod k f H (mod-ℤ k (inl x)))) ∙
        ( ap f (inv (preserves-predecessor-mod-ℤ k (inl x)))))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inl _)) =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (mod-zero-ℤ k)) ∙
  ( ( left-unit-law-add-ℤ-Mod k (f (zero-ℤ-Mod k))) ∙
    ( ap f (inv (mod-zero-ℤ k))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr zero-ℕ)) =
  ( ap-add-ℤ-Mod k (mod-one-ℤ k) (ap f (inv (mod-zero-ℤ k)))) ∙
  ( ( inv (is-left-add-one-succ-ℤ-Mod k (f (mod-ℤ k zero-ℤ)))) ∙
    ( ( inv (H (mod-ℤ k zero-ℤ))) ∙
      ( ap f (inv (preserves-successor-mod-ℤ k zero-ℤ)))))
compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr (succ-ℕ x))) =
  ( ap
    ( add-ℤ-Mod' k (f (zero-ℤ-Mod k)))
    ( preserves-successor-mod-ℤ k (inr (inr x)))) ∙
  ( ( left-successor-law-add-ℤ-Mod k
      ( mod-ℤ k (inr (inr x)))
      ( f (zero-ℤ-Mod k))) ∙
    ( ( ap
        ( succ-ℤ-Mod k)
        ( compute-map-preserves-succ-map-ℤ-Mod' k f H (inr (inr x)))) ∙
      ( ( inv (H (mod-ℤ k (inr (inr x))))) ∙
        ( ap f (inv (preserves-successor-mod-ℤ k (inr (inr x))))))))

compute-map-preserves-succ-map-ℤ-Mod :
  (k : ℕ) (f : ℤ-Mod k → ℤ-Mod k) (H : (f ∘ succ-ℤ-Mod k) ~ (succ-ℤ-Mod k ∘ f))
  (x : ℤ-Mod k) → Id (add-ℤ-Mod k x (f (zero-ℤ-Mod k))) (f x)
compute-map-preserves-succ-map-ℤ-Mod k f H x =
  ( ap (add-ℤ-Mod' k (f (zero-ℤ-Mod k))) (inv (is-section-int-ℤ-Mod k x))) ∙
  ( ( compute-map-preserves-succ-map-ℤ-Mod' k f H (int-ℤ-Mod k x)) ∙
    ( ap f (is-section-int-ℤ-Mod k x)))

is-retraction-equiv-Eq-Cyclic-Type :
  (k : ℕ) →
  (equiv-Eq-Cyclic-Type k ∘ Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k)) ~ id
is-retraction-equiv-Eq-Cyclic-Type k e =
  eq-htpy-equiv-Cyclic-Type k
    ( ℤ-Mod-Cyclic-Type k)
    ( ℤ-Mod-Cyclic-Type k)
    ( equiv-Eq-Cyclic-Type k (Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) e))
    ( e)
    ( compute-map-preserves-succ-map-ℤ-Mod
      ( k)
      ( map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k) e)
      ( coherence-square-equiv-Cyclic-Type
        ( k)
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( e)))

abstract
  is-equiv-Eq-equiv-Cyclic-Type :
    (k : ℕ) (X : Cyclic-Type lzero k) → is-equiv (Eq-equiv-Cyclic-Type k X)
  is-equiv-Eq-equiv-Cyclic-Type k X =
    apply-universal-property-trunc-Prop
      ( mere-eq-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) X)
      ( is-equiv-Prop (Eq-equiv-Cyclic-Type k X))
      ( λ where
        refl →
          is-equiv-is-invertible
            ( equiv-Eq-Cyclic-Type k)
            ( is-section-equiv-Eq-Cyclic-Type k)
            ( is-retraction-equiv-Eq-Cyclic-Type k))

equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) ≃ ℤ-Mod k
equiv-compute-Ω-Cyclic-Type k =
  ( pair
    ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))
    ( is-equiv-Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))) ∘e
  ( extensionality-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k))

map-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) → type-Ω (pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k)) → ℤ-Mod k
map-equiv-compute-Ω-Cyclic-Type k = map-equiv (equiv-compute-Ω-Cyclic-Type k)

preserves-concat-equiv-eq-Cyclic-Type :
  (k : ℕ) (X Y Z : Cyclic-Type lzero k) (p : X ＝ Y) (q : Y ＝ Z) →
  Id
    ( equiv-eq-Cyclic-Type k X Z (p ∙ q))
    ( comp-equiv-Cyclic-Type k X Y Z
      ( equiv-eq-Cyclic-Type k Y Z q)
      ( equiv-eq-Cyclic-Type k X Y p))
preserves-concat-equiv-eq-Cyclic-Type k X .X Z refl q =
  inv
    ( right-unit-law-comp-equiv-Cyclic-Type
        k X Z (equiv-eq-Cyclic-Type k X Z q))

preserves-comp-Eq-equiv-Cyclic-Type :
  (k : ℕ)
  (e f : equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)) →
  Id
    ( Eq-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( comp-equiv-Cyclic-Type k
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( ℤ-Mod-Cyclic-Type k)
        ( f)
        ( e)))
    ( add-ℤ-Mod k
      ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) e)
      ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) f))
preserves-comp-Eq-equiv-Cyclic-Type k e f =
  inv
  ( compute-map-preserves-succ-map-ℤ-Mod k
    ( map-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k) f)
    ( coherence-square-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( f))
    ( map-equiv-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( e)
      ( zero-ℤ-Mod k)))

preserves-concat-equiv-compute-Ω-Cyclic-Type :
  (k : ℕ) {p q : type-Ω (Cyclic-Type-Pointed-Type k)} →
  Id
    ( map-equiv (equiv-compute-Ω-Cyclic-Type k) (p ∙ q))
    ( add-ℤ-Mod k
      ( map-equiv (equiv-compute-Ω-Cyclic-Type k) p)
      ( map-equiv (equiv-compute-Ω-Cyclic-Type k) q))
preserves-concat-equiv-compute-Ω-Cyclic-Type k {p} {q} =
  ( ap
    ( Eq-equiv-Cyclic-Type k (ℤ-Mod-Cyclic-Type k))
    ( preserves-concat-equiv-eq-Cyclic-Type k
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( ℤ-Mod-Cyclic-Type k)
      ( p)
      ( q))) ∙
  ( preserves-comp-Eq-equiv-Cyclic-Type k
    ( equiv-eq-Cyclic-Type k ( ℤ-Mod-Cyclic-Type k) ( ℤ-Mod-Cyclic-Type k) p)
    ( equiv-eq-Cyclic-Type k ( ℤ-Mod-Cyclic-Type k) ( ℤ-Mod-Cyclic-Type k) q))

type-Ω-Cyclic-Type : (k : ℕ) → UU (lsuc lzero)
type-Ω-Cyclic-Type k = Id (ℤ-Mod-Cyclic-Type k) (ℤ-Mod-Cyclic-Type k)

is-set-type-Ω-Cyclic-Type : (k : ℕ) → is-set (type-Ω-Cyclic-Type k)
is-set-type-Ω-Cyclic-Type k =
  is-set-equiv
    ( ℤ-Mod k)
    ( equiv-compute-Ω-Cyclic-Type k)
    ( is-set-ℤ-Mod k)

concrete-group-Cyclic-Type :
  (k : ℕ) → Concrete-Group (lsuc lzero)
pr1 (concrete-group-Cyclic-Type k) = ∞-group-Cyclic-Type k
pr2 (concrete-group-Cyclic-Type k) = is-set-type-Ω-Cyclic-Type k

Ω-Cyclic-Type-Group : (k : ℕ) → Group (lsuc lzero)
Ω-Cyclic-Type-Group k =
  loop-space-Group
    ( pair (Cyclic-Type lzero k) (ℤ-Mod-Cyclic-Type k))
    ( is-set-type-Ω-Cyclic-Type k)

equiv-Ω-Cyclic-Type-Group :
  (k : ℕ) → equiv-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
pr1 (equiv-Ω-Cyclic-Type-Group k) = equiv-compute-Ω-Cyclic-Type k
pr2 (equiv-Ω-Cyclic-Type-Group k) {x} {y} =
  preserves-concat-equiv-compute-Ω-Cyclic-Type k {x} {y}

iso-Ω-Cyclic-Type-Group :
  (k : ℕ) → iso-Group (Ω-Cyclic-Type-Group k) (ℤ-Mod-Group k)
iso-Ω-Cyclic-Type-Group k =
  iso-equiv-Group
    ( Ω-Cyclic-Type-Group k)
    ( ℤ-Mod-Group k)
    ( equiv-Ω-Cyclic-Type-Group k)
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
