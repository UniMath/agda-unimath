# Premetric structures on types

```agda
module metric-spaces.premetric-structures where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "premetric" Disambiguation="structure on a type" Agda=Premetric}}
is a type family of
[proposition-valued binary relations](foundation.binary-relations.md) indexed by
the
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md).

This follows Definition 4.5.2 from {{#cite Booij2020PhD}}.

## Definitions

### Premetric structures

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  Premetric : UU (l1 ⊔ lsuc l2)
  Premetric = ℚ⁺ → Relation-Prop l2 A
```

### Closeness relation in a premetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  neighborhood-Premetric : ℚ⁺ → A → A → UU l2
  neighborhood-Premetric d = type-Relation-Prop (B d)

  is-prop-neighborhood-Premetric :
    (d : ℚ⁺) (x y : A) → is-prop (neighborhood-Premetric d x y)
  is-prop-neighborhood-Premetric d = is-prop-type-Relation-Prop (B d)
```

### Two points `x` and `y` are indistinguishable in a premetric if `x` and `y` are `d`-neighbours for any positive rational `d`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-indistinguishable-prop-Premetric : Prop l2
  is-indistinguishable-prop-Premetric =
    Π-Prop ℚ⁺ (λ (d : ℚ⁺) → B d x y)

  is-indistinguishable-Premetric : UU l2
  is-indistinguishable-Premetric =
    type-Prop is-indistinguishable-prop-Premetric

  is-prop-is-indistinguishable-Premetric :
    is-prop is-indistinguishable-Premetric
  is-prop-is-indistinguishable-Premetric =
    is-prop-type-Prop is-indistinguishable-prop-Premetric
```

### Two points `x` and `y` are separated in a premetric if there exists some positive rational `d` such that `x` and `y` are not `d`-neighbours

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-separated-pt-prop-Premetric : Prop l2
  is-separated-pt-prop-Premetric =
    ∃ ℚ⁺ (λ d → neg-Prop (B d x y))

  is-separated-pt-Premetric : UU l2
  is-separated-pt-Premetric =
    type-Prop is-separated-pt-prop-Premetric

  is-prop-is-separated-pt-Premetric :
    is-prop is-separated-pt-Premetric
  is-prop-is-separated-pt-Premetric =
    is-prop-type-Prop is-separated-pt-prop-Premetric
```

## Properties

### Points separated by a premetric structure are not indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (x y : A)
  where

  is-not-indistinguishable-is-separated-pt-Premetric :
    is-separated-pt-Premetric B x y → ¬ (is-indistinguishable-Premetric B x y)
  is-not-indistinguishable-is-separated-pt-Premetric S I =
    elim-exists
      ( empty-Prop)
      ( λ d H → H (I d))
      ( S)
```

### A premetric is reflexive if any element is indistinguishable from itself

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-reflexive-prop-Premetric : Prop (l1 ⊔ l2)
  is-reflexive-prop-Premetric =
    Π-Prop ℚ⁺ (is-reflexive-prop-Relation-Prop ∘ B)

  is-reflexive-Premetric : UU (l1 ⊔ l2)
  is-reflexive-Premetric = type-Prop is-reflexive-prop-Premetric

  is-prop-is-reflexive-Premetric : is-prop is-reflexive-Premetric
  is-prop-is-reflexive-Premetric =
    is-prop-type-Prop is-reflexive-prop-Premetric
```

### Indistiguishability in a reflexive premetric is reflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B)
  where

  is-reflexive-is-indistinguishable-reflexive-Premetric :
    is-reflexive (is-indistinguishable-Premetric B)
  is-reflexive-is-indistinguishable-reflexive-Premetric x d = R d x
```

### In a reflexive premetric, equal elements are indistinguishable

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (H : is-reflexive-Premetric B)
  where

  indistinguishable-eq-reflexive-Premetric :
    {x y : A} → x ＝ y → is-indistinguishable-Premetric B x y
  indistinguishable-eq-reflexive-Premetric {x} {.x} refl d = H d x
```

### Being separated in a reflexive premetric is irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B)
  where

  is-irreflexive-is-separated-pt-is-reflexive-Premetric :
    (x : A) → ¬ (is-separated-pt-Premetric B x x)
  is-irreflexive-is-separated-pt-is-reflexive-Premetric x =
    elim-exists
      ( empty-Prop)
      ( λ d H → H (R d x))
```

### A premetric is symmetric if `d`-neighbourhoods are symmetric for all positive rational number `d`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-symmetric-prop-Premetric : Prop (l1 ⊔ l2)
  is-symmetric-prop-Premetric =
    Π-Prop ℚ⁺ (is-symmetric-prop-Relation-Prop ∘ B)

  is-symmetric-Premetric : UU (l1 ⊔ l2)
  is-symmetric-Premetric = type-Prop is-symmetric-prop-Premetric

  is-prop-is-symmetric-Premetric : is-prop is-symmetric-Premetric
  is-prop-is-symmetric-Premetric =
    is-prop-type-Prop is-symmetric-prop-Premetric
```

### Indistiguishability in a symmetric premetric is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (S : is-symmetric-Premetric B)
  where

  is-symmetric-is-indistinguishable-is-symmetric-Premetric :
    is-symmetric (is-indistinguishable-Premetric B)
  is-symmetric-is-indistinguishable-is-symmetric-Premetric x y H d =
    S d x y (H d)
```

### Being separated in a symmetric premetric is symmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (S : is-symmetric-Premetric B)
  where

  is-symmetric-is-separated-pt-is-symmetric-Premetric :
    is-symmetric (is-separated-pt-Premetric B)
  is-symmetric-is-separated-pt-is-symmetric-Premetric x y =
    elim-exists
      ( is-separated-pt-prop-Premetric B y x)
      ( λ d I → intro-exists d (I ∘ S d y x))
```

### A premetric is local if indistinguishability has propositional fibers

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-local-prop-Premetric : Prop (l1 ⊔ l2)
  is-local-prop-Premetric =
    Π-Prop A (is-prop-Prop ∘ Σ A ∘ is-indistinguishable-Premetric B)

  is-local-Premetric : UU (l1 ⊔ l2)
  is-local-Premetric = type-Prop is-local-prop-Premetric

  is-prop-is-local-Premetric : is-prop is-local-Premetric
  is-prop-is-local-Premetric = is-prop-type-Prop is-local-prop-Premetric
```

### In a local reflexive premetric, indistinguishability is torsorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B) (x : A)
  where

  is-torsorial-indistinguishable-local-reflexive-Premetric :
    is-torsorial (is-indistinguishable-Premetric B x)
  is-torsorial-indistinguishable-local-reflexive-Premetric =
    is-proof-irrelevant-is-prop (L x) (x , λ d → R d x)

  is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric :
    (y : A) → is-equiv (indistinguishable-eq-reflexive-Premetric B R)
  is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric =
    fundamental-theorem-id
      ( is-torsorial-indistinguishable-local-reflexive-Premetric)
      ( λ y → indistinguishable-eq-reflexive-Premetric B R {x} {y})
```

### Any type equipped with a reflexive local premetric is a set

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B)
  where

  is-set-has-local-reflexive-Premetric : is-set A
  is-set-has-local-reflexive-Premetric x y =
    is-prop-is-equiv
      ( is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric
        B
        R
        L
        x
        y)
      ( is-prop-is-indistinguishable-Premetric B x y)
```

### A premetric is tight if any two indistinguishable elements are equal

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-tight-Premetric : UU (l1 ⊔ l2)
  is-tight-Premetric =
    (x y : A) → is-indistinguishable-Premetric B x y → x ＝ y
```

### Any tight premetric is local

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-tight-Premetric B)
  where

  is-local-is-tight-Premetric : is-local-Premetric B
  is-local-is-tight-Premetric x =
    is-prop-all-elements-equal
      ( λ (u , I) (v , J) →
        eq-type-subtype
          ( is-indistinguishable-prop-Premetric B x)
          ( inv (T x u I) ∙ T x v J))
```

### Any reflexive local premetric is tight

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (L : is-local-Premetric B)
  where

  is-tight-is-local-reflexive-Premetric : is-tight-Premetric B
  is-tight-is-local-reflexive-Premetric x =
    ( map-inv-is-equiv) ∘
    ( is-fiberwise-equiv-indistinguishable-local-reflexive-Premetric B R L x)
```

### A premetric is monotonic if any `d₁`-neighbourhoods are `d₂`-neighbourhoods for `d₁ < d₂`

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-monotonic-prop-Premetric : Prop (l1 ⊔ l2)
  is-monotonic-prop-Premetric =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( ℚ⁺)
              ( λ d₁ →
                ( Π-Prop
                  ( ℚ⁺)
                  ( λ d₂ →
                    ( Π-Prop
                      ( le-ℚ⁺ d₁ d₂)
                      ( λ H →
                        hom-Prop (B d₁ x y) (B d₂ x y))))))))))

  is-monotonic-Premetric : UU (l1 ⊔ l2)
  is-monotonic-Premetric = type-Prop is-monotonic-prop-Premetric

  is-prop-is-monotonic-Premetric : is-prop is-monotonic-Premetric
  is-prop-is-monotonic-Premetric = is-prop-type-Prop is-monotonic-prop-Premetric
```

### A premetric is triangular if it is additively transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  where

  is-triangular-prop-Premetric : Prop (l1 ⊔ l2)
  is-triangular-prop-Premetric =
    Π-Prop
      ( A)
      ( λ x →
        ( Π-Prop
          ( A)
          ( λ y →
            ( Π-Prop
              ( A)
              ( λ z →
                Π-Prop
                  ( ℚ⁺)
                  ( λ d₁ →
                    ( Π-Prop
                      ( ℚ⁺)
                      ( λ d₂ →
                        hom-Prop
                          ( B d₂ y z)
                          ( hom-Prop
                            ( B d₁ x y)
                            ( B (d₁ +ℚ⁺ d₂) x z))))))))))

  is-triangular-Premetric : UU (l1 ⊔ l2)
  is-triangular-Premetric = type-Prop is-triangular-prop-Premetric

  is-prop-is-triangular-Premetric : is-prop is-triangular-Premetric
  is-prop-is-triangular-Premetric =
    is-prop-type-Prop is-triangular-prop-Premetric
```

### Indistiguishability in a triangular premetric is transitive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (T : is-triangular-Premetric B)
  where

  is-transitive-is-indistinguishable-triangular-Premetric :
    is-transitive (is-indistinguishable-Premetric B)
  is-transitive-is-indistinguishable-triangular-Premetric x y z H K d =
    tr
      ( λ h → neighborhood-Premetric B h x z)
      ( eq-add-split-ℚ⁺ d)
      ( T
        ( x)
        ( y)
        ( z)
        ( left-summand-split-ℚ⁺ d)
        ( right-summand-split-ℚ⁺ d)
        ( H (right-summand-split-ℚ⁺ d))
        ( K (left-summand-split-ℚ⁺ d)))
```

### Any triangular reflexive premetric is monotonic

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : Premetric l2 A)
  (R : is-reflexive-Premetric B) (T : is-triangular-Premetric B)
  where

  is-monotonic-is-reflexive-triangular-Premetric : is-monotonic-Premetric B
  is-monotonic-is-reflexive-triangular-Premetric x y d₁ d₂ I H₁ =
    tr
      ( λ d → neighborhood-Premetric B d x y)
      ( right-diff-law-add-ℚ⁺ d₁ d₂ I)
      ( T x y y d₁ (le-diff-ℚ⁺ d₁ d₂ I) (R (le-diff-ℚ⁺ d₁ d₂ I) y) H₁)
```

### Two premetrics on a type are equal if they define the same neighbourhoods

```agda
module _
  {l1 l2 : Level} {A : UU l1} (N : Premetric l2 A)
  where

  Eq-prop-Premetric : Premetric l2 A → Prop (l1 ⊔ l2)
  Eq-prop-Premetric N' =
    Π-Prop
      ( ℚ⁺)
      ( λ d →
        Π-Prop
          ( A)
          ( λ x →
            Π-Prop
              ( A)
              ( λ y → N d x y ⇔ N' d x y)))

  Eq-Premetric : Premetric l2 A → UU (l1 ⊔ l2)
  Eq-Premetric N' = type-Prop (Eq-prop-Premetric N')

  is-prop-Eq-Premetric : (N' : Premetric l2 A) → is-prop (Eq-Premetric N')
  is-prop-Eq-Premetric N' = is-prop-type-Prop (Eq-prop-Premetric N')

  refl-Eq-Premetric : Eq-Premetric N
  refl-Eq-Premetric d x y = id-iff

  Eq-eq-Premetric : (N' : Premetric l2 A) → (N ＝ N') → Eq-Premetric N'
  Eq-eq-Premetric .N refl = refl-Eq-Premetric

  eq-Eq-Premetric : (N' : Premetric l2 A) → Eq-Premetric N' → N ＝ N'
  eq-Eq-Premetric N' H =
    eq-htpy
      ( λ d →
        eq-htpy
        ( λ x →
          eq-htpy
          ( λ y →
            eq-iff' (N d x y) (N' d x y) (H d x y))))

  is-torsorial-Eq-Premetric : is-torsorial Eq-Premetric
  is-torsorial-Eq-Premetric =
    ( N , refl-Eq-Premetric) ,
    ( λ (N' , e) →
      eq-type-subtype
        ( Eq-prop-Premetric)
        ( eq-Eq-Premetric N' e))

  is-fiberwise-equiv-Eq-eq-Premetric :
    (N' : Premetric l2 A) → is-equiv (Eq-eq-Premetric N')
  is-fiberwise-equiv-Eq-eq-Premetric =
    fundamental-theorem-id is-torsorial-Eq-Premetric Eq-eq-Premetric

  equiv-Eq-eq-Premetric :
    (N' : Premetric l2 A) → (N ＝ N') ≃ (Eq-Premetric N')
  equiv-Eq-eq-Premetric N' =
    Eq-eq-Premetric N' , is-fiberwise-equiv-Eq-eq-Premetric N'
```

### Characterisation of the transport of premetric structures along equality of types

```agda
module _
  {l1 l2 : Level} (A : UU l1)
  where

  eq-map-eq-tr-Premetric :
    (B : UU l1) (e : A ＝ B) (S : Premetric l2 A) →
    Eq-Premetric S (λ d x y → tr (Premetric l2) e S d (map-eq e x) (map-eq e y))
  eq-map-eq-tr-Premetric .A refl S = refl-Eq-Premetric S

  eq-map-inv-eq-tr-Premetric :
    (B : UU l1) (e : A ＝ B) (S : Premetric l2 A) →
    Eq-Premetric
      (tr (Premetric l2) e S)
      (λ d x y → S d (map-inv-eq e x) (map-inv-eq e y))
  eq-map-inv-eq-tr-Premetric .A refl S = refl-Eq-Premetric S
```

## References

{{#bibliography}}

## See also

- [Booij premetric spaces](https://ncatlab.org/nlab/show/Booij+premetric+space)
  at $n$Lab.
