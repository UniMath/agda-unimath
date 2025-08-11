# Subfinite indexing

```agda
module univalent-combinatorics.subfinite-indexing where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.minimum-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.propositional-maps
open import foundation.repetitions-of-values
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.dedekind-finite-types
open import univalent-combinatorics.finite-choice
open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.subcounting
```

</details>

## Idea

A {{#concept "subfinite indexing" Agda=subfinite-indexing}} of a type `X` is the
data of a type `D` [equipped](foundation.structure.md) with a
[subcounting](univalent-combinatorics.subcounting.md) `D ↪ Fin n` and a
[surjection](foundation.surjective-maps.md) `D ↠ X`.

## Definitions

```agda
subfinite-indexing : {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
subfinite-indexing l2 X = Σ (UU l2) (λ D → (subcount D) × (D ↠ X))

module _
  {l1 l2 : Level} {X : UU l1} (e : subfinite-indexing l2 X)
  where

  indexing-type-subfinite-indexing : UU l2
  indexing-type-subfinite-indexing = pr1 e

  subcount-indexing-type-subfinite-indexing :
    subcount indexing-type-subfinite-indexing
  subcount-indexing-type-subfinite-indexing = pr1 (pr2 e)

  is-set-indexing-type-subfinite-indexing :
    is-set indexing-type-subfinite-indexing
  is-set-indexing-type-subfinite-indexing =
    is-set-has-subcount subcount-indexing-type-subfinite-indexing

  indexing-set-subfinite-indexing : Set l2
  indexing-set-subfinite-indexing =
    ( indexing-type-subfinite-indexing ,
      is-set-indexing-type-subfinite-indexing)

  bound-number-of-elements-subfinite-indexing : ℕ
  bound-number-of-elements-subfinite-indexing =
    bound-number-of-elements-subcount subcount-indexing-type-subfinite-indexing

  emb-subfinite-indexing :
    indexing-type-subfinite-indexing ↪
    Fin bound-number-of-elements-subfinite-indexing
  emb-subfinite-indexing =
    emb-subcount subcount-indexing-type-subfinite-indexing

  map-emb-subfinite-indexing :
    indexing-type-subfinite-indexing →
    Fin bound-number-of-elements-subfinite-indexing
  map-emb-subfinite-indexing =
    map-subcount subcount-indexing-type-subfinite-indexing

  is-emb-map-emb-subfinite-indexing :
    is-emb map-emb-subfinite-indexing
  is-emb-map-emb-subfinite-indexing =
    is-emb-map-subcount subcount-indexing-type-subfinite-indexing

  is-injective-map-emb-subfinite-indexing :
    is-injective map-emb-subfinite-indexing
  is-injective-map-emb-subfinite-indexing =
    is-injective-map-subcount subcount-indexing-type-subfinite-indexing

  surjection-subfinite-indexing :
    indexing-type-subfinite-indexing ↠ X
  surjection-subfinite-indexing = pr2 (pr2 e)

  map-surjection-subfinite-indexing :
    indexing-type-subfinite-indexing → X
  map-surjection-subfinite-indexing =
    map-surjection surjection-subfinite-indexing

  is-surjective-map-surjection-subfinite-indexing :
    is-surjective map-surjection-subfinite-indexing
  is-surjective-map-surjection-subfinite-indexing =
    is-surjective-map-surjection surjection-subfinite-indexing
```

## Properties

### Types with subcountings have subfinite indexings

```agda
subfinite-indexing-subcount :
  {l : Level} {X : UU l} → subcount X → subfinite-indexing l X
subfinite-indexing-subcount {X = X} e = (X , e , id-surjection)
```

### Types equipped with subfinite indexings are closed under surjections

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where

  subfinite-indexing-surjection :
    X ↠ Y → subfinite-indexing l3 X → subfinite-indexing l3 Y
  subfinite-indexing-surjection s (D , e , t) = (D , e , comp-surjection s t)
```

### Types equipped with subfinite indexings are closed under retracts

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where

  subfinite-indexing-retract-of :
    Y retract-of X → subfinite-indexing l3 X → subfinite-indexing l3 Y
  subfinite-indexing-retract-of R =
    subfinite-indexing-surjection
      ( map-retraction-retract R ,
        is-surjective-has-section (section-retract R))
```

### Types equipped with subfinite indexings are closed under equivalences

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  where

  subfinite-indexing-equiv :
    Y ≃ X → subfinite-indexing l3 X → subfinite-indexing l3 Y
  subfinite-indexing-equiv e =
    subfinite-indexing-retract-of (retract-equiv e)

  subfinite-indexing-equiv' :
    X ≃ Y → subfinite-indexing l3 X → subfinite-indexing l3 Y
  subfinite-indexing-equiv' e =
    subfinite-indexing-retract-of (retract-inv-equiv e)
```

### Types equipped with subfinite indexings are closed under subtypes

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} (P : subtype l2 X)
  (f : subfinite-indexing l3 X)
  where

  indexing-subtype-subfinite-indexing-subtype :
    subtype l2 (indexing-type-subfinite-indexing f)
  indexing-subtype-subfinite-indexing-subtype d =
    P (map-surjection-subfinite-indexing f d)

  indexing-type-subfinite-indexing-subtype : UU (l2 ⊔ l3)
  indexing-type-subfinite-indexing-subtype =
    type-subtype indexing-subtype-subfinite-indexing-subtype

  bound-number-of-elements-subfinite-indexing-subtype : ℕ
  bound-number-of-elements-subfinite-indexing-subtype =
    bound-number-of-elements-subfinite-indexing f

  emb-subfinite-indexing-subtype :
    indexing-type-subfinite-indexing-subtype ↪
    Fin bound-number-of-elements-subfinite-indexing-subtype
  emb-subfinite-indexing-subtype =
    comp-emb
      ( emb-subfinite-indexing f)
      ( emb-subtype indexing-subtype-subfinite-indexing-subtype)

  subcount-subfinite-indexing-subtype :
    subcount indexing-type-subfinite-indexing-subtype
  subcount-subfinite-indexing-subtype =
    ( bound-number-of-elements-subfinite-indexing-subtype ,
      emb-subfinite-indexing-subtype)

  map-surjection-subfinite-indexing-subtype :
    indexing-type-subfinite-indexing-subtype → type-subtype P
  map-surjection-subfinite-indexing-subtype (d , p) =
    (map-surjection-subfinite-indexing f d , p)

  abstract
    is-surjective-map-surjection-subfinite-indexing-subtype :
      is-surjective map-surjection-subfinite-indexing-subtype
    is-surjective-map-surjection-subfinite-indexing-subtype (x , p) =
      map-trunc-Prop
        ( λ where (y , refl) → ((y , p) , refl))
        ( is-surjective-map-surjection-subfinite-indexing f x)

  surjection-subfinite-indexing-subtype :
    indexing-type-subfinite-indexing-subtype ↠ type-subtype P
  surjection-subfinite-indexing-subtype =
    ( map-surjection-subfinite-indexing-subtype ,
      is-surjective-map-surjection-subfinite-indexing-subtype)

  subfinite-indexing-subtype : subfinite-indexing (l2 ⊔ l3) (type-subtype P)
  subfinite-indexing-subtype =
    ( indexing-type-subfinite-indexing-subtype ,
      subcount-subfinite-indexing-subtype ,
      surjection-subfinite-indexing-subtype)
```

### Types equipped with subfinite indexings are closed under embeddings

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (e : Y ↪ X)
  (f : subfinite-indexing l3 X)
  where

  subfinite-indexing-emb : subfinite-indexing (l1 ⊔ l2 ⊔ l3) Y
  subfinite-indexing-emb =
    subfinite-indexing-equiv'
      ( equiv-total-fiber (map-emb e))
      ( subfinite-indexing-subtype (fiber-emb-Prop e) f)
```

### A type has a subfinite indexing if and only if it is a subtype of a type with a finite indexing

**Proof.** Given a subfinite indexing on `X`, we may form the
[pushout](synthetic-homotopy-theory.pushouts.md)

```text
  D ╰──────→ Fin n
  │            │
  │            │
  ↡          ⌜ ↓
  X ─────────→ D'.
```

Since surjective maps are the left class of an orthogonal factorization system
they are stable under cobase change, so the right vertical map is surjective.
And by Proposition 2.2.6 of {{#cite ABFJ20}} the pushout of an embedding is an
embedding, so the bottom horizontal map is an embedding.

Conversely, given a subtype of a type with a finite indexing, we may form the
[pullback](foundation-core.pullbacks.md)

```text
  D' ──────→ Fin n
  │ ⌟          │
  │            │
  ↓            ↡
  X ╰────────→ D.
```

Embeddings are closed under pullbacks since it is characterized as the right
class of an orthogonal factorization system, and since this orthogonal
factorization system is stable, so are the surjections. ■

> This remains to be formalized.

### Types equipped with subfinite indexings are Dedekind finite

We reproduce a proof given by
[Gro-Tsen](https://mathoverflow.net/users/17064/gro-tsen) in this MathOverflow
answer: <https://mathoverflow.net/a/433318>.

**Proof.** Let $X$ be a subfinitely enumerable type, witnessed by
$Fin n ↩ D ↠ X$ where $h$ is the surjection. We wish to show $X$ is Dedekind
finite, so let $f : X ↪ X$ be an arbitrary self-embedding. To conclude $f$ is an
equivalence it suffices to prove $f$ is surjective, so assume given an arbitrary
$x : X$ where we want to show there exists $z : X$ such that $f(z) ＝ x$.

The mapping $i ↦ fⁱ(x)$ defines a sequence of elements of $X$. By surjectivity
of $h$ each $fⁱ(x)$ merely has a representative in $D$, so by
[finite choice](univalent-combinatorics.finite-choice.md) there exists a
sequence $x₋ :  D^{\operatorname{Fin}n}$ lifting $x,f(x),…,f^{n-1}(x)$.

Now, the standard pigeonhole principle applies to $\operatorname{Fin}n$, so
there has to be $i < j$ in $\operatorname{Fin}n$ such that $xᵢ = xⱼ$, and in
particular $h(xᵢ) = h(xⱼ)$, i.e., $fⁱ(x) = fʲ(x)$. By injectivity of $f$ we can
cancel $i$ applications to obtain $x = f(f^{j-i-1}(x))$, and so $f^{j-i-1}(x)$
is the desired preimage. ∎

```agda
module _
  {l1 l2 : Level} {X : UU l1} (c : subfinite-indexing l2 X)
  where

  abstract
    is-surjective-is-injective-endo-subfinite-indexing :
      (f : X → X) → is-injective f → is-surjective f
    is-surjective-is-injective-endo-subfinite-indexing f F x =
      map-trunc-Prop
        ( lemma-is-surjective-is-injective-endo-subfinite-indexing f F x)
        ( finite-choice-Fin
          ( succ-ℕ (bound-number-of-elements-subfinite-indexing c))
          ( λ i →
            is-surjective-map-surjection-subfinite-indexing c
              ( iterate
                ( nat-Fin
                  ( succ-ℕ (bound-number-of-elements-subfinite-indexing c))
                  ( i))
                ( f)
                ( x))))
      where abstract
        lemma-is-surjective-is-injective-endo-subfinite-indexing :
          (f : X → X) →
          is-injective f →
          (x : X) →
          ((i : Fin (succ-ℕ (bound-number-of-elements-subfinite-indexing c))) →
          fiber
            ( map-surjection-subfinite-indexing c)
            ( iterate
              ( nat-Fin
                ( succ-ℕ (bound-number-of-elements-subfinite-indexing c)) i)
              ( f)
              ( x))) →
          fiber f x
        lemma-is-surjective-is-injective-endo-subfinite-indexing
          f is-injective-f x hy =
          ( iterate k f x , compute-iterate-dist-f-x)
          where abstract
            y :
              Fin (succ-ℕ (bound-number-of-elements-subfinite-indexing c)) →
              indexing-type-subfinite-indexing c
            y = pr1 ∘ hy

            r : repetition-of-values y
            r =
              repetition-of-values-right-factor'
                ( is-injective-emb (emb-subfinite-indexing c))
                ( repetition-of-values-Fin-succ-to-Fin
                  ( bound-number-of-elements-subfinite-indexing c)
                  ( map-emb-subfinite-indexing c ∘ y))

            i : ℕ
            i =
              nat-Fin
                ( succ-ℕ (bound-number-of-elements-subfinite-indexing c))
                ( first-repetition-of-values y r)

            j : ℕ
            j =
              nat-Fin
                ( succ-ℕ (bound-number-of-elements-subfinite-indexing c))
                ( second-repetition-of-values y r)

            k+1-nonzero : ℕ⁺
            k+1-nonzero =
              ( dist-ℕ i j ,
                dist-neq-ℕ i j
                  ( distinction-repetition-of-values y r ∘
                    is-injective-nat-Fin
                      ( succ-ℕ
                        ( bound-number-of-elements-subfinite-indexing c))))

            k : ℕ
            k = pred-ℕ⁺ k+1-nonzero

            compute-succ-k : succ-ℕ k ＝ dist-ℕ i j
            compute-succ-k = ap pr1 (is-section-succ-nonzero-ℕ' k+1-nonzero)

            compute-iterate-f-x : iterate i f x ＝ iterate j f x
            compute-iterate-f-x =
              inv (pr2 (hy (first-repetition-of-values y r))) ∙
              ap
                ( map-surjection-subfinite-indexing c)
                ( is-repetition-of-values-repetition-of-values y r) ∙
              pr2 (hy (second-repetition-of-values y r))

            compute-iterate-min-max-f-x :
              iterate (max-ℕ i j) f x ＝ iterate (min-ℕ i j) f x
            compute-iterate-min-max-f-x =
              eq-value-min-max-eq-value-sequence
                ( λ u → iterate u f x)
                ( i)
                ( j)
                ( compute-iterate-f-x)

            compute-iterate-dist-f-x : f (iterate k f x) ＝ x
            compute-iterate-dist-f-x =
              compute-iterate-offset f is-injective-f
                ( min-ℕ i j)
                ( k)
                ( ( ap
                    ( λ u → iterate u f x)
                    ( ( inv (left-successor-law-add-ℕ k (min-ℕ i j))) ∙
                      ( ap (_+ℕ min-ℕ i j) compute-succ-k) ∙
                      ( eq-max-dist-min-ℕ i j))) ∙
                  ( compute-iterate-min-max-f-x))

  is-dedekind-finite-subfinite-indexing : is-dedekind-finite X
  is-dedekind-finite-subfinite-indexing f is-emb-f =
    is-equiv-is-emb-is-surjective
      ( is-surjective-is-injective-endo-subfinite-indexing f
        ( is-injective-is-emb is-emb-f))
      ( is-emb-f)
```

## References

{{#bibliograhy}}

## See also

- [Subfinitely enumerable types](univalent-combinatorics.subfinitely-enumerable-types.md)
