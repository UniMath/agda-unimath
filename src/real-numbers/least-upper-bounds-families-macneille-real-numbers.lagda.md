# Least upper bounds of families of MacNeille real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.least-upper-bounds-families-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import logic.double-negation-elimination
open import logic.functoriality-existential-quantification

open import order-theory.least-upper-bounds-large-posets
open import order-theory.upper-bounds-large-posets

open import real-numbers.inequality-lower-dedekind-real-numbers
open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.macneille-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.upper-bounds-families-macneille-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

A
{{#concept "least upper bound" Disambiguation="on a family of MacNeille real numbers" Agda=is-least-upper-bound-family-of-elements-macneille-ℝ}}
on a family of [MacNeille real numbers](real-numbers.macneille-real-numbers.md)
`y : I → ℝ` is a MacNeille real number `x` such that any MacNeille real number
`u` is greater than `x` [if and only if](foundation.logical-equivalences.md) for
all `i` we have `yᵢ ≤ u`. In other words, it is a
[least upper bound](order-theory.least-upper-bounds-large-posets.md) in the
[ordering on the MacNeille reals](real-numbers.inequality-macneille-real-numbers.md).

All inhabited upper bounded families of MacNeille real numbers have a least
upper bound.

## Definitions

```agda
is-least-upper-bound-family-of-elements-macneille-ℝ :
  {l1 l2 l3 : Level} {I : UU l1} → (I → macneille-ℝ l2) → macneille-ℝ l3 → UUω
is-least-upper-bound-family-of-elements-macneille-ℝ =
  is-least-upper-bound-family-of-elements-Large-Poset large-poset-macneille-ℝ

has-least-upper-bound-family-of-elements-macneille-ℝ :
  {l1 l2 : Level} (l3 : Level) → {I : UU l1} → (I → macneille-ℝ l2) → UUω
has-least-upper-bound-family-of-elements-macneille-ℝ l3 =
  has-least-upper-bound-family-of-elements-Large-Poset l3
    ( large-poset-macneille-ℝ)
```

## Properties

### Least upper bounds of inhabited bounded families

Every inhabited upper bounded family of MacNeille real numbers has a least upper
bound. This is referred to as the _conditional order completeness_ of the
MacNeille real numbers. We follow the construction in Lemma D4.7.7
{{#cite Johnstone02}}.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1}
  (H : is-inhabited I)
  (y : I → macneille-ℝ l2)
  (u : macneille-ℝ l3)
  (y≤u : is-upper-bound-family-of-elements-macneille-ℝ y u)
  where
```

Let

$$
  A ≔ \{\,p : ℚ \mid ∀(i : I),\; p ∈ U_{y_i}\,\},
$$

where $U_{y_i}$ is the upper cut of $y_i$. In Agda this is
`all-upper-sections-family-macneille-ℝ`.

The candidate upper cut of the least upper bound is then

$$
  (q ∈ U_{\sup y}) ≔ (∃(p : ℚ),\; (p ≤ q) ∧ (p ∈ A)).
$$

```agda
  all-upper-sections-family-macneille-ℝ : subtype (l1 ⊔ l2) ℚ
  all-upper-sections-family-macneille-ℝ p =
    Π-Prop I (λ i → upper-cut-macneille-ℝ (y i) p)

  upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    subtype (l1 ⊔ l2) ℚ
  upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q =
    ∃ ℚ (λ p → le-ℚ-Prop p q ∧ all-upper-sections-family-macneille-ℝ p)

  is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    ℚ → UU (l1 ⊔ l2)
  is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
    is-in-subtype
      ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

If $q ∈ U_{\sup y}$, then by definition there is $p ≤ q$ with $p ∈ U_{y_i}$ for
all $i$. By upward closure of upper cuts, this implies $q ∈ U_{y_i}$ for all
$i$.

```agda
  abstract
    is-in-all-upper-sections-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q →
      is-in-subtype all-upper-sections-family-macneille-ℝ q
    is-in-all-upper-sections-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      elim-exists
        ( all-upper-sections-family-macneille-ℝ q)
        ( λ p (p<q , p∈all) i →
          is-in-cut-le-ℚ-upper-ℝ
            ( upper-real-macneille-ℝ (y i))
            ( p)
            ( q)
            ( p<q)
            ( p∈all i))

  abstract
    is-in-cut-upper-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (i : I) (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q →
      is-in-upper-cut-macneille-ℝ (y i) q
    is-in-cut-upper-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      i q q∈U =
      is-in-all-upper-sections-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        q q∈U i
```

To show that $U_{\sup y}$ is inhabited, we use the given upper bound $u$: choose
$q ∈ U_u$, then choose $r > q$. Since each $y_i ≤ u$, we get $q ∈ U_{y_i}$ for
all $i$, hence $r ∈ U_{\sup y}$.

For roundedness of $U_{\sup y}$, the forward direction refines a witness $p < q$
to the mediant $\operatorname{med}(p,q)$, and the backward direction composes
two existential witnesses using transitivity of $≤$ on $ℚ$.

```agda
  abstract
    is-inhabited-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      exists ℚ upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
    is-inhabited-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ( ℚ)
                ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ))
      in do
        (q , q∈Uu) ← is-inhabited-upper-cut-macneille-ℝ u
        (r , q<r) ← exists-greater-ℚ q
        intro-exists r (intro-exists q (q<r , (λ i → pr2 (y≤u i) q q∈Uu)))

  abstract
    forward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p)
    forward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      map-exists
        ( λ r →
          type-Prop
            ( le-ℚ-Prop r q ∧
              upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
                ( r)))
        ( λ p → mediant-ℚ p q)
        ( λ p (p<q , p∈all) →
          le-right-mediant-ℚ p<q ,
          intro-exists p (le-left-mediant-ℚ p<q , p∈all))

  abstract
    backward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q
    backward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      elim-exists
        ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q)
        ( λ p (p<q , p∈U) →
          elim-exists
            ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
              ( q))
            ( λ r (r<p , r∈all) →
              intro-exists r (transitive-le-ℚ r p q p<q r<p , r∈all))
            ( p∈U))

  abstract
    is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q ↔
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p)
    is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      ( forward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( q) ,
        backward-implication-is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( q))

  upper-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    upper-ℝ (l1 ⊔ l2)
  upper-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
    ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
      is-inhabited-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
      is-rounded-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

For the lower cut we take the open lower complement:

$$
  (p ∈ L_{\sup y}) ≔ (∃(q : ℚ),\; (p ≤ q) ∧ ¬ (q ∈ U_{\sup y})).
$$

```agda
  lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    subtype (l1 ⊔ l2) ℚ
  lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p =
    ∃ ( ℚ)
      ( λ q →
        le-ℚ-Prop p q ∧
        ¬' upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q)

  is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    ℚ → UU (l1 ⊔ l2)
  is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
    is-in-subtype
      ( lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

To see $L_{\sup y}$ is inhabited, pick $i : I$, choose $p ∈ L_{y_i}$, and then
choose $q > p$ with $q ∉ U_{y_i}$. If $q ∈ U_{\sup y}$, then in particular
$q ∈ U_{y_i}$, a contradiction.

```agda
  abstract
    is-inhabited-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      exists ℚ lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
    is-inhabited-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
      rec-trunc-Prop
        ( ∃ ℚ lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
        ( λ i →
          let
            open
              do-syntax-trunc-Prop
                ( ∃ ( ℚ)
                    ( lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ))
          in do
            (p , p∈Li) ← is-inhabited-lower-cut-macneille-ℝ (y i)
            (q , p<q , q∉Ui) ←
              forward-implication
                ( is-open-lower-complement-upper-cut-macneille-ℝ (y i) p)
                ( p∈Li)
            intro-exists
              ( p)
              ( intro-exists
                ( q)
                ( p<q ,
                  ( q∉Ui ∘
                    is-in-cut-upper-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
                      ( i)
                      ( q)))))
          ( H)
```

Roundedness of $L_{\sup y}$ follows from density of $ℚ$: from a witness $p < q$
with $q ∉ U*{\sup y}$, choose $r$ with $p < r < q$, and keep the same $q$.

```agda
  abstract
    forward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (p : ℚ) →
      is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p →
      exists ℚ
        ( λ r →
          le-ℚ-Prop p r ∧
          lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ r)
    forward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      p p∈L =
      let
        open
          do-syntax-trunc-Prop
            ( ∃ ℚ
              ( λ r →
                le-ℚ-Prop p r ∧
                lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
                  ( r)))
      in do
        (q , p<q , q∉U) ← p∈L
        (r , p<r , r<q) ← dense-le-ℚ p<q
        intro-exists r (p<r , intro-exists q (r<q , q∉U))

  abstract
    backward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (p : ℚ) →
      exists ℚ
        ( λ r →
          le-ℚ-Prop p r ∧
          lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ r) →
      is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p
    backward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      p =
      elim-exists
        ( lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p)
        ( λ r (p<r , r∈L) →
          elim-exists
            ( lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
              ( p))
            ( λ q (r<q , q∉U) →
              intro-exists q (transitive-le-ℚ p r q r<q p<r , q∉U))
            ( r∈L))

  abstract
    is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (p : ℚ) →
      is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p ↔
      exists ℚ
        ( λ r →
          le-ℚ-Prop p r ∧
          lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ r)
    is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      p =
      ( forward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( p) ,
        backward-implication-is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( p))

  lower-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
    lower-ℝ (l1 ⊔ l2)
  lower-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
    ( lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
      is-inhabited-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
      is-rounded-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

Next we verify that the two cuts are open complements, i.e.,

$$
 (q ∈ U_{\sup y}) ⇔ (∃(p ≤ q),\; p ∉ L_{\sup y})
$$

and

$$
  (p ∈ L_{\sup y}) ⇔ (∃(q ≥ p),\; q ∉ U_{\sup y}).
$$

This is exactly the openness condition needed for a MacNeille real.

```agda
  abstract
    forward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p)
    forward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      elim-exists
        ( ∃ ℚ
          ( λ p →
            le-ℚ-Prop p q ∧
            ¬' lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
                ( p)))
        ( λ p (p<q , p∈all) →
          intro-exists
            ( p)
            ( p<q ,
              elim-exists
                ( empty-Prop)
                ( λ r (p<r , r∉U) → r∉U (intro-exists p (p<r , p∈all)))))

  abstract
    backward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
              ( p)) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q
    backward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      elim-exists
        ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q)
        ( λ p (p<q , p∉L) →
          let
            open
              do-syntax-trunc-Prop
                ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
                  ( q))
          in do
            (r , p<r , r<q) ← dense-le-ℚ p<q
            (s , r<s , s<q) ← dense-le-ℚ r<q
            intro-exists
              ( s)
              ( s<q ,
                λ i →
                backward-implication
                  ( is-open-upper-complement-lower-cut-macneille-ℝ (y i) s)
                  ( intro-exists
                    ( r)
                    ( r<s ,
                      λ r∈Li →
                      p∉L
                        ( intro-exists
                          ( r)
                          ( p<r ,
                            elim-exists
                              ( empty-Prop)
                              ( λ t (t<r , t∈all) →
                                is-not-in-upper-cut-is-in-lower-cut-macneille-ℝ
                                  ( y i)
                                  ( t)
                                  ( is-in-cut-le-ℚ-lower-ℝ
                                    ( lower-real-macneille-ℝ (y i))
                                    ( t)
                                    ( r)
                                    ( t<r)
                                    ( r∈Li))
                                  ( t∈all i))))))))

  abstract
    is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (q : ℚ) →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q ↔
      exists ℚ
        ( λ p →
          le-ℚ-Prop p q ∧
          ¬' lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p)
    is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      q =
      ( forward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( q) ,
        backward-implication-is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( q))

  abstract
    is-open-lower-complement-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      (p : ℚ) →
      is-in-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ p ↔
      exists ℚ
        ( λ q →
          le-ℚ-Prop p q ∧
          ¬' upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q)
    is-open-lower-complement-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
      p =
      ( id , id)

  abstract
    is-open-dedekind-macneille-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      is-open-dedekind-macneille-lower-upper-ℝ
        ( lower-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
        ( upper-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
    is-open-dedekind-macneille-least-upper-bound-inhabited-bounded-family-macneille-ℝ =
      ( is-open-upper-complement-lower-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
        is-open-lower-complement-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

We now assemble the MacNeille real $\sup y$ from its lower and upper cuts.

```agda
  least-upper-bound-inhabited-bounded-family-macneille-ℝ : macneille-ℝ (l1 ⊔ l2)
  least-upper-bound-inhabited-bounded-family-macneille-ℝ =
    ( ( lower-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ ,
        upper-real-least-upper-bound-inhabited-bounded-family-macneille-ℝ) ,
      is-open-dedekind-macneille-least-upper-bound-inhabited-bounded-family-macneille-ℝ)
```

To prove the upper-bound property, we use:

$$
(q ∈ U_{\sup y}) \;\Longrightarrow\; (∀(i : I),\; q ∈ U_{y_i}),
$$

which immediately yields $y_i ≤ \sup y$ for each $i$.

```agda
  abstract
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      is-upper-bound-family-of-elements-macneille-ℝ
        ( y)
        ( least-upper-bound-inhabited-bounded-family-macneille-ℝ)
    is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ i =
      leq-macneille-leq-upper-real-macneille-ℝ
        ( y i)
        ( least-upper-bound-inhabited-bounded-family-macneille-ℝ)
        ( is-in-cut-upper-family-is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( i))
```

To prove it is a _least_ upper-bound, let $z$ be any upper bound of the family.
The key step is:

$$
  (q ∈ U_z) \;\Longrightarrow\; (q ∈ U_{\sup y}).
$$

Equivalently, $U_z ⊆ U_{\sup y}$, so $\sup y ≤ z$.

```agda
  abstract
    is-in-cut-upper-least-upper-bound-family-is-in-upper-cut-macneille-ℝ :
      {l4 : Level} (z : macneille-ℝ l4) →
      is-upper-bound-family-of-elements-macneille-ℝ y z →
      (q : ℚ) →
      is-in-upper-cut-macneille-ℝ z q →
      is-in-upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ q
    is-in-cut-upper-least-upper-bound-family-is-in-upper-cut-macneille-ℝ
      z y≤z q q∈Uz =
      let
        open
          do-syntax-trunc-Prop
            ( upper-cut-least-upper-bound-inhabited-bounded-family-macneille-ℝ
              ( q))
      in do
        (p , p<q , p∉Lz) ←
          forward-implication
            ( is-open-upper-complement-lower-cut-macneille-ℝ z q)
            ( q∈Uz)
        (r , p<r , r<q) ← dense-le-ℚ p<q
        intro-exists
          ( r)
          ( r<q ,
            λ i →
            backward-implication
              ( is-open-upper-complement-lower-cut-macneille-ℝ (y i) r)
              ( intro-exists p (p<r , p∉Lz ∘ pr1 (y≤z i) p)))

  abstract
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ :
      {l4 : Level} (z : macneille-ℝ l4) →
      is-upper-bound-family-of-elements-macneille-ℝ y z →
      leq-macneille-ℝ least-upper-bound-inhabited-bounded-family-macneille-ℝ z
    leq-least-upper-bound-family-upper-bound-family-macneille-ℝ z y≤z =
      leq-macneille-leq-upper-real-macneille-ℝ
        ( least-upper-bound-inhabited-bounded-family-macneille-ℝ)
        ( z)
        ( is-in-cut-upper-least-upper-bound-family-is-in-upper-cut-macneille-ℝ
          ( z)
          ( y≤z))
```

The final theorem packages both directions:

$$
\left(∀ z,\; \bigl(∀ i,\; y_i ≤ z\bigr) ⇒ \sup y ≤ z\right)
\quad\text{and}\quad \left(∀ i,\; y_i ≤ \sup y\right).
$$

So the constructed real is a least upper bound of the inhabited bounded family.

```agda
  abstract
    is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ :
      is-least-upper-bound-family-of-elements-macneille-ℝ
        ( y)
        ( least-upper-bound-inhabited-bounded-family-macneille-ℝ)
    pr1
      ( is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( z)) =
      leq-least-upper-bound-family-upper-bound-family-macneille-ℝ z
    pr2
      ( is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
        ( z))
      x≤z i =
      transitive-leq-macneille-ℝ
        ( y i)
        ( least-upper-bound-inhabited-bounded-family-macneille-ℝ)
        ( z)
        ( x≤z)
        ( is-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
          ( i))

  has-least-upper-bound-inhabited-upper-bounded-family-of-elements-macneille-ℝ :
    has-least-upper-bound-family-of-elements-macneille-ℝ lzero y
  has-least-upper-bound-inhabited-upper-bounded-family-of-elements-macneille-ℝ =
    λ where
    .sup-has-least-upper-bound-family-of-elements-Large-Poset →
      least-upper-bound-inhabited-bounded-family-macneille-ℝ
    .is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset →
      is-least-upper-bound-least-upper-bound-inhabited-bounded-family-macneille-ℝ
```

## References

{{#bibliography}}
