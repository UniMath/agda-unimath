# The large poset of closed intervals of real numbers

```agda
module real-numbers.large-poset-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.large-poset-closed-intervals-large-posets
open import order-theory.large-posets

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
```

</details>

## Idea

The type of [closed intervals](real-numbers.closed-intervals-real-numbers.md) in
the [real numbers](real-numbers.dedekind-real-numbers.md) forms a
[large poset](order-theory.large-posets.md) under the containment relation,
where `[a, b]` is contained in `[c, d]` if `c ≤ a` and `b ≤ d`.

## Definition

```agda
leq-prop-closed-interval-ℝ :
  {l1 l2 l3 l4 : Level} →
  closed-interval-ℝ l1 l2 → closed-interval-ℝ l3 l4 → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
leq-prop-closed-interval-ℝ =
  leq-prop-closed-interval-Large-Poset ℝ-Large-Poset

leq-closed-interval-ℝ :
  {l1 l2 l3 l4 : Level} →
  closed-interval-ℝ l1 l2 → closed-interval-ℝ l3 l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
leq-closed-interval-ℝ = leq-closed-interval-Large-Poset ℝ-Large-Poset
```

## Properties

### Containment of intervals forms a poset

```agda
refl-leq-closed-interval-ℝ :
  {l1 l2 : Level} ([a,b] : closed-interval-ℝ l1 l2) →
  leq-closed-interval-ℝ [a,b] [a,b]
refl-leq-closed-interval-ℝ =
  refl-leq-closed-interval-Large-Poset ℝ-Large-Poset

transitive-leq-closed-interval-ℝ :
  {l1 l2 l3 l4 l5 l6 : Level}
  ([a,b] : closed-interval-ℝ l1 l2)
  ([c,d] : closed-interval-ℝ l3 l4)
  ([e,f] : closed-interval-ℝ l5 l6) →
  leq-closed-interval-ℝ [c,d] [e,f] →
  leq-closed-interval-ℝ [a,b] [c,d] →
  leq-closed-interval-ℝ [a,b] [e,f]
transitive-leq-closed-interval-ℝ =
  transitive-leq-closed-interval-Large-Poset ℝ-Large-Poset

antisymmetric-leq-closed-interval-ℝ :
  {l1 l2 : Level} ([a,b] [c,d] : closed-interval-ℝ l1 l2) →
  leq-closed-interval-ℝ [a,b] [c,d] →
  leq-closed-interval-ℝ [c,d] [a,b] →
  [a,b] ＝ [c,d]
antisymmetric-leq-closed-interval-ℝ =
  antisymmetric-leq-closed-interval-Large-Poset ℝ-Large-Poset

large-poset-closed-interval-ℝ : Large-Poset lsuc (_⊔_)
large-poset-closed-interval-ℝ =
  large-poset-closed-interval-Large-Poset ℝ-Large-Poset
```

### If `[a, b]` is contained in `[c, d]`, then their subtypes are contained

```agda
abstract
  leq-subtype-leq-closed-interval-ℝ :
    {l1 l2 l3 l4 l5 : Level}
    ([a,b] : closed-interval-ℝ l1 l2)
    ([c,d] : closed-interval-ℝ l3 l4) →
    leq-closed-interval-ℝ [a,b] [c,d] →
    subtype-closed-interval-ℝ l5 [a,b] ⊆ subtype-closed-interval-ℝ l5 [c,d]
  leq-subtype-leq-closed-interval-ℝ =
    leq-subtype-leq-closed-interval-Large-Poset ℝ-Large-Poset
```

### If the subtype associated with `[a, b]` is contained in the subtype associated with `[c, d]`, then `[a, b]` is contained in `[c, d]`

```agda
abstract
  leq-leq-subtype-closed-interval-ℝ :
    {l1 l2 l3 l4 : Level}
    ([a,b] : closed-interval-ℝ l1 l2)
    ([c,d] : closed-interval-ℝ l3 l4) →
    ( subtype-closed-interval-ℝ (l1 ⊔ l2) [a,b] ⊆
      subtype-closed-interval-ℝ (l1 ⊔ l2) [c,d]) →
    leq-closed-interval-ℝ [a,b] [c,d]
  leq-leq-subtype-closed-interval-ℝ
    {l1} {l2} ((a , b) , a≤b) ((c , d) , c≤d) S[a,b]⊆S[c,d] =
    ( reflects-leq-right-raise-ℝ
        ( l2)
        ( pr1
          ( S[a,b]⊆S[c,d]
            ( raise-ℝ l2 a)
            ( leq-sim-ℝ (sim-raise-ℝ l2 a) ,
              preserves-leq-left-raise-ℝ l2 a≤b))) ,
      reflects-leq-left-raise-ℝ
        ( l1)
        ( pr2
          ( S[a,b]⊆S[c,d]
            ( raise-ℝ l1 b)
            ( preserves-leq-right-raise-ℝ l1 a≤b ,
              leq-sim-ℝ' (sim-raise-ℝ l1 b)))))
```

### If `[a, b]` is contained in `[c, d]`, the width of `[a, b]` is less than or equal to the width of `[c, d]`

```agda
abstract
  leq-width-leq-closed-interval-ℝ :
    {l1 l2 l3 l4 : Level}
    ([a,b] : closed-interval-ℝ l1 l2)
    ([c,d] : closed-interval-ℝ l3 l4) →
    leq-closed-interval-ℝ [a,b] [c,d] →
    leq-ℝ (width-closed-interval-ℝ [a,b]) (width-closed-interval-ℝ [c,d])
  leq-width-leq-closed-interval-ℝ ((a , b) , _) ((c , d) , _) (a≤c , b≤d) =
    preserves-leq-add-ℝ b≤d (neg-leq-ℝ a≤c)
```
