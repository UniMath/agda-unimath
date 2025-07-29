# Quasigroups

```agda
module group-theory.quasigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-equivalences
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.function-types

open import group-theory.left-quasigroups
open import group-theory.right-quasigroups

open import structured-types.magmas
```

</details>

## Idea

{{#concept "Quasigroups" Agda=Quasigroup}} are both
[left](group-theory.left-quasigroups.md) and
[right](group-theory.right-quasigroups.md) quasigroups with a compatible
multiplication. In
[`algebraic-theory-of-quasigroups`](universal-algebra.algebraic-theory-of-quasigroups.md)
we show that quasigroups form an
[algebraic variety](universal-algebra.algebraic-variaties.md), while in
[`wild-quasigroups`](structured-types.wild-quasigroups.md) we show that they are
precisely the wild quasigroups whose underlying type is a set.

These give two distinct but interchangeably useful definitions of quasigroups:
the universal-algebraic definition implies nice results such as the HSP theorem
(to be formalized), while the binary-equivalence definition can be nicer to work
with in practice as it carries only one binary operation rather than three.

## Definitions

```agda
Quasigroup : (l : Level) → UU (lsuc l)
Quasigroup l =
  Σ (Set l) λ Q → Σ (type-Set Q → type-Set Q → type-Set Q)
  ( λ mul → Σ (type-Set Q → type-Set Q → type-Set Q)
  ( λ left-div → Σ (type-Set Q → type-Set Q → type-Set Q)
  ( λ right-div →
  is-left-Quasigroup Q mul left-div × is-right-Quasigroup Q mul right-div)))

module _
  {l : Level} (Q : Quasigroup l)
  where

  set-Quasigroup : Set l
  set-Quasigroup = pr1 Q

  type-Quasigroup : UU l
  type-Quasigroup = type-Set set-Quasigroup

  is-set-Quasigroup : is-set type-Quasigroup
  is-set-Quasigroup = is-set-type-Set set-Quasigroup

  mul-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  mul-Quasigroup = pr1 (pr2 Q)

  left-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  left-div-Quasigroup = pr1 (pr2 (pr2 Q))

  right-div-Quasigroup : type-Quasigroup → type-Quasigroup → type-Quasigroup
  right-div-Quasigroup = pr1 (pr2 (pr2 (pr2 Q)))

  is-left-cancellative-left-div-Quasigroup :
    is-left-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-left-cancellative-left-div-Quasigroup = pr1 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-left-div-Quasigroup :
    is-right-cancellative-left-div set-Quasigroup
    mul-Quasigroup left-div-Quasigroup
  is-right-cancellative-left-div-Quasigroup =
    pr2 (pr1 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-left-cancellative-right-div-Quasigroup :
    is-left-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-left-cancellative-right-div-Quasigroup =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))

  is-right-cancellative-right-div-Quasigroup :
    is-right-cancellative-right-div set-Quasigroup
    mul-Quasigroup right-div-Quasigroup
  is-right-cancellative-right-div-Quasigroup =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 Q)))))
```

## Properties

### Multiplication in a quasigroup is a [binary equivalence](foundation.binary-equivalences.md)

```agda
module _
  {l : Level} (Q : Quasigroup l)
  where

  is-binary-equiv-mul-Quasigroup : is-binary-equiv (mul-Quasigroup Q)
  pr1 (pr1 (pr1 is-binary-equiv-mul-Quasigroup x)) y =
    right-div-Quasigroup Q y x
  pr2 (pr1 (pr1 is-binary-equiv-mul-Quasigroup x)) y =
    inv (is-left-cancellative-right-div-Quasigroup Q x y)
  pr1 (pr2 (pr1 is-binary-equiv-mul-Quasigroup x)) y =
    right-div-Quasigroup Q y x
  pr2 (pr2 (pr1 is-binary-equiv-mul-Quasigroup x)) y =
    inv (is-right-cancellative-right-div-Quasigroup Q x y)
  pr1 (pr1 (pr2 is-binary-equiv-mul-Quasigroup x)) y = left-div-Quasigroup Q x y
  pr2 (pr1 (pr2 is-binary-equiv-mul-Quasigroup x)) y =
    inv (is-left-cancellative-left-div-Quasigroup Q x y)
  pr1 (pr2 (pr2 is-binary-equiv-mul-Quasigroup x)) y = left-div-Quasigroup Q x y
  pr2 (pr2 (pr2 is-binary-equiv-mul-Quasigroup x)) y =
    inv (is-right-cancellative-left-div-Quasigroup Q x y)
```
