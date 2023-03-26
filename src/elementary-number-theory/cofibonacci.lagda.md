# The cofibonacci sequence

```agda
module elementary-number-theory.cofibonacci where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The **cofibonacci sequence** [1] is the unique function G : ℕ → ℕ satisfying the
property that

```md
  div-ℕ (G m) n ↔ div-ℕ m (Fibonacci-ℕ n).
```

[1] https://oeis.org/A001177 [2] https://oeis.org/A001175

{- div-Fibonacci-left-summand-ℕ : (d m n : ℕ) → div-ℕ d (Fibonacci-ℕ n) → div-ℕ
d (Fibonacci-ℕ (add-ℕ m n)) → div-ℕ d (Fibonacci-ℕ m)
div-Fibonacci-left-summand-ℕ d m n H1 H2 = {!!} -}

--

---

-- The Pisano sequence

---

-- The cofibonacci sequence

is-multiple-of-cofibonacci : (m x : ℕ) → UU lzero is-multiple-of-cofibonacci m x
= is-nonzero-ℕ m → is-nonzero-ℕ x × div-ℕ m (Fibonacci-ℕ x)

is-decidable-is-multiple-of-cofibonacci : (m x : ℕ) → is-decidable
(is-multiple-of-cofibonacci m x) is-decidable-is-multiple-of-cofibonacci m x =
is-decidable-function-type ( is-decidable-is-nonzero-ℕ m) ( is-decidable-prod (
is-decidable-is-nonzero-ℕ x) ( is-decidable-div-ℕ m (Fibonacci-ℕ x)))

cofibonacci-multiple : (m : ℕ) → Σ ℕ (is-multiple-of-cofibonacci m)
cofibonacci-multiple zero-ℕ = pair zero-ℕ (λ f → (ex-falso (f refl)))
cofibonacci-multiple (succ-ℕ m) = pair ( pisano-period m) ( λ f → pair
(is-nonzero-pisano-period m) (div-fibonacci-pisano-period m))

least-multiple-of-cofibonacci : (m : ℕ) → minimal-element-ℕ
(is-multiple-of-cofibonacci m) least-multiple-of-cofibonacci m =
well-ordering-principle-ℕ ( is-multiple-of-cofibonacci m) (
is-decidable-is-multiple-of-cofibonacci m) ( cofibonacci-multiple m)

cofibonacci : ℕ → ℕ cofibonacci m = pr1 (least-multiple-of-cofibonacci m)

is-multiple-of-cofibonacci-cofibonacci : (m : ℕ) → is-multiple-of-cofibonacci m
(cofibonacci m) is-multiple-of-cofibonacci-cofibonacci m = pr1 (pr2
(least-multiple-of-cofibonacci m))

is-lower-bound-cofibonacci : (m x : ℕ) → is-multiple-of-cofibonacci m x →
cofibonacci m ≤-ℕ x is-lower-bound-cofibonacci m = pr2 (pr2
(least-multiple-of-cofibonacci m))

is-zero-cofibonacci-zero-ℕ : is-zero-ℕ (cofibonacci zero-ℕ)
is-zero-cofibonacci-zero-ℕ = is-zero-leq-zero-ℕ ( cofibonacci zero-ℕ) (
is-lower-bound-cofibonacci zero-ℕ zero-ℕ ( λ f → ex-falso (f refl)))

forward-is-left-adjoint-cofibonacci : (m n : ℕ) → div-ℕ (cofibonacci m) n →
div-ℕ m (Fibonacci-ℕ n) forward-is-left-adjoint-cofibonacci zero-ℕ n H = tr (
div-ℕ zero-ℕ) ( ap ( Fibonacci-ℕ) ( inv ( is-zero-div-zero-ℕ n ( tr (λ t → div-ℕ
t n) is-zero-cofibonacci-zero-ℕ H)))) ( refl-div-ℕ zero-ℕ)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) zero-ℕ H = div-zero-ℕ (succ-ℕ m)
forward-is-left-adjoint-cofibonacci (succ-ℕ m) (succ-ℕ n) H =
div-Fibonacci-div-ℕ ( succ-ℕ m) ( cofibonacci (succ-ℕ m)) ( succ-ℕ n) ( H) ( pr2
( is-multiple-of-cofibonacci-cofibonacci ( succ-ℕ m) ( is-nonzero-succ-ℕ m)))

{- converse-is-left-adjoint-cofibonacci : (m n : ℕ) → div-ℕ m (Fibonacci-ℕ n) →
div-ℕ (cofibonacci m) n converse-is-left-adjoint-cofibonacci m n H = {!!}

is-left-adjoint-cofibonacci : (m n : ℕ) → div-ℕ (cofibonacci m) n ↔ div-ℕ m
(Fibonacci-ℕ n) is-left-adjoint-cofibonacci zero-ℕ n = {!!}
is-left-adjoint-cofibonacci (succ-ℕ m) n = {!!} -}
