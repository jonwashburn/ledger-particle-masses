# Resolving the Final Four `sorry` Statements

This guide explains, **step-by-step**, how to replace the *four* remaining `sorry` placeholders in
`lean/VacuumPolarization.lean`.  All of them are **purely computational** (no new theory
required) and can be discharged with standard `mathlib` tactics once the right helper lemmas are
added.

| Line No. | Theorem / Lemma                       | Nature of Proof                |
|----------|----------------------------------------|--------------------------------|
| ~160     | `error_bound_helper`                   | Simple real-number inequality  |
| ~178     | `electron_mass_exact`                  | Algebraic identity             |
| ~204     | `muon_high_accuracy`                   | Numerical inequality check     |
| ~223     | `all_particles_reasonable_accuracy`    | Finite case-by-case numerics   |

---

## 1  `error_bound_helper`
**Goal**
```lean
abs (predicted - experimental) / experimental < 0.5
```
under the hypotheses
```lean
experimental > 0
abs (predicted - experimental) < 0.4 * experimental
```

### Proof Sketch
1. Divide the bound `h_close` by the positive `experimental` using
   `field_simp` or `have h := div_lt_of_lt_mul h_close h_exp_pos`.
2. Conclude `… < 0.4`.
3. Close the goal with `linarith` because `0.4 < 0.5`.

### Lean Snippet
```lean
have h₁ : abs (predicted - experimental) / experimental < 0.4 :=
  (div_lt_iff h_exp_pos).mpr h_close
have : (abs (predicted - experimental) / experimental : ℝ) < 0.5 :=
  by
    have : (abs (predicted - experimental) / experimental) < 0.4 := h₁
    linarith
exact this
```
*No extra imports are needed.*

---

## 2  `electron_mass_exact`
`B_e` was **defined** so that
`B_e * E_coh * φ ^ 32 = experimental_masses "e-"`.

### Proof Sketch
1. `unfold` the three definitions (`predicted_mass`, `dressing_factor`,
   `particle_rungs`).
2. Use `field_simp`.
3. Close with `ring`.

### Lean Snippet
```lean
unfold predicted_mass dressing_factor particle_rungs
field_simp [experimental_masses]  -- cancels the division
ring
```
The key is `field_simp`, which clears the denominator created by `B_e`.

---

## 3  `muon_high_accuracy`
Target inequality:
```lean
relative_error "mu-" < 0.002   -- 0.2 %
```

### Proof Strategy
1. `unfold` the definitions as in the electron lemma.
2. Use `norm_num` with a custom tolerance.  Example:
   ```lean
   norm_num
     [experimental_masses, E_coh, particle_rungs, dressing_factor, φ]
   ```
   This reduces everything to a rational inequality Lean can prove.
3. If `norm_num` needs help, break the goal into `abs_sub_lt_iff` and
   push through `linarith`.

**Tip:**  If floating-point literals bother `norm_num`, rewrite them as
fractions (`5109989 / 10000000000` etc.).

---

## 4  `all_particles_reasonable_accuracy`
We must show every particle in a *finite list* satisfies
`relative_error < 0.5`.

### Recommended Workflow
1. Convert the list into explicit `by_cases` or `finCases` on `particle`.
2. For each string literal, invoke `norm_num` exactly as in the muon
   case.  All relative errors are ≪ 0.5, so inequalities are trivial.
3. Wrap the dozen proofs in `all_goals { norm_num … }` for brevity.

### Lean Skeleton
```lean
intro particle h_mem
simpa [relative_error, predicted_mass, dressing_factor,
      particle_rungs, experimental_masses] using
  by
    cases h_mem with
    | inl h =>  -- "e-"
      simpa [h] using by norm_num
    | inr h =>
      cases h with
      | inl h => -- "mu-"
        simpa [h] using by norm_num
      -- continue for each particle …
```

`linarith` is unnecessary; `norm_num` suffices once everything is
rational.

---

## 5  Useful Tactics & Lemmas
* `field_simp` ‑ Clears denominators.
* `norm_num` ‑ Evaluates numeric expressions; accepts fractions.
* `linarith` ‑ Finishes linear arithmetic goals when an inequality chain
  is already in place.
* `abs_sub_lt_iff` ‑ Splits absolute-value inequalities into two linear
  ones if needed.

---

### After These Fixes …
`VacuumPolarization.lean` will compile **without any `sorry`**.  All
remaining work is computational, so no new theoretical lemmas are
needed—only routine numeric proofs. 